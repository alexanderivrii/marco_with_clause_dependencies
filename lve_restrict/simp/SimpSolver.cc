/***********************************************************************************[SimpSolver.cc]
Copyright (c) 2006,      Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "mtl/Sort.h"
#include "simp/SimpSolver.h"
#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "core/SolverTypes.h"
#include "core/Dimacs.h"

#include "reduce_bins/reduceBins.h"

// Even though MiniSat offers its own vector classes, it's much easier for me to work with the STL ones
#include <vector>
#include <algorithm>
using std::vector;

using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "SIMP";

static BoolOption   opt_use_asymm        (_cat, "asymm",            "Shrink clauses by asymmetric branching.", false);
static BoolOption   opt_use_rcheck       (_cat, "rcheck",           "Check if a clause is already implied. (costly)", false);
static BoolOption   opt_use_elim         (_cat, "elim",             "Perform variable elimination.", true);
static IntOption    opt_grow             (_cat, "grow",             "Allow a variable elimination step to grow by a number of clauses.", 0);
static IntOption    opt_clause_lim       (_cat, "cl-lim",           "Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit", 20,   IntRange(-1, INT32_MAX));
static IntOption    opt_subsumption_lim  (_cat, "sub-lim",          "Do not check if subsumption against a clause larger than this. -1 means no limit.", 1000, IntRange(-1, INT32_MAX));
static DoubleOption opt_simp_garbage_frac(_cat, "simp-gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered during simplification.",  0.5, DoubleRange(0, false, HUGE_VAL, false));
static DoubleOption opt_simp_time_limit  (_cat, "time",             "Stop after this time. -1 means no limit.",  3600, DoubleRange(-1, true, HUGE_VAL, false));
static IntOption    opt_restrict_cap     (_cat, "max",              "Cap number of restrictions.  -1 means no limit.", 1000000, IntRange(-1, INT32_MAX));
static BoolOption   opt_restrict_reduce  (_cat, "reduce",           "Reduce restrictions found.", true);
static IntOption    opt_handle_removable (_cat, "redundant",        "Handling redundant groups (0 - nothing, 1 - remove, 2 -relabel as group 0).", 0, IntRange(0, 2));
static BoolOption   opt_lve_only         (_cat, "lve-only",         "Do not analyze restrictions.", false);
static BoolOption   opt_eq_only          (_cat, "eq-only",          "Only return restrictions corresponding to equivalences.", false);


//=================================================================================================
// Constructor/Destructor:


SimpSolver::SimpSolver() :
    simp_time_limit    (opt_simp_time_limit)
  , restrict_cap       (opt_restrict_cap)
  , restrict_reduce    (opt_restrict_reduce)
  , handle_removable   (opt_handle_removable)
  , lve_only           (opt_lve_only)
  , eq_only            (opt_eq_only)
  , grow               (opt_grow)
  , clause_lim         (opt_clause_lim)
  , subsumption_lim    (opt_subsumption_lim)
  , simp_garbage_frac  (opt_simp_garbage_frac)
  , use_asymm          (opt_use_asymm)
  , use_rcheck         (opt_use_rcheck)
  , use_elim           (opt_use_elim)
  , merges             (0)
  , asymm_lits         (0)
  , eliminated_vars    (0)
  , elimorder          (1)
  , use_simplification (true)
  , occurs             (ClauseDeleted(ca))
  , elim_heap          (ElimLt(n_occ))
  , bwdsub_assigns     (0)
  , n_touched          (0)
{
    vec<Lit> dummy(1,lit_Undef);
    ca.extra_clause_field = true; // NOTE: must happen before allocating the dummy clause below.
    bwdsub_tmpunit        = ca.alloc(dummy);
    remove_satisfied      = false;
}


SimpSolver::~SimpSolver()
{
}


Var SimpSolver::newVar(bool sign, bool dvar) {
    Var v = Solver::newVar(sign, dvar);

    frozen    .push((char)false);
    eliminated.push((char)false);

    if (use_simplification){
        n_occ     .push(0);
        n_occ     .push(0);
        occurs    .init(v);
        touched   .push(0);
        elim_heap .insert(v);
    }
    return v; }



lbool SimpSolver::solve_(bool do_simp, bool turn_off_simp)
{
    vec<Var> extra_frozen;
    lbool    result = l_True;

    do_simp &= use_simplification;

    if (do_simp){
        // Assumptions must be temporarily frozen to run variable elimination:
        for (int i = 0; i < assumptions.size(); i++){
            Var v = var(assumptions[i]);

            // If an assumption has been eliminated, remember it.
            assert(!isEliminated(v));

            if (!frozen[v]){
                // Freeze and store.
                setFrozen(v, true);
                extra_frozen.push(v);
            } }

        result = lbool(eliminate(turn_off_simp));
    }

    if (result == l_True)
        result = Solver::solve_();
    else if (verbosity >= 1)
        printf("===============================================================================\n");

    if (result == l_True)
        extendModel();

    if (do_simp)
        // Unfreeze the assumptions that were frozen:
        for (int i = 0; i < extra_frozen.size(); i++)
            setFrozen(extra_frozen[i], false);

    return result;
}



bool SimpSolver::addClause_(vec<Lit>& ps)
{
#ifndef NDEBUG
    for (int i = 0; i < ps.size(); i++)
        assert(!isEliminated(var(ps[i])));
#endif

    int nclauses = clauses.size();

    if (use_rcheck && implied(ps))
        return true;

    if (!Solver::addClause_(ps))
        return false;

    if (use_simplification && clauses.size() == nclauses + 1){
        CRef          cr = clauses.last();
        const Clause& c  = ca[cr];

        // NOTE: the clause is added to the queue immediately and then
        // again during 'gatherTouchedClauses()'. If nothing happens
        // in between, it will only be checked once. Otherwise, it may
        // be checked twice unnecessarily. This is an unfortunate
        // consequence of how backward subsumption is used to mimic
        // forward subsumption.
        subsumption_queue.insert(cr);
        for (int i = 0; i < c.size(); i++){
            occurs[var(c[i])].push(cr);
            n_occ[toInt(c[i])]++;
            touched[var(c[i])] = 1;
            n_touched++;
            if (elim_heap.inHeap(var(c[i])))
                elim_heap.increase(var(c[i]));
        }
    }

    return true;
}


void SimpSolver::removeClause(CRef cr)
{
    const Clause& c = ca[cr];

    if (use_simplification)
        for (int i = 0; i < c.size(); i++){
            n_occ[toInt(c[i])]--;
            updateElimHeap(var(c[i]));
            occurs.smudge(var(c[i]));
        }

    Solver::removeClause(cr);
}


bool SimpSolver::strengthenClause(CRef cr, Lit l)
{
    Clause& c = ca[cr];
    assert(decisionLevel() == 0);
    assert(use_simplification);

    // FIX: this is too inefficient but would be nice to have (properly implemented)
    // if (!find(subsumption_queue, &c))
    subsumption_queue.insert(cr);

    if (c.size() == 2){
        removeClause(cr);
        c.strengthen(l);
    }else{
        detachClause(cr, true);
        c.strengthen(l);
        attachClause(cr);
        remove(occurs[var(l)], cr);
        n_occ[toInt(l)]--;
        updateElimHeap(var(l));
    }

    return c.size() == 1 ? enqueue(c[0]) && propagate() == CRef_Undef : true;
}


// Returns FALSE if clause is always satisfied ('out_clause' should not be used).
bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause)
{
    merges++;
    out_clause.clear();

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps  =  ps_smallest ? _qs : _ps;
    const Clause& qs  =  ps_smallest ? _ps : _qs;

    for (int i = 0; i < qs.size(); i++){
        if (var(qs[i]) != v){
            for (int j = 0; j < ps.size(); j++)
                if (var(ps[j]) == var(qs[i]))
                    if (ps[j] == ~qs[i])
                        return false;
                    else
                        goto next;
            out_clause.push(qs[i]);
        }
        next:;
    }

    for (int i = 0; i < ps.size(); i++)
        if (var(ps[i]) != v)
            out_clause.push(ps[i]);

    return true;
}


// Returns FALSE if clause is always satisfied.
bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v, int& size)
{
    merges++;

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps  =  ps_smallest ? _qs : _ps;
    const Clause& qs  =  ps_smallest ? _ps : _qs;
    const Lit*  __ps  = (const Lit*)ps;
    const Lit*  __qs  = (const Lit*)qs;

    size = ps.size()-1;

    for (int i = 0; i < qs.size(); i++){
        if (var(__qs[i]) != v){
            for (int j = 0; j < ps.size(); j++)
                if (var(__ps[j]) == var(__qs[i]))
                    if (__ps[j] == ~__qs[i])
                        return false;
                    else
                        goto next;
            size++;
        }
        next:;
    }

    return true;
}


void SimpSolver::gatherTouchedClauses()
{
    if (n_touched == 0) return;

    int i,j;
    for (i = j = 0; i < subsumption_queue.size(); i++)
        if (ca[subsumption_queue[i]].mark() == 0)
            ca[subsumption_queue[i]].mark(2);

    for (i = 0; i < touched.size(); i++)
        if (touched[i]){
            const vec<CRef>& cs = occurs.lookup(i);
            for (j = 0; j < cs.size(); j++)
                if (ca[cs[j]].mark() == 0){
                    subsumption_queue.insert(cs[j]);
                    ca[cs[j]].mark(2);
                }
            touched[i] = 0;
        }

    for (i = 0; i < subsumption_queue.size(); i++)
        if (ca[subsumption_queue[i]].mark() == 2)
            ca[subsumption_queue[i]].mark(0);

    n_touched = 0;
}


bool SimpSolver::implied(const vec<Lit>& c)
{
    assert(decisionLevel() == 0);

    trail_lim.push(trail.size());
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True){
            cancelUntil(0);
            return false;
        }else if (value(c[i]) != l_False){
            assert(value(c[i]) == l_Undef);
            uncheckedEnqueue(~c[i]);
        }

    bool result = propagate() != CRef_Undef;
    cancelUntil(0);
    return result;
}


// Backward subsumption + backward subsumption resolution
bool SimpSolver::backwardSubsumptionCheck(bool verbose)
{
    int cnt = 0;
    int subsumed = 0;
    int deleted_literals = 0;
    assert(decisionLevel() == 0);

    while (subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()){

        // Empty subsumption queue and return immediately on user-interrupt:
        if (asynch_interrupt){
            subsumption_queue.clear();
            bwdsub_assigns = trail.size();
            break; }

        // Check top-level assignments by creating a dummy clause and placing it in the queue:
        if (subsumption_queue.size() == 0 && bwdsub_assigns < trail.size()){
            Lit l = trail[bwdsub_assigns++];
            ca[bwdsub_tmpunit][0] = l;
            ca[bwdsub_tmpunit].calcAbstraction();
            subsumption_queue.insert(bwdsub_tmpunit); }

        CRef    cr = subsumption_queue.peek(); subsumption_queue.pop();
        Clause& c  = ca[cr];

        if (c.mark()) continue;

        if (verbose && verbosity >= 2 && cnt++ % 1000 == 0)
            printf("subsumption left: %10d (%10d subsumed, %10d deleted literals)\r", subsumption_queue.size(), subsumed, deleted_literals);

        assert(c.size() > 1 || value(c[0]) == l_True);    // Unit-clauses should have been propagated before this point.

        // Find best variable to scan:
        Var best = var(c[0]);
        for (int i = 1; i < c.size(); i++)
            if (occurs[var(c[i])].size() < occurs[best].size())
                best = var(c[i]);

        // Search all candidates:
        vec<CRef>& _cs = occurs.lookup(best);
        CRef*       cs = (CRef*)_cs;

        for (int j = 0; j < _cs.size(); j++)
            if (c.mark())
                break;
            else if (!ca[cs[j]].mark() &&  cs[j] != cr && (subsumption_lim == -1 || ca[cs[j]].size() < subsumption_lim)){
                Lit l = c.subsumes(ca[cs[j]]);

                if (l == lit_Undef)
                    subsumed++, removeClause(cs[j]);
                else if (l != lit_Error){
                    deleted_literals++;

                    if (!strengthenClause(cs[j], ~l))
                        return false;

                    // Did current candidate get deleted from cs? Then check candidate at index j again:
                    if (var(l) == best)
                        j--;
                }
            }
    }

    return true;
}


bool SimpSolver::asymm(Var v, CRef cr)
{
    Clause& c = ca[cr];
    assert(decisionLevel() == 0);

    if (c.mark() || satisfied(c)) return true;

    trail_lim.push(trail.size());
    Lit l = lit_Undef;
    for (int i = 0; i < c.size(); i++)
        if (var(c[i]) != v && value(c[i]) != l_False)
            uncheckedEnqueue(~c[i]);
        else
            l = c[i];

    if (propagate() != CRef_Undef){
        cancelUntil(0);
        asymm_lits++;
        if (!strengthenClause(cr, l))
            return false;
    }else
        cancelUntil(0);

    return true;
}


bool SimpSolver::asymmVar(Var v)
{
    assert(use_simplification);

    const vec<CRef>& cls = occurs.lookup(v);

    if (value(v) != l_Undef || cls.size() == 0)
        return true;

    for (int i = 0; i < cls.size(); i++)
        if (!asymm(v, cls[i]))
            return false;

    return backwardSubsumptionCheck();
}


static void mkElimClause(vec<uint32_t>& elimclauses, Lit x)
{
    elimclauses.push(toInt(x));
    elimclauses.push(1);
}


static void mkElimClause(vec<uint32_t>& elimclauses, Var v, Clause& c)
{
    int first = elimclauses.size();
    int v_pos = -1;

    // Copy clause to elimclauses-vector. Remember position where the
    // variable 'v' occurs:
    for (int i = 0; i < c.size(); i++){
        elimclauses.push(toInt(c[i]));
        if (var(c[i]) == v)
            v_pos = i + first;
    }
    assert(v_pos != -1);

    // Swap the first literal with the 'v' literal, so that the literal
    // containing 'v' will occur first in the clause:
    uint32_t tmp = elimclauses[v_pos];
    elimclauses[v_pos] = elimclauses[first];
    elimclauses[first] = tmp;

    // Store the length of the clause last:
    elimclauses.push(c.size());
}



bool SimpSolver::eliminateVar(Var v)
{
    assert(!frozen[v]);
    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    // Split the occurrences into positive and negative:
    //
    const vec<CRef>& cls = occurs.lookup(v);
    vec<CRef>        pos, neg;
    for (int i = 0; i < cls.size(); i++)
        (find(ca[cls[i]], mkLit(v)) ? pos : neg).push(cls[i]);

    // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover, no
    // clause must exceed the limit on the maximal clause size (if it is set):
    //
    int cnt         = 0;
    int clause_size = 0;

    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, clause_size) &&
                (++cnt > cls.size() + grow || (clause_lim != -1 && clause_size > clause_lim)))
                return true;

    // Delete and store old clauses:
    eliminated[v] = true;
    setDecisionVar(v, false);
    eliminated_vars++;

    if (pos.size() > neg.size()){
        for (int i = 0; i < neg.size(); i++)
            mkElimClause(elimclauses, v, ca[neg[i]]);
        mkElimClause(elimclauses, mkLit(v));
    }else{
        for (int i = 0; i < pos.size(); i++)
            mkElimClause(elimclauses, v, ca[pos[i]]);
        mkElimClause(elimclauses, ~mkLit(v));
    }

    for (int i = 0; i < cls.size(); i++)
        removeClause(cls[i]);

    // Produce clauses in cross product:
    vec<Lit>& resolvent = add_tmp;
    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, resolvent) && !addClause_(resolvent))
                return false;

    // Free occurs list for this variable:
    occurs[v].clear(true);

    // Free watchers lists for this variable, if possible:
    if (watches[ mkLit(v)].size() == 0) watches[ mkLit(v)].clear(true);
    if (watches[~mkLit(v)].size() == 0) watches[~mkLit(v)].clear(true);

    return backwardSubsumptionCheck();
}


bool SimpSolver::substitute(Var v, Lit x)
{
    assert(!frozen[v]);
    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    if (!ok) return false;

    eliminated[v] = true;
    setDecisionVar(v, false);
    const vec<CRef>& cls = occurs.lookup(v);

    vec<Lit>& subst_clause = add_tmp;
    for (int i = 0; i < cls.size(); i++){
        Clause& c = ca[cls[i]];

        subst_clause.clear();
        for (int j = 0; j < c.size(); j++){
            Lit p = c[j];
            subst_clause.push(var(p) == v ? x ^ sign(p) : p);
        }

        removeClause(cls[i]);

        if (!addClause_(subst_clause))
            return ok = false;
    }

    return true;
}


void SimpSolver::extendModel()
{
    int i, j;
    Lit x;

    for (i = elimclauses.size()-1; i > 0; i -= j){
        for (j = elimclauses[i--]; j > 1; j--, i--)
            if (modelValue(toLit(elimclauses[i])) != l_False)
                goto next;

        x = toLit(elimclauses[i]);
        model[var(x)] = lbool(!sign(x));
    next:;
    }
}

bool SimpSolver::simp_time_limit_exceeded()
{
    return ( (simp_time_limit < 0) || (cpuTime() - simp_start_time > simp_time_limit) );
}

bool SimpSolver::eliminate(bool turn_off_elim)
{
    printf("*** Calling eliminate with grow = %d and clause_lim = %d\n", grow, clause_lim);

    if (!simplify())
        return false;
    else if (!use_simplification)
        return true;

    simp_start_time = cpuTime();

    // Main simplification loop:
    //
    while (n_touched > 0 || bwdsub_assigns < trail.size() || elim_heap.size() > 0){

        gatherTouchedClauses();
        // printf("  ## (time = %6.2f s) BWD-SUB: queue = %d, trail = %d\n", cpuTime(), subsumption_queue.size(), trail.size() - bwdsub_assigns);
        if ((subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()) &&
            !backwardSubsumptionCheck(true)){
            ok = false; goto cleanup; }

        // Empty elim_heap and return immediately on user-interrupt:
        if (asynch_interrupt || simp_time_limit_exceeded() ){
            assert(bwdsub_assigns == trail.size());
            assert(subsumption_queue.size() == 0);
            assert(n_touched == 0);
            elim_heap.clear();
            goto cleanup; }

        // printf("  ## (time = %6.2f s) ELIM: vars = %d\n", cpuTime(), elim_heap.size());
        for (int cnt = 0; !elim_heap.empty(); cnt++){
            Var elim = elim_heap.removeMin();

            if (asynch_interrupt || simp_time_limit_exceeded()) break;

            if (isEliminated(elim) || value(elim) != l_Undef) continue;

            if (verbosity >= 2 && cnt % 100 == 0)
                printf("elimination left: %10d\r", elim_heap.size());

            if (use_asymm){
                // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                bool was_frozen = frozen[elim];
                frozen[elim] = true;
                if (!asymmVar(elim)){
                    ok = false; goto cleanup; }
                frozen[elim] = was_frozen; }

            // At this point, the variable may have been set by assymetric branching, so check it
            // again. Also, don't eliminate frozen variables:
            if (use_elim && value(elim) == l_Undef && !frozen[elim] && !eliminateVar(elim)){
                ok = false; goto cleanup; }

            checkGarbage(simp_garbage_frac);
        }

        assert(subsumption_queue.size() == 0);
    }
 cleanup:

    // If no more simplification is needed, free all simplification-related data structures:
    if (turn_off_elim){
        touched  .clear(true);
        occurs   .clear(true);
        n_occ    .clear(true);
        elim_heap.clear(true);
        subsumption_queue.clear(true);

        use_simplification    = false;
        remove_satisfied      = true;
        ca.extra_clause_field = false;

        // Force full cleanup (this is safe and desirable since it only happens once):
        rebuildOrderHeap();
        garbageCollect();
    }else{
        // Cheaper cleanup:
        cleanUpClauses(); // TODO: can we make 'cleanUpClauses()' not be linear in the problem size somehow?
        checkGarbage();
    }

    if (verbosity >= 1 && elimclauses.size() > 0)
        printf("|  Eliminated clauses:     %10d                                         |\n", elimclauses.size());

    return ok;
}


void SimpSolver::cleanUpClauses()
{
    occurs.cleanAll();
    int i,j;
    for (i = j = 0; i < clauses.size(); i++)
        if (ca[clauses[i]].mark() == 0)
            clauses[j++] = clauses[i];
    clauses.shrink(i - j);
}


//=================================================================================================
// Garbage Collection methods:


void SimpSolver::relocAll(ClauseAllocator& to)
{
    if (!use_simplification) return;

    // All occurs lists:
    //
    for (int i = 0; i < nVars(); i++){
        vec<CRef>& cs = occurs[i];
        for (int j = 0; j < cs.size(); j++)
            ca.reloc(cs[j], to);
    }

    // Subsumption queue:
    //
    for (int i = 0; i < subsumption_queue.size(); i++)
        ca.reloc(subsumption_queue[i], to);

    // Temporary clause:
    //
    ca.reloc(bwdsub_tmpunit, to);
}


void SimpSolver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());

    cleanUpClauses();
    to.extra_clause_field = ca.extra_clause_field; // NOTE: this is important to keep (or lose) the extra fields.
    relocAll(to);
    Solver::relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n",
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}



//=================================================================================================
// NEW:

void SimpSolver::readRGCNF(StreamBuffer& in)
{
    bool seenHeader = false;
    bool isGcnf = false;

    unsigned numDeclaredVars=0, numDeclaredClauses=0, numDeclaredGroups=0;

    vector<int> lits;
    vector<int> groupRestriction;
    unsigned group;

    for (;;){
        skipWhitespace(in);
        if (*in == EOF) break;
        else if (*in == 'p') {
            isGcnf = readHeader(in, numDeclaredVars, numDeclaredClauses, numDeclaredGroups);
            seenHeader = true;
        } else if (*in == 'c') {
            bool readRestrictionClause = readComment(in, groupRestriction);
            if (readRestrictionClause) {
                assert(seenHeader && isGcnf);
                //Currently we don't do anything with restrictions
            }
        }
        else if (*in == '{') {
            assert(seenHeader && isGcnf);
            readGroupClause(in, group, lits);
            addOriginalClause(group, lits);
        } else {
            assert(seenHeader && !isGcnf);
            readClause(in, lits);
            group = mOriginalClauses.size() + 1;
            addOriginalClause(group, lits);
        }
    }

    unsigned max_var = 0;
    for (unsigned i=0; i<mOriginalClauses.size(); ++i) {
        for (unsigned j=0; j<mOriginalClauses[i].size(); ++j) {
            if (max_var < (unsigned) abs(mOriginalClauses[i][j]))
                max_var = abs(mOriginalClauses[i][j]);
        }
    }
    mMaxOriginalVar = max_var;

    if (mMaxOriginalVar > numDeclaredVars) {
        printf("PARSE ERROR! number of actual variables %u exceeds the number of %u declared variables\n", mMaxOriginalVar, numDeclaredVars), exit(3);
    }

    if (mOriginalClauses.size() != numDeclaredClauses) {
        printf("PARSE WARNING: number of actual clauses does not match HEADER\n");
    }

    if (isGcnf && (mGroups.size() != numDeclaredGroups + 1)) {
        printf("PARSE WARNING: number of actual groups does not match HEADER\n");
    }

    printf("RGCNF contains %u vars, %u clauses, %u groups\n", mMaxOriginalVar, (unsigned) mOriginalClauses.size(),(unsigned)  mGroups.size());

    sendOriginalCnfToSolver();

    printf("*** After reading solver contains %d variables and %d clauses\n", nVars(), nClauses());


}

void SimpSolver::addOriginalClause(unsigned groupId, const vector<int>& clause)
{
    // Record the clause and group information
    unsigned clauseId = mOriginalClauses.size();
    mOriginalClauses.push_back(clause);
    mContainingGroup.push_back(groupId);

    while (groupId >= mGroups.size()) {
        vector<unsigned> emptyGroup;
        mGroups.push_back(emptyGroup);
    }

    mGroups[groupId].push_back(clauseId);
}


void SimpSolver::displayClauses()
{
    for (int i = 0; i < clauses.size(); i++)
    {
        //if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++) {
                //if (value(c[i]) != l_False)
                    printf("%s%d ", sign(c[j]) ? "-" : "", var(c[j]));
            }
            printf("0\n");
        //}
    }
}

// Add clauses to the SAT-solver
void SimpSolver::sendOriginalCnfToSolver()
{
    for (unsigned clauseId=0; clauseId<mOriginalClauses.size(); ++clauseId)
    {
        int var, lit;
        vec<Lit> lits;

        unsigned groupId = mContainingGroup[clauseId];
        for (unsigned i=0; i<mOriginalClauses[clauseId].size(); ++i)
        {
            lit = mOriginalClauses[clauseId][i];
            var = abs(lit)-1;
            while (var >= nVars()) newVar();
            lits.push( (lit > 0) ? mkLit(var) : ~mkLit(var) );
        }

        if (groupId > 0)
        {
            int group_activation_var = mMaxOriginalVar + groupId - 1;
            while (group_activation_var >= nVars()) newVar();
            lits.push(mkLit(group_activation_var));
        }

        addClause_(lits);
    }

    //printf("DISPLAYING CLAUSES:\n");
    //displayClauses();

}

void SimpSolver::freezeLabels()
{
    for (int var = mMaxOriginalVar; var < nVars(); var++) {
        setFrozen(var, true);
    }
}

vector<unsigned> intersect_sorted_vectors(const vector<unsigned>& u, const vector<unsigned>& v)
{
    vector<unsigned> w;
    unsigned ind_u = 0, ind_v = 0;
    while (1)
    {
        if (ind_u >= u.size()) break;
        if (ind_v >= v.size()) break;

        if (u[ind_u] == v[ind_v]) {
            w.push_back(u[ind_u]);
            ind_u++;
            ind_v++;
        }
        else if (u[ind_u] > v[ind_v]) {
            ind_v++;
        }
        else {
            ind_u++;
        }
    }

    return w;
}

void SimpSolver::writeSimplifiedRGCNF(const char *file)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);

    unsigned numGroups = (mGroups.size() == 0) ? mGroups.size() : (mGroups.size()-1);
    unsigned numClauses = nClauses() + numGroups;
    if (handle_removable==1) numClauses -= (unsigned) mRedundantGroups.size();
    fprintf(f, "p gcnf %d %d %d\n", nVars(), numClauses, numGroups);
    for (int i = 0; i < clauses.size(); i++)
    {
        Clause& c = ca[clauses[i]];
        fprintf(f, "{0} ");
        for (int j = 0; j < c.size(); j++)
        {
            fprintf(f, "%s%d ", sign(c[j]) ? "-" : "", var(c[j])+1);
        }
        fprintf(f, "0\n");
    }

    if (handle_removable==2)
    {
        for (unsigned i=0; i<mRedundantGroups.size(); ++i)
        {
            unsigned groupId = mRedundantGroups[i];
            fprintf(f, "{0} -%d 0\n", groupId);
        }
    }

    for (unsigned groupId=1; groupId <= numGroups; ++groupId)
    {
        if ((handle_removable==0) || !mIsRedundantGroup[groupId])
        {
            fprintf(f, "{%d} -%d 0\n", groupId, groupId + mMaxOriginalVar);
        }
    }

    // Write size-1 MCSes
    for (unsigned i = 0; i<mNecessaryGroups.size(); ++i)
    {
        fprintf(f, "c restrict %u 0\n", mNecessaryGroups[i]);
    }

    // Write binary restrictions
    for (unsigned i = 0; i<restrictionClauses.size(); ++i)
    {
        fprintf(f, "c restrict ");
        for (unsigned j=0; j<restrictionClauses[i].size(); ++j)
        {
            fprintf(f, "%d ", restrictionClauses[i][j]);
        }
        fprintf(f, "0\n");
    }

    fclose(f);
}

void SimpSolver::writeRGCNF(const char *file)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);

    // Compute the number of remaining clauses
    unsigned numRemovedClauses = 0;
    if (handle_removable == 1)
    {
        for (unsigned i=0; i<mRedundantGroups.size(); ++i)
        {
            unsigned groupId = mRedundantGroups[i];
            numRemovedClauses += mGroups[groupId].size();
        }
    }

    unsigned numRemainingClauses = mOriginalClauses.size() - numRemovedClauses;
    unsigned numGroups = (mGroups.size() == 0) ? mGroups.size() : (mGroups.size()-1);
    fprintf(f, "p gcnf %u %u %u\n", mMaxOriginalVar, numRemainingClauses, numGroups);

 /*   // Write clauses in globally removed groups as group-0 clauses (if required)
    if (handle_removable==2)
    {
        for (unsigned i=0; i<mRedundantGroups.size(); ++i)
        {
            unsigned groupId = mRedundantGroups[i];
            for (unsigned j=0; j<mGroups[groupId].size(); ++j)
            {
                unsigned clauseId = mGroups[groupId][j];
                fprintf(f, "{0} ");
                for (unsigned j=0; j<mOriginalClauses[clauseId].size(); ++j)
                {
                    fprintf(f, "%d ", mOriginalClauses[clauseId][j]);
                }
                fprintf(f, "0\n");
            }
        }
    }*/

    for (unsigned clauseId=0; clauseId<mOriginalClauses.size(); ++clauseId)
    {
        unsigned groupId = mContainingGroup[clauseId];
        if ((handle_removable==0) || !mIsRedundantGroup[groupId])
        {
            fprintf(f, "{%u} ", groupId);
            for (unsigned j=0; j<mOriginalClauses[clauseId].size(); ++j)
            {
                fprintf(f, "%d ", mOriginalClauses[clauseId][j]);
            }
            fprintf(f, "0\n");
        }
        else if (handle_removable==2)
        {
            fprintf(f, "{%u} ", 0);
            for (unsigned j=0; j<mOriginalClauses[clauseId].size(); ++j)
            {
                fprintf(f, "%d ", mOriginalClauses[clauseId][j]);
            }
            fprintf(f, "0\n");
        }
    }

    // Write size-1 MCSes
    for (unsigned i = 0; i<mNecessaryGroups.size(); ++i)
    {
        fprintf(f, "c restrict %u 0\n", mNecessaryGroups[i]);
    }

    // In theory, we could make use of redundant clauses.
    // There are multiple ways for doing so:
    //   - simply removing these
    //   - putting to group-0
    //   - adding restriction clause specifying that a redundant clause can't be in MUS
    // This is left for future work.

    // Write binary restrictions
    for (unsigned i = 0; i<restrictionClauses.size(); ++i)
    {
        fprintf(f, "c restrict ");
        for (unsigned j=0; j<restrictionClauses[i].size(); ++j)
        {
            fprintf(f, "%d ", restrictionClauses[i][j]);
        }
        fprintf(f, "0\n");
    }

    fclose(f);
}





void SimpSolver::analyzeLabeledClauses()
{
    double analyze_start_time = cpuTime();

    if (verbosity>=3)
    {
        printf("*** Displaying preprocessed clauses:\n");
        displayClauses();
    }

    // 1. Extract labels for each active clause in the SAT-solver
    vector < vector<unsigned> > labelClauses;

    for (int i = 0; i < clauses.size(); i++) {
        //if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            vector<unsigned> lbls;
            for (int j = 0; j < c.size(); j++) {
                //if (value(c[i]) != l_False) {
                    if ((unsigned)var(c[j]) >= mMaxOriginalVar) {
                        // This is a label and not the original literal
                        lbls.push_back(var(c[j]) - mMaxOriginalVar + 1);
                        std::sort(lbls.begin(), lbls.end());
                    }
                //}
            }
            if (!lbls.empty()) {
                labelClauses.push_back(lbls);
            }
        //}
    }

    printf("*** After extracting labels, have %u labeled clauses\n", (unsigned) labelClauses.size());
    if (verbosity>=3)
    {
        for (unsigned i=0; i<labelClauses.size(); i++) {
            for (unsigned j=0; j<labelClauses[i].size(); j++) {
                printf("%u ", labelClauses[i][j]);
            }
            printf("\n");
        }
    }

    // 2. For each label, create the occurrence list of the labeled clause it appears in
    vector < vector <unsigned> > labelOccs(mGroups.size());
    for (unsigned i=0; i<labelClauses.size(); i++) {
        for (unsigned j=0; j<labelClauses[i].size(); j++) {
            labelOccs[ labelClauses[i][j] ].push_back(i);
        }
    }

    if (verbosity>=3)
    {
        printf("*** After creating occurrence lists\n");
        for (unsigned i=1; i<labelOccs.size(); i++) {
            printf("%6d : ", i);
            for (unsigned j=0; j<labelOccs[i].size(); j++) {
                printf("%d ", labelOccs[i][j]);
            }
            printf("\n");
        }
    }

    // 3. We consider two special types of labels
    //  - label is not present in any clause
    //    this means that the corresponding original group is not in any GMUS (i.e. redundant)
    //  - label is present in every clause
    //    hence removing this label will make the resulting formula empty (and hence SAT)
    //    this means that this label is necessary
    mIsNecessaryGroup.resize(mGroups.size(), false);
    mIsRedundantGroup.resize(mGroups.size(), false);

    for (unsigned i=1; i<labelOccs.size(); i++) {
        if (labelOccs[i].size() == 0) {
            mIsRedundantGroup[i] = true;
            mRedundantGroups.push_back(i);
        }
        else if (labelOccs[i].size() == labelClauses.size()) {
            mIsNecessaryGroup[i] = true;
            mNecessaryGroups.push_back(i);
        }
    }
    printf("*** We have %u necessary and %u redundant labels\n", (unsigned) mNecessaryGroups.size(), (unsigned) mRedundantGroups.size());
    printf("CURRENT ANALYSIS TIME: %6.2f\n", cpuTime() - analyze_start_time);

    if (lve_only)
    {
        return;
    }

    // 4. For each other label L1, we want to examine all clauses that contain L1, and find
    //    if there are other labels contained in all of these clauses
    //    For example, suppose that every clause that contains L1 also contains L2
    //    (of course, there can be more clauses labeled with L2 but not with L1).
    //    Then removing L2-labeled clauses would also remove L1-labeled clauses.
    //    I.e. for every MUS: if L2 is not there, then also L1 is not there.
    //    Equivalently: if L1 in a MUS, then L2 is also in that MUS.
    //    Restriction clause: (-L1, L2).
    vector<int> restrictClause(2);
    for (unsigned u=1; u<labelOccs.size(); u++) {
        if (mIsRedundantGroup[u] || mIsNecessaryGroup[u]) continue;
        vector<unsigned>& occClauseIds = labelOccs[u];

        vector<unsigned> remainingLabels = labelClauses[ occClauseIds[0] ];

        for (unsigned j=1; j< occClauseIds.size(); ++j) {
            vector<unsigned>& nextLabels = labelClauses[ occClauseIds[j] ];
            vector<unsigned> newLabels = intersect_sorted_vectors(remainingLabels, nextLabels);
            remainingLabels = newLabels;
            if (remainingLabels.size() == 1 + mNecessaryGroups.size()) break;
        }

        if (remainingLabels.size() > 1 + mNecessaryGroups.size()) {
            if (verbosity >= 2) printf(" RESTRICT %6u -> ", u);
            for (unsigned j=0; j<remainingLabels.size(); ++j)
            {
                unsigned v = remainingLabels[j];
                if ((v==u) || mIsNecessaryGroup[v]) continue;
                restrictClause[0] = -(int) u;
                restrictClause[1] =  (int) v;
                restrictionClauses.push_back(restrictClause);
                if (verbosity >= 2) printf("%6u ", v);

                if ((restrict_cap >= 0) && (restrictionClauses.size() > (unsigned) restrict_cap)) {
                    printf("restriction-cap reached\n");
                    break;
                }
            }
            if (verbosity >= 2) printf("\n");
        }
        if ((restrict_cap >= 0) && (restrictionClauses.size() > (unsigned) restrict_cap)) break;
    }
    printf("*** We have %u necessary, %u redundant, and %u binary restriction clauses\n", (unsigned) mNecessaryGroups.size(), (unsigned) mRedundantGroups.size(), (unsigned) restrictionClauses.size());


    if (restrict_reduce)
    {
        printf("Running transitive reduction on binary clauses (only equivalences = %d)\n", eq_only);
        vector < vector <int> > reducedRestrictionClauses;
        reduce_bin_clauses(restrictionClauses, reducedRestrictionClauses, eq_only);
        restrictionClauses.swap(reducedRestrictionClauses);
    }
    else
    {
        printf("NOT running transitive reduction on binary clauses\n");
    }
    printf("FINAL: *** We have %u necessary, %u redundant, and %u binary restriction clauses\n", (unsigned) mNecessaryGroups.size(), (unsigned) mRedundantGroups.size(), (unsigned) restrictionClauses.size());
    printf("TOTAL ANALYSIS TIME: %6.2f\n", cpuTime() - analyze_start_time);
}
