// CNF parsing code is copied from Minisat.

#include <stdio.h>
#include <stdlib.h>
#include <zlib.h>
#include <vector>
#include <string>
#include <string.h>
#include <set>
#include <iostream>
#include "assert.h"
#include <climits>
#include <algorithm>
#include <sys/time.h>

#include "utils.hpp"
#include "bce.hpp"

//#define ASSERT(s) assert(s)
#define ASSERT(s)

#include "reduceBins.h"

using namespace std;


//-------------------------------------------------------------------------------------------------
// Timing support
//-------------------------------------------------------------------------------------------------
double getCurrentTime()
{
    struct timeval tm;
    gettimeofday(&tm, NULL);
    double t = tm.tv_sec + (tm.tv_usec/1000000.0);
    return t;
}

double BceFinder::timeElapsed()
{
    return getCurrentTime() - mTimer;
}

bool BceFinder::outOfTime()
{
    if (!mOutOfTime && (timeElapsed() >= mOpts.mTimeLimit))
    {
        mOutOfTime = true;
        printf("TIME-LIMIT of %u seconds reached\n", mOpts.mTimeLimit);
    }

    return mOutOfTime;
}


//-------------------------------------------------------------------------------------------------
// Read / write support
//-------------------------------------------------------------------------------------------------

template <class B>
void BceFinder::readRGCNF(B& in)
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
                ASSERT(seenHeader && isGcnf);
                addGroupRestriction(groupRestriction);
            }
        }
        else if (*in == '{') {
            ASSERT(seenHeader && isGcnf);
            readGroupClause(in, group, lits);
            addClause(group, lits);
        } else {
            ASSERT(seenHeader && !isGcnf);
            readClause(in, lits);
            group = mClauses.size() + 1;
            addClause(group, lits);
        }
    }

    unsigned max_var = 0;
    for (unsigned i=0; i<mClauses.size(); ++i) {
        for (unsigned j=0; j<mClauses[i].size(); ++j) {
            if (max_var < abs(mClauses[i][j]))
                max_var = abs(mClauses[i][j]);
        }
    }
    mMaxVar = max_var;

    if (mMaxVar > numDeclaredVars) {
        printf("PARSE WARNING: number of actual variables exceed HEADER\n");
    }

    if (mClauses.size() != numDeclaredClauses) {
        printf("PARSE WARNING: number of actual clauses does not match HEADER\n");
    }

    if (isGcnf && (mGroups.size() != numDeclaredGroups + 1)) {
        printf("PARSE WARNING: number of actual groups does not match HEADER\n");
    }

    printf("RGCNF contains %u vars, %u clauses, %u groups, %u mcses\n", mMaxVar, mClauses.size(), mGroups.size(), mNecessaryGroups.size());

    printAll();
}


// Writes the problem (in the EGCNF format).
// This includes:
//   (1) The main GCNF (as appears in mGroups, mClauses); this is possibly already simplified;
//   (2) Lists of equivalent nodes;
//   (3) Graph storing additional implications.
// Note that depending on the work done by the main algorithm, the same information may be represented
// in different ways, for example if SCC detection was not run, then equivalences are implicitly presents
// as part of the dependency graph; if the SCC detection was run but the corresponding groups were not
// explicitly merged in GCNF, then equivalent groups are passed via the dedicated argument; and if the SCC
// equivalence was run and the groups were merged in GCNF, then there is no longer need to pass these.
template <class B>
void BceFinder::writeRGCNF(B& out)
{
    /////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // We need to write GCNF header and for that we need to know the number of variables, clauses and groups.
    // (We do this in two-pass approach)
    /////////////////////////////////////////////////////////////////////////////////////////////////////////////

    /////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Compute only
    /////////////////////////////////////////////////////////////////////////////////////////////////////////////

    unsigned numRemainingClauses = 0;
    for (unsigned clauseId = 0; clauseId < mClauses.size(); ++clauseId)
    {
        if (mClauseIsEnabled[clauseId] || (mOpts.mHandleRemoved==0) || (mOpts.mHandleRemoved==2))
            numRemainingClauses++;
    }
    unsigned numGroups = (mGroups.size() == 0) ? 0 : (mGroups.size() - 1);

    /////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Write header
    /////////////////////////////////////////////////////////////////////////////////////////////////////////////

    writeHeader(out, mMaxVar, numRemainingClauses, numGroups);

    /////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Actually write
    /////////////////////////////////////////////////////////////////////////////////////////////////////////////

    // Write globally removed clauses as group-0 clauses (if required)
/*    if (mOpts.mHandleRemoved==2)
    {
        for (unsigned clauseId = 0; clauseId < mClauses.size(); ++clauseId)
        {
            if (!mClauseIsEnabled[clauseId])
                writeGroupClause(out, 0, mClauses[clauseId]);
        }
    }
*/
    // Write groups
    for (unsigned groupId = 0; groupId < mGroups.size(); ++groupId)
    {
        for (unsigned i = 0; i<mGroups[groupId].size(); ++i)
        {
            unsigned clauseId = mGroups[groupId][i];
            if ( (mClauseIsEnabled[clauseId]) || (mOpts.mHandleRemoved==0) )
            {
                writeGroupClause(out, groupId, mClauses[clauseId]);
            }
            else if (mOpts.mHandleRemoved==2)
            {
                writeGroupClause(out, 0, mClauses[clauseId]);
            }
        }
    }

    // Write necessary groups (as hints)
    for (unsigned i=0; i<mNecessaryGroups.size(); ++i)
    {
        unsigned groupId = mNecessaryGroups[i];
        writeGroupNecessity(out, groupId);
    }

    // Write restriction clauses (as hints)
    for (unsigned i=0; i<mRestrictionClauses.size(); ++i)
    {
        writeGroupRestriction(out, mRestrictionClauses[i]);
    }
}


// For now, we only handle positive unit restrictions (i.e. those that specify that a certain
// group is necessary).
void BceFinder::addGroupRestriction(const vector<int>& restriction)
{
    if ((restriction.size() == 1) && (restriction[0] > 0))
    {
        markGroupAsNecessary(restriction[0]);
    }
}

void BceFinder::addClause(unsigned groupId, const vector<int>& clause)
{
    unsigned clauseId = mClauses.size();
    mClauses.push_back(clause);
    mClauseIsEnabled.push_back(true);
    mContainingGroup.push_back(groupId);
    mClauseEnabledCnt++;

    while (groupId >= mGroups.size()) {
        vector<unsigned> emptyGroup;
        mGroups.push_back(emptyGroup);
        mGroupEnabledCnt.push_back(0);
    }

    mGroups[groupId].push_back(clauseId);
    mGroupEnabledCnt[groupId]++;
}

void BceFinder::markGroupAsNecessary(unsigned groupId)
{
    ASSERT(!isGroupRemoved(groupId));

    while (groupId >= mGroupIsNecessary.size())
        mGroupIsNecessary.push_back(false);

    if (!mGroupIsNecessary[groupId])
    {
        mGroupIsNecessary[groupId] = true;
        mNecessaryGroups.push_back(groupId);
    }
}

void BceFinder::markGroupAsRemoved(unsigned groupId)
{
    ASSERT(!isGroupNecessary(groupId));

    while (groupId >= mGroupIsRemoved.size())
        mGroupIsRemoved.push_back(false);

    if (!mGroupIsRemoved[groupId])
    {
        mGroupIsRemoved[groupId] = true;
        mRemovedGroups.push_back(groupId);
    }
}

bool BceFinder::isGroupNecessary(unsigned groupId)
{
    return (groupId < mGroupIsNecessary.size()) && (mGroupIsNecessary[groupId]);
}

bool BceFinder::isGroupRemoved(unsigned groupId)
{
    return (groupId < mGroupIsRemoved.size()) && (mGroupIsRemoved[groupId]);
}

// Merges from first group to second group
void BceFinder::mergeGroups(unsigned firstGroupId, unsigned secondGroupId)
{
    ASSERT(firstGroupId != secondGroupId);
    //printf("MERGING from %d to %d\n", firstGroupId, secondGroupId);
    for (unsigned i=0; i<mGroups[firstGroupId].size(); ++i)
    {
        unsigned clauseId = mGroups[firstGroupId][i];
        mContainingGroup[clauseId] = secondGroupId;
        mGroups[secondGroupId].push_back(clauseId);
    }
    mGroupEnabledCnt[secondGroupId] += mGroupEnabledCnt[firstGroupId];
    mGroups[firstGroupId].clear();
    mGroupEnabledCnt[firstGroupId] = 0;
}


void BceFinder::printClause(const vector<int>& c)
{
    for (unsigned j=0; j<c.size(); ++j)
        printf("%d ", c[j]);

}

void BceFinder::printAllClauses()
{
    printf("Clauses:\n");
    for (unsigned i=0; i<mClauses.size(); ++i) {
        printf("%5d {%d}", i, mContainingGroup[i]);
        if (mClauseIsEnabled[i])
            printf("[*]: ");
        else
            printf("   : ");
        printClause(mClauses[i]);
        printf("\n");
    }
}

void BceFinder::printAllGroups()
{
    printf("Groups:\n");
    for (unsigned groupId = 0; groupId < mGroups.size(); ++groupId)
    {
        printf("%5d (%d / %d) : ", groupId, mGroupEnabledCnt[groupId], mGroups[groupId].size());
        for (unsigned i=0; i< mGroups[groupId].size(); ++i)
        {
            printf("%d ", mGroups[groupId][i]);
        }
        printf("\n");
    }
}

void BceFinder::printAll()
{
    if (mOpts.mVerbosity >= 2)
    {
        printAllClauses();
        //printAllGroups();
    }
    printInfoOnGroups();
}

void BceFinder::printInfoOnGroups()
{
    unsigned en = 0;
    for (unsigned groupId=1; groupId<mGroups.size(); ++groupId)
    {
        if (mGroupEnabledCnt[groupId] != 0)
            ++en;
    }
    printf("Groups info: %u groups, %u enabled, %u disabled\n", mGroups.size(), en, mGroups.size() - en);
}

bool BceFinder::checkInternalDatabaseIsOk() const
{
    for (unsigned groupId = 0; groupId < mGroups.size(); ++groupId)
    {
        unsigned numEnabledInGroup = 0;
        for (unsigned i=0; i<mGroups[groupId].size(); ++i)
        {
            unsigned clauseId = mGroups[groupId][i];

            if (mClauseIsEnabled[clauseId])
            {
                numEnabledInGroup++;
                if (mContainingGroup[clauseId] != groupId)
                {
                    printf("CheckError: clauseId %u has mismatching groupId %u\n", clauseId, groupId);
                    return false;
                }
            }
        }

        if (numEnabledInGroup != mGroupEnabledCnt[groupId])
        {
            printf("CheckError: number of enabled clauses in groupId %u is incorrect\n", groupId);
            return false;
        }
    }

    unsigned numEnabled = 0;
    for (unsigned clauseId = 0; clauseId < mClauses.size(); ++clauseId)
    {
        if (mClauseIsEnabled[clauseId])
            numEnabled++;
    }
    if (numEnabled != mClauseEnabledCnt)
    {
        printf("CheckError: number of total enabled clauses is incorrect\n");
        return false;
    }
    //printf("---CHECK IS OK---\n");
    return true;
}

//-------------------------------------------------------------------------------------------------
// BCE support
//-------------------------------------------------------------------------------------------------

unsigned BceFinder::lit2index(int lit) const
{
    return 2 * abs(lit) + (lit < 0);
}

void BceFinder::touchLit(int lit)
{
    if (!mTouched[ lit2index(lit) ])
    {
        mTouchedLits.push_back(lit);
        mTouched[ lit2index(lit) ] = true;
    }
}

void BceFinder::untouchLit(int lit)
{
    mTouched[ lit2index(lit) ] = false;
}

void BceFinder::touchLitsInClauseNegation(const vector<int>& c)
{
    for (unsigned i=0; i<c.size(); ++i)
    {
        touchLit(-c[i]);
    }
}

void BceFinder::untouchAllLits()
{
    for (unsigned i=0; i<mTouchedLits.size(); ++i)
    {
        untouchLit(mTouchedLits[i]);
    }
    mTouchedLits.clear();
}

bool BceFinder::checkAllLitsUntouched() const
{
    if (mTouchedLits.size() > 0)
    {
        printf("mTouchedLits.size() = %u\n", mTouchedLits.size());
        return false;
    }

    for (unsigned i=0; i<mTouched.size(); ++i)
    {
        if (mTouched[i])
        {
            printf("mTouched[%u] = true\n", i);
            return false;
        }
    }

    return true;
}

// Return true if c and d resolve tautolically
// lit must be in c, -lit must be in d
bool BceFinder::isResolutionTautological(const vector<int> &c, const vector<int>& d, int lit)
{
    //printf("  resolving ");
    //print_clause(c);
    //printf(" and ");
    //print_clause(d);
    //printf(" on lit %d,", lit);

    bool found = false;
    set<int> c_lits;
    for (unsigned i=0; i<c.size(); ++i)
    {
        if ( c[i] != lit )
            c_lits.insert(c[i]);
    }
    for (unsigned j=0; j<d.size(); ++j) {
        if ((d[j] != -lit) && (c_lits.find(-d[j])!=c_lits.end()))
        {
            found = true;
            break;
        }
    }
    //printf(" is_tautology: %d\n", found);
    return found;
}

// Do BCE using touched lits as the set of literals to examine
// Returns true if ALL the clauses were removed (or a necessary clause was removed)
bool BceFinder::doBce()
{
    bool allRemoved = false;

    while (!mTouchedLits.empty() && !allRemoved)
    {
        int curLit = mTouchedLits.back();
        mTouchedLits.pop_back();
       // printf("Examining lit %d\n", curLit);

        vector<unsigned>& litClauses    = (curLit > 0) ? mOccsPos[ abs(curLit) ] : mOccsNeg[ abs(curLit) ] ;
        vector<unsigned>& negLitClauses = (curLit < 0) ? mOccsPos[ abs(curLit) ] : mOccsNeg[ abs(curLit) ] ;

        for (unsigned litClausePos=0; litClausePos<litClauses.size(); ++litClausePos)
        {
            unsigned litClauseId = litClauses[litClausePos];
            if (!mClauseIsEnabled[litClauseId]) continue;

            //printf("Examining clauseId %u on lit %d\n", litClauseId, curLit);

            bool allResolventsTautological = true;
            for (unsigned negLitClausePos=0; negLitClausePos<negLitClauses.size(); ++negLitClausePos)
            {
                unsigned negLitClauseId = negLitClauses[negLitClausePos];
                if (!mClauseIsEnabled[negLitClauseId]) continue;

                if (!isResolutionTautological(mClauses[litClauseId], mClauses[negLitClauseId], curLit))
                {
                    allResolventsTautological = false;
                    break;
                }
            }

            if (allResolventsTautological)
            {
                //printf("-- clauseId %u can be removed\n", litClauseId);
                // The clause (litClauseId) is blocked on lit, so can be removed
                mClauseIsEnabled[litClauseId] = false;
                mClauseEnabledCnt--;
                mNewDisabledClauses.push_back(litClauseId);
                unsigned groupId = mContainingGroup[litClauseId];
                mGroupEnabledCnt[groupId]--;

                // Check if the corresponding group becomes empty
                if ((mGroupEnabledCnt[groupId] == 0) && (groupId != 0))
                {
                    //printf("-- group %u is now disabled\n", groupId);
                    mNewDisabledGroups.push_back(groupId);

                    // If we are disabling a necessary group, or all the clauses are removed...
                    if (mOpts.mUseForced && (isGroupNecessary(groupId) || (mClauseEnabledCnt==0)))
                    {
                        //printf("-- necessity condition met\n");
                        allRemoved = true;
                        untouchAllLits();
                        break; // out of FOR
                    }
                }

                // all the clauses containing negation of a literal in a blocked clause may now become blocked
                touchLitsInClauseNegation(mClauses[litClauseId]);
            }
        }

        untouchLit(curLit);
    }

    ASSERT(checkAllLitsUntouched());
    return allRemoved;
}

void BceFinder::run()
{
    // Read main file
    printf("Reading file %s\n", mFilename);
    double tt = getCurrentTime();
    InStreamBuffer in(mFilename);
    readRGCNF(in);
    in.close();
    printf("  --completed in %1.2f sec\n", getCurrentTime() - tt);

    // Pos + Neg occurrence lists
    mOccsPos.resize(mMaxVar+1);
    mOccsNeg.resize(mMaxVar+1);
    for (unsigned i=0; i<mClauses.size(); ++i) {
        for (unsigned j=0; j<mClauses[i].size(); ++j) {
            int lit = mClauses[i][j];
            if (lit > 0)
                mOccsPos[ abs(lit) ].push_back(i);
            else
                mOccsNeg[ abs(lit) ].push_back(i);
        }
    }
    mTouched.resize(2 * (mMaxVar+1), false);

    //===========================================================================
    // Perform top-level BCE
    //===========================================================================

    if (!mOpts.mBceSkip)
    {
        printf("Performing top-level BCE\n");

        // set all literals as touched
        for (unsigned i=1; i<=mMaxVar; ++i) {
            touchLit ( (int) i);
            touchLit ( -(int) i);
        }

        tt = getCurrentTime();
        ASSERT(checkInternalDatabaseIsOk());
        doBce();

        printf("  detected %u removable clauses and %u removable groups\n", mNewDisabledClauses.size(), mNewDisabledGroups.size());
        printf("  --completed in %1.2f sec\n", getCurrentTime() - tt);

        for (unsigned i=0; i<mNewDisabledGroups.size(); ++i)
        {
            unsigned groupId = mNewDisabledGroups[i];
            ASSERT(groupId != 0);
            markGroupAsRemoved(mNewDisabledGroups[i]);
        }

        if (mOpts.mVerbosity >= 2)
        {
            printf("TOP-LEVEL REMOVED GROUPS:\n");
            for (unsigned i=0; i<mNewDisabledGroups.size(); ++i)
                printf("%d\n", mNewDisabledGroups[i]);
            printf("\n");

            printAll();
        }
    }
    else
    {
        printf("Skipping top-level BCE\n");
    }

    if (mOpts.mBceOnly)
    {
        if (mOpts.mOutputName != NULL)
        {
            string outputFileName = mOpts.mOutputName;
            printf("Writing simplified problem to file %s\n", outputFileName.c_str());

            tt = getCurrentTime();
            OutStreamBuffer out(outputFileName.c_str());
            writeRGCNF(out);
            out.close();
            printf("  --completed in %1.2f sec\n", getCurrentTime() - tt);
        } // WRITE OUTPUT
        return;
    }

    //===========================================================================
    // Now, we iterative remove a group and see which other groups get removed
    //===========================================================================

    printf("Performing dependency-based BCE\n");
    vector<int> restrictClause(2);

    tt = getCurrentTime();
    for (unsigned groupId=1; groupId<mGroups.size(); ++groupId)
    {
        if (outOfTime())
            break;

        // do not remove necessary groups
        if (isGroupNecessary(groupId))
            continue;

        // do not remove groups that are already removed
        if (isGroupRemoved(groupId))
            continue;

        ASSERT(mGroupEnabledCnt[groupId] > 0);
        ASSERT(checkInternalDatabaseIsOk());

        mNewDisabledClauses.clear();
        mNewDisabledGroups.clear();

        // Disable all clauses in the current group
        mNewDisabledGroups.push_back(groupId);
        for (unsigned i=0; i<mGroups[groupId].size(); ++i)
        {
            unsigned clauseId = mGroups[groupId][i];
            if (mClauseIsEnabled[clauseId])
            {
                mNewDisabledClauses.push_back(clauseId);
                mClauseIsEnabled[clauseId] = false;
                mClauseEnabledCnt--;
                mGroupEnabledCnt[groupId]--;
                touchLitsInClauseNegation(mClauses[clauseId]);
            }
        }
        ASSERT(mGroupEnabledCnt[groupId]==0);
        ASSERT(mNewDisabledGroups.size()==1);
        ASSERT(mNewDisabledClauses.size() > 0);
        unsigned numDisabledClauses =  mNewDisabledClauses.size();

        bool allRemoved = doBce();

        if (allRemoved)
        {
            if (mOpts.mVerbosity >= 1) printf("  --removed group %d/%d, removed group is necessary\n", groupId, mGroups.size());
            markGroupAsNecessary(groupId);
        }
        else
        {
            if (mOpts.mVerbosity >= 1) printf("  --removed group %d/%d, detected %u removable clauses and %u removable groups\n", groupId, mGroups.size(), mNewDisabledClauses.size() - numDisabledClauses, mNewDisabledGroups.size() - 1);
            // add new edges to the group dependency graph

            if (mNewDisabledGroups.size() > 1)
            {
                if (mOpts.mVerbosity >= 1) printf(" RESTRICT %6u <- ", mNewDisabledGroups[0]);
                for (unsigned j=1; j<mNewDisabledGroups.size(); ++j)
                {
                    ASSERT(mNewDisabledGroups[0]!=0);
                    ASSERT(mNewDisabledGroups[j]!=0);

                    restrictClause[0] = -(int) mNewDisabledGroups[j];
                    restrictClause[1] =  (int) mNewDisabledGroups[0];
                    mRestrictionClauses.push_back(restrictClause);
                    if (mOpts.mVerbosity >= 1) printf("%6u ", mNewDisabledGroups[j]);

                    if (mRestrictionClauses.size() > mOpts.mRestrictCap)
                    {
                        printf("restriction-cap reached\n");
                        break;
                    }
                }
                if (mOpts.mVerbosity >= 1) printf("\n");
            }
        }

        // Restore
        for (unsigned i=0; i<mNewDisabledClauses.size(); ++i)
        {
            unsigned currentClauseId = mNewDisabledClauses[i];
            unsigned currentGroupId  = mContainingGroup[currentClauseId];
            mClauseIsEnabled[currentClauseId] = true;
            mClauseEnabledCnt++;
            mGroupEnabledCnt[currentGroupId]++;
        }

        if (mRestrictionClauses.size() > mOpts.mRestrictCap) break;
    }
    printf("  detected %u necessary groups and %u binary restrictions\n", mNecessaryGroups.size(), mRestrictionClauses.size());
    printf("  --completed in %1.2f sec\n", getCurrentTime() - tt);


    //===========================================================================
    // Now, reduce implications
    //===========================================================================

    if (mOpts.mReduceImplies > 0)
    {
        tt = getCurrentTime();
        printf("Running transitive reduction on binary clauses (initially %u binary clauses)\n", mRestrictionClauses.size());
        vector < vector <int> > reducedRestrictionClauses;
        reduce_bin_clauses(mRestrictionClauses, reducedRestrictionClauses, mOpts.mEqOnly);
        mRestrictionClauses.swap(reducedRestrictionClauses);
        printf("Completed transitive reduction (final %u binary clauses)\n", mRestrictionClauses.size());
        printf("  --completed in %1.2f sec\n", getCurrentTime() - tt);
    }
    else
    {
        printf("NOT running transitive reduction on binary clauses\n");
    }

    if (mOpts.mOutputName != NULL)
    {
        string outputFileName = mOpts.mOutputName;
        printf("Writing simplified problem to file %s\n", outputFileName.c_str());

        tt = getCurrentTime();
        OutStreamBuffer out(outputFileName.c_str());
        writeRGCNF(out);
        out.close();
        printf("  --completed in %1.2f sec\n", getCurrentTime() - tt);
    } // WRITE OUTPUT
}





BceFinder::BceFinder(const char *filename, const BceFinderOptions& opts)
{
    mFilename = filename;
    mOpts = opts;
    mMaxVar = 0;
    mClauseEnabledCnt = 0;
    mOutOfTime = false;
    mTimer = getCurrentTime();
    printf("BCE experiment started\n");
}

BceFinder::~BceFinder()
{
    printf("BCE experiment finished in %1.2f sec (timed-out: %d)\n", timeElapsed(), mOutOfTime);
}

unsigned parseValue(int argc, char **argv, unsigned i, const char* name, int minVal, int maxVal)
{
    if (i >= argc)
    {
        printf("Unspecified value for %s\n", name);
        exit(3);
    }
    int val = atoi(argv[i]);
    if ((val < minVal) || (val > maxVal))
    {
        printf("Specified value %d for %s is out-of-range\n", val, name);
        exit(3);
    }
    printf("Setting %s to %d\n", name, val);
    return val;
}

const char* parseStringValue(int argc, char **argv, unsigned i, const char* name)
{
    if (i >= argc)
    {
        printf("Unspecified value for %s\n", name);
        exit(3);
    }

    const char* val = argv[i];

    printf("Setting %s to %s\n", name, val);
    return val;
}

void parseArguments(int argc, char **argv, BceFinderOptions& opts)
{
    for (unsigned i=2; i<argc; i++)
    {
        if (strcmp(argv[i], "-verb")==0)
        {
            opts.mVerbosity = parseValue(argc, argv, ++i, "verb", 0, 3);
        }
        else if (strcmp(argv[i], "-time")==0)
        {
            opts.mTimeLimit = parseValue(argc, argv, ++i, "time", 0, 86400);
        }
        else if (strcmp(argv[i], "-max")==0)
        {
            opts.mRestrictCap = parseValue(argc, argv, ++i, "max", 0, 10000000);
        }
        else if (strcmp(argv[i], "-redundant")==0)
        {
            opts.mHandleRemoved = parseValue(argc, argv, ++i, "redundant", 0, 2);
        }
        else if (strcmp(argv[i], "-reduce")==0)
        {
            opts.mReduceImplies = parseValue(argc, argv, ++i, "reduce", 0, 1);
        }
        else if (strcmp(argv[i], "-fc")==0)
        {
            opts.mUseForced = parseValue(argc, argv, ++i, "use-forced", 0, 1);
        }
        else if (strcmp(argv[i], "-output")==0)
        {
            opts.mOutputName = parseStringValue(argc, argv, ++i, "output");
        }
        else if (strcmp(argv[i], "-bce-only")==0)
        {
            opts.mBceOnly = parseValue(argc, argv, ++i, "bce-only", 0, 1);
        }
        else if (strcmp(argv[i], "-bce-skip")==0)
        {
            opts.mBceSkip = parseValue(argc, argv, ++i, "bce-skip", 0, 1);
        }
        else if (strcmp(argv[i], "-eq-only")==0)
        {
            opts.mEqOnly = parseValue(argc, argv, ++i, "eq-only", 0, 1);
        }
        else
        {
            cout << "Unknown argument: " << argv[i] << endl;
            exit(3);
        }
    }
}

int main(int argc, char ** argv)
{
    if (argc < 2)
    {
        cout << "Usage: " << argv[0] << " [E][G]CNF" << endl;
        return 0;
    }

    BceFinderOptions opts;
    parseArguments(argc, argv, opts);
    BceFinder bce(argv[1], opts);
    bce.run();
}


