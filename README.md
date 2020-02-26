# MARCO WITH CLAUSE DEPENDENCIES
---------------------------------------------------------------------------
This repository contains the source code to find and exploit clause
dependencies for MUS enumeration.

This is not the most elegant or the most efficient code, and the output is a mess -- you've been warned.

We are submitting a paper to SAT'2020. So we also include benchmarks and experimental results here.

---------------------------------------------------------------------------


---------------------------------------------------------------------------
## 1. GCNF format with additional restriction clauses
---------------------------------------------------------------------------
A Group-CNF input format is described in http://www.satcompetition.org/2011/rules.pdf.

We have extended the above format to specify "restriction clauses" using lines such as:
*c restrict -847 760  0*

That is, any regular tool that reads GCNFS will treat the above line as a comment and simply ignore it.
On the other hand, marco_with_restrictions will treat such lines differently from comments.

Here is a longer example:

p gcnf 3 6 6 <br/>
{1} 1 0 <br/>
{2} -1 0 <br/>
{3} 2 0 <br/>
{4} -2 0 <br/>
{5} 3 0 <br/>
{6} -3 0 <br/>
c restrict -2 1 0 <br/>
c restrict -1 2 0 <br/>
c restrict -4 3 0 <br/>
c restrict -3 4 0 <br/>
c restrict -6 5 0 <br/>
c restrict -5 6 0 <br/>

The first 7 lines are in the usual GCNF format. Each "c restrict" line specifies restriction between groups.



---------------------------------------------------------------------------
## 2. marco_with_restrictions
---------------------------------------------------------------------------
Please refer to MARCO algorithm at https://sun.iwu.edu/~mliffito/marco.

marco_with_restrictions is a minor modification of the above, which allows:
	- parsing GCNFs with restriction clauses and passing restriction clauses to msolver
	- disabling the check if seed is explored (not valid with restrictions)
	- minor output tweaks

On the above example, marco_with_restriction will add the clauses
(-2, 1), (-1, 2), (-4, 3), (4, -3), (-6, 5) and (6, -5)
to the map-solver in MARCO.

__to compile__:
marco_with_restrictions should be compiled in exactly the same way as marco.

__to run [example]__:
*python3 -u marco_with_restrictions/marco.py --print-mcses -T 3600 -s -a -v -v ssa2670-129.cnf*



---------------------------------------------------------------------------
## 3. lve_restrict
---------------------------------------------------------------------------
##### Shorter description:

lve_restrict reads a CNF or a GCNF formula and discovers dependencies between clauses (or groups) in the
sense of the submitted SAT'2020 paper. With -output=..., it writes the GCNF with discovered restrictions
(which can be used as an input to marco_with_restrictions)

It is a rather small hack on top of minisat/simp.


#### Longer description:

lve_restrict/minisat_*
    - reads a CNF, GCNF, or GCNF with restrictions
        (however, ignores all restrictions)
    - finds restrictions
    - writes a GCNF with restrictions

    - options:
        -grow, -cl-lim: controls the effort spent on VE
            (ex. -grow=40 -cl-lim=200)

        -verb:      verbosity
        -time:      specifies the time for VE
        -output:    name of the output file
        -max:       allows to restrict the number of binary implications
        -reduce:    reduce binary implications
        -redundant: handling redundant groups (0 - nothing, 1 - remove, 2 - relabel as group-0)
        -eq-only:   only equivalences

        -lve-only:  does not analyze restrictions (only necessary and redudant groups)
        -outputs:   name of the simplified output file

    - __To compile__:
        ./build.sh

    - __To run__:
        lve_restrict/lverestrict <input>.cnf -output=<output>.gcnf -param=<value>

      __Example__:
        *lve_restrict/lverestrict tests/ssa2670-129.cnf -lve-only -redundant=1 -output=aaa2*
---------------------------------------------------------------------------


---------------------------------------------------------------------------
## 4. bce_restrict
---------------------------------------------------------------------------
#### Shorter description:

bce_restrict reads a CNF or a GCNF formula and discovers dependencies between clauses (or groups) in the
sense of the submitted SAT'2020 paper. With -output ..., it writes the GCNF with discovered restrictions
(which can be used as an input to marco_with_restrictions)


#### Longer description:

bce_restrict:
    - reads a CNF, GCNF, or GCNF with restrictions
        (however, for now only positive unit restrictions are used)
    - finds restrictions
    - writes a GCNF with restrictions

    - options:
        -bce-only:  does only top-level BCE
        -bce-skip:  skips top-level BCE

        -verb:      verbosity
        -time:      specifies the time for VE
        -output:    name of the output file
        -max:       allows to restrict the number of binary implications
        -reduce:    reduce binary implications
        -redundant: handling redundant groups (0 - nothing, 1 - remove, 2 - relabel as group-0)
        -eq-only:   only equivalences

    - __to compile__:
        *./build.sh*

    - __to run__:
        *bce_restrict/bcerestrict <input>.cnf -output <output>.gcnf -param <value>*

      __Example__:
        *bce_restrict/bcerestrict tests/ssa2670-129.cnf -bce-only 1 -redundant 1 -output aaa1*
---------------------------------------------------------------------------

---------------------------------------------------------------------------
## 5. benchmarks (used for the paper)
---------------------------------------------------------------------------
Located in benchmarks/

*cnf*: the original 11 benchmarks from the MUS track of the 2011 SAT competition

*bce*: the original 11 benchmrks together with restriction clauses found by bce_restrict

*lve*: the original 11 benchmrks together with restriction clauses found by lve_restrict


---------------------------------------------------------------------------
## 5. experimental results (for the paper)
---------------------------------------------------------------------------
Located in results/

*bce_output*: output of bce_restrict on benchmarks from *cnf* (i.e. this is how *bce* benchmarks are produced)

*lve_output*: output of lve_restrict on benchmarks from *cnf* (i.e. this is how *lve* benchmarks are produced)

*marco_on_cnf_output*: output of *marco_with_restrictions* when running on benchmarks from *cnf*

*marco_on_bce_output*: output of *marco_with_restrictions* when running on benchmarks from *bce*

*marco_on_lve_output*: output of *marco_with_restrictions* when running on benchmarks from *lve*
