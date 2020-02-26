# MARCO WITH CLAUSE DEPENDENCIES
---------------------------------------------------------------------------
This repository contains the source code to find and exploit clause
dependencies for MUS enumeration.

We are submitting a paper to SAT'2020.

This is not the most elegant or the most efficient code -- you've been warned.

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

p gcnf 3 6 6

{1} 1 0

{2} -1 0

{3} 2 0

{4} -2 0

{5} 3 0

{6} -3 0

c restrict -2 1 0

c restrict -1 2 0

c restrict -4 3 0

c restrict -3 4 0

c restrict -6 5 0

c restrict -5 6 0


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

_to compile_:
marco_with_restrictions should be compiled in exactly the same way as marco.

_to use [example]_:
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

    - _To compile_:
        ./build.sh

    - _To run_:
        lve_restrict/lverestrict <input>.cnf -output=<output>.gcnf -param=<value>

      _Example_:
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

    - _to compile_:
        *./build.sh*

    - _to run_:
        *bce_restrict/bcerestrict <input>.cnf -output <output>.gcnf -param <value>*

      _Example_:
        *bce_restrict/bcerestrict tests/ssa2670-129.cnf -bce-only 1 -redundant 1 -output aaa1*
---------------------------------------------------------------------------





