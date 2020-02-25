/****************************************************************************************[Dimacs.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
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

#ifndef Minisat_Dimacs_h
#define Minisat_Dimacs_h

#include <stdio.h>

#include "utils/ParseUtils.h"
#include "core/SolverTypes.h"

// Even though MiniSat offers its own vector classes, it's much easier for me to work with the STL ones
#include <vector>
using std::vector;

namespace Minisat {

//=================================================================================================
// DIMACS Parser:

template<class B>
static void readClause(B& in, vector<int>& lits) {
    int     parsed_lit;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        lits.push_back( parsed_lit );
    }
}

template<class B>
static void readGroupClause(B& in, unsigned &group, vector<int>& lits) {
    int     parsed_lit;

    // Read the group information
    assert(*in == '{');
    ++in;
    parsed_lit = parseInt(in);
    if (parsed_lit<0) fprintf(stderr, "PARSE ERROR! Negative group: %d\n", parsed_lit), exit(3);
    group = parsed_lit;
    skipWhitespace(in);
    if (*in != '}') fprintf(stderr, "PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
    ++in;

    // Read the rest of the clause
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        lits.push_back( parsed_lit );
    }
}

template<class B>
static bool readComment(B& in, vector<int>& group_restriction) {
    bool read_clause = false;
    assert (*in == 'c');
    if (eagerMatch(in, "c restrict")) {
        // group restriction clause
        read_clause = true;
        group_restriction.clear();
        int parsed_lit;
        for (;;){
            parsed_lit = parseInt(in);
            if (parsed_lit == 0) break;
            group_restriction.push_back( parsed_lit );
        }
    }
    else {
        // regular comment
        skipLine(in);
    }
    return read_clause;
}


template<class B>
static bool readHeader(B& in, unsigned &num_vars, unsigned &num_clauses, unsigned &num_groups)
{
    bool is_gcnf = false;
    assert(*in == 'p');
    ++in;
    skipWhitespace(in);
    if (eagerMatch(in, "cnf")) {
        num_vars    = parseInt(in);
        num_clauses = parseInt(in);
        num_groups = num_clauses;
    }
    else if (eagerMatch(in, "gcnf")) {
        num_vars    = parseInt(in);
        num_clauses = parseInt(in);
        num_groups  = parseInt(in);
        is_gcnf = true;
    }
    else  {
        printf("PARSE ERROR! Unexpected char: %c\n", *in);
        exit(3);
    }
    return is_gcnf;
}

//=================================================================================================
}

#endif
