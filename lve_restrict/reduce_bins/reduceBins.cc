
#include <iostream>
#include <vector>
#include <stdio.h>
#include <stdlib.h>
#include <algorithm>
#include <climits>
#include <sys/time.h>

#include "reduceBins.h"

using std::vector;


static double getCurrentTime()
{
    struct timeval tm;
    gettimeofday(&tm, NULL);
    double t = tm.tv_sec + (tm.tv_usec/1000000.0);
    return t;
}

void printInfoOnSccs(const vector< vector<unsigned> >& sccs)
{
    unsigned maxDisplaySize = 10;
    vector<unsigned> stats(maxDisplaySize, 0);              // for 0<k<maxDisplaySize, stats[k] holds #SCCs of size k; and stats[0] holds #SCCs of size >= maxDisplaySize
    unsigned largeSccsTotalSize = 0;

    for (unsigned i=0; i<sccs.size(); ++i)
    {
        unsigned pos = (sccs[i].size() >= maxDisplaySize) ? 0 : sccs[i].size();
        stats[pos]++;
        if (pos==0) largeSccsTotalSize+= sccs[i].size();
    }
    printf("  have %d SCCs total, of which ", (unsigned) sccs.size());
    for (unsigned pos=1; pos < maxDisplaySize; pos++)
        printf("%u of size %u, ", stats[pos], pos);
    printf("%u of size >=%u (and total size %u)\n", stats[0], maxDisplaySize, largeSccsTotalSize);
}


void printAllSccs(const vector<vector<unsigned> >& sccs)
{
    for (unsigned i=0; i<sccs.size(); ++i)
    {
        assert(sccs[i].size() > 0);
        printf("%5d : ", sccs[i][0]);
        for (unsigned j=1; j<sccs[i].size(); ++j)
        {
            printf("%d ", sccs[i][j]);
        }
        printf("\n");
    }
}


void reduce_bin_clauses(const vector< vector <int> >& originalClauses, vector< vector<int> >& reducedClauses, bool equivsOnly)
{
    printf(" I AM IN REDUCE_BIN_CLAUSES\n");
    reducedClauses.clear();
    vector<int> binClause(2);

    double tt = getCurrentTime();

    // =========================================================================================================
    printf("Constructing original graph\n");

    // Check that the input is valid and find the maximum element that appears
    unsigned maxVariable = 0;
    for (unsigned i=0; i<originalClauses.size(); ++i) {
        assert(originalClauses[i].size()==2);
        assert(originalClauses[i][0]<0);
        assert(originalClauses[i][1]>0);
        assert(abs(originalClauses[i][0])!=abs(originalClauses[i][1]));
        maxVariable = std::max(maxVariable, (unsigned) abs(originalClauses[i][0]));
        maxVariable = std::max(maxVariable, (unsigned) abs(originalClauses[i][1]));
    }

    // Add edges
    Graph currentGraph(maxVariable+1);
    for (unsigned i=0; i<originalClauses.size(); ++i) {
        currentGraph.addEdge(abs(originalClauses[i][0]), abs(originalClauses[i][1]));
    }
    //currentGraph.print();
    printf("  --contains %u variables and %u edges\n", currentGraph.getNumVertices(), currentGraph.getNumEdges());
    printf("  --completed in %1.2f sec\n", getCurrentTime() - tt);

    // =========================================================================================================
    printf("Computing SCCs\n");
    tt = getCurrentTime();
    SccFinder sccFinder(&currentGraph);
    sccFinder.findSccs();
    // Note: sccs are topologically sorted!
    vector< vector< unsigned> > sccs = sccFinder.getSccs();
    printInfoOnSccs(sccs);
    printf("  --completed in %1.2f sec\n", getCurrentTime() - tt);

    // =========================================================================================================
    printf("Shrinking based on SCCs\n");
    tt = getCurrentTime();

    // for each SCC, record binary clauses
    for (unsigned i=0; i<sccs.size(); ++i) {
        unsigned n = sccs[i].size();
        if ( n == 1) continue;
        for (unsigned j=0; j<sccs[i].size(); ++j) {
            binClause[0] = -(int) sccs[i][j];
            binClause[1] =  (int) sccs[i][(j+1) % n];

            //printf("Adding equiv-implication: %u -> %u\n", sccs[i][j], sccs[i][(j+1) % n]);

            reducedClauses.push_back(binClause);
        }
    }
    printf("Recorded %u equivalence clauses\n", (unsigned) reducedClauses.size());

    if (equivsOnly)
    {
        return;
    }
    // In principle, we can stop here [if we only want to find equivalences]
    // But we can keep other implications as well
    // =========================================================================================================

    // for each SCC, compute its root (just take the first element)
    vector<unsigned> topoSortedSccRoots(sccs.size(), UINT_MAX);
    for (unsigned i=0; i<sccs.size(); ++i) {
        topoSortedSccRoots[i] = sccs[sccs.size() - 1 - i][0];
    }
    // also, create a map from a variable to its scc root
    vector<unsigned> mapVarToRoot(maxVariable+1, UINT_MAX);
    for (unsigned i=0; i<sccs.size(); ++i) {
        for (unsigned j=0; j<sccs[i].size(); ++j)
            mapVarToRoot[ sccs[i][j] ] = sccs[i][0];
    }

    // Create simplified information
    // -- only leave edges between the roots
    // We use the fact that the graph has all transitive edges, i.e. if removing u removes v, and removing v removes w, then removing u necessarily removes w too.
    // In particular, if {u, v} and {w, x} are SCCs with v->x an edge, then there is an edge u->w as well.
    for (unsigned u=0; u<= maxVariable; ++u)
    {
        if (u != mapVarToRoot[u]) {
            currentGraph.removeAllEdges(u);
            continue;
        }
        vector<unsigned> children = currentGraph.getChildren(u);
        currentGraph.removeAllEdges(u);
        for (unsigned i=0; i<children.size(); ++i) {
            unsigned v = children[i];
            if (v != mapVarToRoot[v])
                continue;
            currentGraph.addEdge(u, v);
        }
    }
    printf("  scc-reduced graph contains %d edges\n", currentGraph.getNumEdges());
    printf("  --completed in %1.2f sec\n", getCurrentTime() - tt);


    printf("Performing transitive reduction\n");
    tt = getCurrentTime();

    // Here we further reduce the simplified graph above by removing all transitive edges.
    // We use two facts:
    //  (1) By construction, the graph already contains all transitive edges
    //  (2) After Tarjan's algorithm, the sccs are topologically sorted
    // Hence, for each node (ordered from topmost to bottommost),
    // we leave its children who are not also its grandchildren.

    vector<unsigned> children;
    vector<unsigned> newgrandchildren, grandchildren;
    vector<bool> grandchildrenMask(maxVariable+1, false);

    unsigned numTransitiveImplicationsRemoved=0;
    for (unsigned i=0; i < topoSortedSccRoots.size(); ++i)
    {
        unsigned var = topoSortedSccRoots[i];

        // collect grandchildren of var
        children = currentGraph.getChildren(var);
        for (unsigned j=0; j<children.size(); ++j)
        {
            unsigned childvar = children[j];
            newgrandchildren = currentGraph.getChildren(childvar);

            for (unsigned k=0; k<newgrandchildren.size(); ++k)
            {
                unsigned grandchildvar = newgrandchildren[k];
                if (!grandchildrenMask[grandchildvar])
                {
                    grandchildren.push_back(grandchildvar);
                    grandchildrenMask[grandchildvar] = true;
                }
            }

        }

        // now examine the children again
        currentGraph.removeAllEdges(var);

        for (unsigned j=0; j<children.size(); ++j)
        {
            unsigned childvar = children[j];
            if (!grandchildrenMask[childvar])
                currentGraph.addEdge(var, childvar);
            else
                numTransitiveImplicationsRemoved++;
        }

        // clear grandchildren info
        for (unsigned j=0; j<grandchildren.size(); ++j)
        {
            unsigned grandchildId = grandchildren[j];
            grandchildrenMask[grandchildId] = false;
        }
        grandchildren.clear();
    }
    printf("  reduced graph contains %d edges (%d transitive edges removed)\n", currentGraph.getNumEdges(), numTransitiveImplicationsRemoved);
    printf("  --completed in %1.2f sec\n", getCurrentTime() - tt);

    // Finally, extract remaining edges and add them to reducedClauses
    for (unsigned u=0; u<currentGraph.getNumVertices(); ++u)
    {
        const vector<unsigned>& children = currentGraph.getChildren(u);
        for (unsigned i=0; i<children.size(); ++i)
        {
            unsigned v = children[i];
            //printf("Adding transitive-implication: %u -> %u\n", u, v);

            binClause[0] = -(int)u;
            binClause[1] =  (int)v;
            assert(u!=0);
            assert(v!=0);
            assert(u!=v);
            reducedClauses.push_back(binClause);
        }
    }
    printf("Recorded %u total clauses\n", (unsigned) reducedClauses.size());
}

