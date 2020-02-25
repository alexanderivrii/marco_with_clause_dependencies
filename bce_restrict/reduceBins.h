#ifndef REDUCE_BINS_H
#define REDUCE_BINS_H

#include "assert.h"
#include <climits>
#include <vector>
#include <algorithm>
using std::vector;

// MAIN FUNCTION:
// This is a somwhat clumsy functionality to reduce the set of binary implication clauses (discovered by lve_restrict or bce_restrict algorithms).
// Each clause is necessarily of the form (-a, b), with a>0 and b>0, and we can think of this as a directed edge from "a" to "b".
// Furthermore, the way these clauses are currently produced, they contain the full transitive closure (i.e. whenever a->b and b->c are edges in the graph,
// then also a->c is an edge).
// We heavily exploit the above fact in the reduction.

void reduce_bin_clauses(const vector< vector <int> >& originalClauses, vector< vector<int> >& reducedClauses, bool equivsOnly);


// Graph
class Graph
{
    unsigned mNumVertices, mNumEdges;
    vector< vector<unsigned> > mEdges;
public:
    Graph(unsigned numVertices) : mNumVertices(numVertices), mNumEdges(0) {
        mEdges.resize(mNumVertices);
    }

    void addEdge(unsigned u, unsigned v) {
        assert(u < mNumVertices);
        assert(v < mNumVertices);
        mEdges[u].push_back(v);
        mNumEdges++;
    }

    // Removes all edges of a node
    void removeAllEdges(unsigned u) {
        assert(u < mNumVertices);
        mNumEdges -= mEdges[u].size();
        mEdges[u].clear();
    }

    const vector<unsigned>& getChildren(unsigned u) const {
        assert(u < mNumVertices);
        return mEdges[u];
    }

    unsigned getNumVertices() const {
        return mNumVertices;
    }

    unsigned getNumEdges() const {
        return mNumEdges;
    }

    bool containsEdge(unsigned u, unsigned v) const {
        assert(u < mNumVertices);
        assert(v < mNumVertices);
        for (unsigned i=0; i<mEdges[u].size(); ++i) {
            if (mEdges[u][i] == v) {
                return true;
            }
        }
        return false;
    }

    void print() {
        for (unsigned i=0; i<mEdges.size(); ++i) {
            if (mEdges[i].size() != 0) {
                printf("%d -> ", i);
                for (unsigned j=0; j<mEdges[i].size(); ++j)
                    printf("%d ", mEdges[i][j]);
                printf("\n");
            }
        }
    }
};

// Strongly connected components - Tarjan's algorithm
class SccFinder
{
    Graph *mGraph;
    unsigned mNumVertices;
    vector<unsigned> mIndex;
    vector<unsigned> mLowlink;
    vector<unsigned> mStack;
    vector<bool> mOnStack;
    unsigned mTime;
    unsigned mVerbosity;

    vector < vector<unsigned> > mSccs;
public:
    SccFinder(Graph *graph, unsigned verbosity=0) : mGraph(graph), mNumVertices(0), mVerbosity(verbosity) {
        assert(mGraph);
        mNumVertices = mGraph->getNumVertices();
        mIndex.resize(mNumVertices, 0);
        mLowlink.resize(mNumVertices, 0);
        mOnStack.resize(mNumVertices, false);
        mTime = 1;
    }

    void printScc(const vector<unsigned>& scc, unsigned idx) {
        if (mVerbosity) {
            printf("%4d: scc (%d): ", idx, (unsigned) scc.size());
            for (unsigned i=0; i<scc.size(); ++i)
                printf("%d ", scc[i]);
            printf("\n");
        }
    }

    const vector < vector<unsigned> >& getSccs() {
        return mSccs;
    }

    void strongConnect(unsigned v) {
        mIndex[v] = mTime;
        mLowlink[v] = mTime;
        mTime++;

        mStack.push_back(v);
        mOnStack[v] = true;

        const vector<unsigned>& ch = mGraph->getChildren(v);

        for (unsigned i=0; i<ch.size(); ++i) {
            unsigned w = ch[i];

            if (mIndex[w]==0) {
                strongConnect(w);
                mLowlink[v] = std::min(mLowlink[v], mLowlink[w]);
            }
            else if (mOnStack[w]) {
                mLowlink[v] = std::min(mLowlink[v], mIndex[w]);
            }
        }

        if (mLowlink[v] == mIndex[v]) {
            vector<unsigned> newScc;
            unsigned w = UINT_MAX;
            while (v != w) {
                w = mStack.back();
                mStack.pop_back();

                mOnStack[w] = false;
                newScc.push_back(w);
            }
            if (mVerbosity>0) {
                printScc(newScc, mSccs.size());
            }
            mSccs.push_back(newScc);
        }
    }

    void findSccs() {
        for (unsigned v=0; v < mNumVertices; ++v) {
            assert(mStack.empty());
            if (mIndex[v] == 0) {
                strongConnect(v);
            }
        }
    }
};



#endif
