#ifndef __BCE_BCE__
#define __BCE_BCE__

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

using namespace std;

struct BceFinderOptions
{
    unsigned    mVerbosity;      // output verbosity

    unsigned    mTimeLimit;      // time-limit

    unsigned    mRestrictCap;    // caps the number of restriction clauses

    unsigned    mHandleRemoved;  // Controls what to do with clauses removable at top-level
                                 //   0 - nothing
                                 //   1 - delete them completely
                                 //   2 - relabel them as group-0

    bool        mBceSkip;        // Controls whether to skip top-level BCE
                                 //   0 - don't
                                 //   1 - do

    bool        mBceOnly;        // Controls whether to do only top-level BCE

    bool        mReduceImplies;  // Controls whether to reduce binary clauses
                                 //   0 - don't
                                 //   1 - do

    bool        mEqOnly;        // Controls whether to keep only equivalences
                                 //   0 - no (both equivalences and transitive)
                                 //   1 - yes

    bool        mUseForced;      // Controls whether to look for necessary groups

    const char* mOutputName;     // Name of the output file
                                 //   NULL if not specified

    BceFinderOptions()
    {
        mVerbosity = 0;
        mTimeLimit = 3600;
        mRestrictCap = 1000000;
        mHandleRemoved = 0;
        mBceSkip = false;
        mBceOnly = false;
        mReduceImplies = true;
        mEqOnly = false;
        mUseForced = true;
        mOutputName = NULL;
    }
};

class BceFinder
{
    BceFinderOptions             mOpts;                  // Options
    const char*                  mFilename;              // Filename
    unsigned                     mMaxVar;

    vector < vector <int> >      mClauses;               // all clauses
    vector < bool >              mClauseIsEnabled;       // clause -> enabled
    vector < unsigned >          mContainingGroup;       // clause -> corresponding group
    unsigned                     mClauseEnabledCnt;      // number of enabled clauses

    vector < vector <unsigned> > mGroups;                // group -> its clauses
    vector <unsigned>            mGroupEnabledCnt;       // group -> number enabled clauses

    vector < bool >              mGroupIsNecessary;      // group -> necessary
    vector < bool >              mGroupIsRemoved;        // group -> removed
    vector <unsigned>            mNecessaryGroups;       // necessary groups as a vector
    vector <unsigned>            mRemovedGroups;         // removed groups as a vector

    vector < vector <unsigned> > mOccsPos, mOccsNeg;     // occurrence lists
    vector<bool>                 mTouched;               // touched lits
    vector<int>                  mTouchedLits;           // touched lits

    vector<unsigned>             mNewDisabledClauses;    // ids of clauses disabled by latest BCE
    vector<unsigned>             mNewDisabledGroups;     // ids of groups disabled by latest BCE

    bool                         mOutOfTime;             // becomes true when out of time
    double                       mTimer;

    vector < vector<int> >       mRestrictionClauses;

public:
    BceFinder(const char *filename, const BceFinderOptions& opts);
    ~BceFinder();

    void run();

private:
    template <class B> void readRGCNF(B& in);                              // Reads [Group] CNF [with Restrictions]
    template <class B> void writeRGCNF(B& out);                            // Writes [Group] CNF [with Restrictions]

    bool checkInternalDatabaseIsOk() const;

    void addClause           (unsigned groupId, const vector<int>& clause);
    void addGroupRestriction (const vector<int>& restriction);

    void markGroupAsNecessary(unsigned groupId);
    void markGroupAsRemoved  (unsigned groupId);
    bool isGroupNecessary    (unsigned groupId);
    bool isGroupRemoved      (unsigned groupId);
    void mergeGroups         (unsigned firstGroupId, unsigned secondGroupId);

    void printClause(const vector<int>& c);
    void printAllClauses();
    void printAllGroups();
    void printInfoOnGroups();
    void printAll();

    unsigned lit2index(int lit) const;
    void touchLit(int lit);
    void untouchLit(int lit);
    void touchLitsInClauseNegation(const vector<int>& c);
    void untouchAllLits();
    bool isResolutionTautological(const vector<int> &c, const vector<int>& d, int lit);
    bool doBce();
    bool checkAllLitsUntouched() const;

    double timeElapsed();
    bool   outOfTime();
};

#endif
