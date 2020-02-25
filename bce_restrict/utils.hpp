#ifndef __BCE_UTILS__
#define __BCE_UTILS__

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
#include <sstream>

using namespace std;


bool stringEndsWith(std::string const & value, std::string const & ending)
{
    if (ending.size() > value.size()) return false;
    return std::equal(ending.rbegin(), ending.rend(), value.rbegin());
}

//-------------------------------------------------------------------------------------------------
// File reading functionality is adapted from Minisat
//-------------------------------------------------------------------------------------------------

//-------------------------------------------------------------------------------------------------
// A simple buffered character stream class:
static const int buffer_size = 1048576;

class InStreamBuffer {
    gzFile        in;
    unsigned char buf[buffer_size];
    int           pos;
    int           size;

    void assureLookahead() {
        if (pos >= size) {
            pos  = 0;
            size = gzread(in, buf, sizeof(buf)); } }

public:
    explicit InStreamBuffer(const char *filename) : pos(0), size(0)
    {
        open(filename);
        assureLookahead();
    }

    void open(const char *filename)
    {
        //cout << "Reading file: " << filename << endl;
        in = gzopen(filename, "rb");

        if (in == NULL)
        {
            fprintf(stderr, "  --error: could not open\n");
            exit(1);
        }
    }

    void close()
    {
        if (in != Z_NULL)
        {
            gzclose(in);
            in = Z_NULL;
        }
    }

    ~InStreamBuffer()
    {
        close();
    }

    int  operator *  () const { return (pos >= size) ? EOF : buf[pos]; }
    void operator ++ ()       { pos++; assureLookahead(); }
    int  position    () const { return pos; }
};


//-------------------------------------------------------------------------------------------------
// End-of-file detection functions for InStreamBuffer and char*:

static inline bool isEof(InStreamBuffer& in) { return *in == EOF;  }
static inline bool isEof(const char*   in) { return *in == '\0'; }


//-------------------------------------------------------------------------------------------------
// Generic parse functions parametrized over the input-stream type.

template<class B>
static void skipWhitespace(B& in) {
    while ((*in >= 9 && *in <= 13) || *in == 32)
        ++in; }


template<class B>
static void skipLine(B& in) {
    for (;;){
        if (isEof(in)) return;
        if (*in == '\n') { ++in; return; }
        ++in; } }


template<class B>
static int parseInt(B& in) {
    int     val = 0;
    bool    neg = false;
    skipWhitespace(in);
    if      (*in == '-') neg = true, ++in;
    else if (*in == '+') ++in;
    if (*in < '0' || *in > '9') fprintf(stderr, "PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
    while (*in >= '0' && *in <= '9')
        val = val*10 + (*in - '0'),
        ++in;
    return neg ? -val : val; }

// String matching: in case of a match the input iterator will be advanced the corresponding
// number of characters.
template<class B>
static bool match(B& in, const char* str) {
    int i;
    for (i = 0; str[i] != '\0'; i++)
        if (in[i] != str[i])
            return false;

    in += i;

    return true;
}

// String matching: consumes characters eagerly, but does not require random access iterator.
template<class B>
static bool eagerMatch(B& in, const char* str) {
    for (; *str != '\0'; ++str, ++in)
        if (*str != *in)
            return false;
    return true; }

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


//-------------------------------------------------------------------------------------------------
// File writing functionality
//-------------------------------------------------------------------------------------------------

class OutStreamBuffer {
    bool          gzip;
	gzFile        out;
    FILE          *out2;

public:
    explicit OutStreamBuffer() : gzip(false), out(Z_NULL), out2(NULL) {}

	explicit OutStreamBuffer(const char* filename) : out(Z_NULL), out2(NULL)
	{
        open(filename);
	}

	~OutStreamBuffer()
	{
        close();
	}

	void open(const char* filename)
	{
        if (stringEndsWith(filename, ".gz"))
        {
            out = gzopen(filename, "wb");
            if (out == NULL)
            {
                fprintf(stderr, "  --error: could not open\n");
                exit(1);
            }
        }
        else
        {
            out2 = fopen(filename, "wb");
            if (out2 == NULL)
            {
                fprintf(stderr, "  --error: could not open\n");
                exit(1);
            }
        }
	}

    void close()
    {
        if (out != Z_NULL)
        {
            gzclose(out);
            out = Z_NULL;
        }

        if (out2 != NULL)
        {
            fclose(out2);
            out2 = NULL;
        }
    }

	OutStreamBuffer& operator<< (const char* buf)
	{
        if (out != Z_NULL)
        {
            gzwrite(out, buf, strlen(buf));
        }
        else
        {
            fprintf(out2, "%s", buf);
        }
        return *this;
	}

	OutStreamBuffer& operator<< (const string& str)
	{
        if (out != Z_NULL)
        {
            gzwrite(out, str.c_str(), str.size());
        }
        else
        {
            fprintf(out2, "%s", str.c_str());
        }
		return *this;
	}

	OutStreamBuffer& operator<< (int n)
	{
        stringstream s;
        s << n;
		const string str = s.str();
        if (out != Z_NULL)
        {
            gzwrite(out, str.c_str(), str.size());
        }
        else
        {
            fprintf(out2, "%s", str.c_str());
        }
		return *this;
	}
};


template<class B>
static bool writeHeader(B& out, unsigned num_vars, unsigned &num_clauses, unsigned num_groups)
{
    out << "p gcnf " << num_vars << " " << num_clauses << " " << num_groups << "\n";
}

template<class B>
static void writeGroupClause(B& out, unsigned group, const vector<int>& lits)
{
    out << "{" << group << "} ";
    for (unsigned i=0; i<lits.size(); ++i)
        out << lits[i] << " ";
    out << "0\n";
}


template<class B>
static void writeGroupNecessity(B& out, unsigned group)
{
    out << "c restrict " << (int)group << " 0\n";
}

template<class B>
static void writeGroupRestriction(B& out, const vector<int>& restriction)
{
    out << "c restrict ";
    for (unsigned i=0; i<restriction.size(); ++i)
        out << restriction[i] << " ";
    out << " 0\n";
}


#endif
