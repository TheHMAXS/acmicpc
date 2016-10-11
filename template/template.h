#pragma comment(linker, "/STACK:32000000")
#include <bits/stdc++.h>
#define REP(i, n) for (int i = 0, _= (n); i < _; ++i)
#define DWN(i, n) for (int i = (n) - 1; i >= 0; --i)
#define FOR(i, l, r) for (int i = (l), _ = (r); i < _; ++i)
#define EDGE(u, v, e) for (int e = head[u], v; e != nil && (v = to[e], true); e = next[e])

using namespace std;

typedef long long int64;
typedef unsigned long long uint64;
typedef complex<double> comp;

inline bool read(int& val) { return scanf("%d", &val) != -1;}
inline bool read(int64& val) { return scanf("%I64d", &val) != -1;}
inline bool read(double& val) { return scanf("%lf", &val) != -1;}
inline bool read(char* val) { return scanf("%s", val) != -1;}
template<class T1, class T2>
inline bool read(T1& a, T2& b)
{ return read(a) && read(b); }
template<class T1, class T2, class T3>
inline bool read(T1& a, T2& b, T3& c)
{ return read(a) && read(b) && read(c); }
template<class T1, class T2, class T3, class T4>
inline bool read(T1& a, T2& b, T3& c, T4& d)
{ return read(a) && read(b) && read(c) && read(d); }
template<class T1, class T2, class T3, class T4, class T5>
inline bool read(T1& a, T2& b, T3& c, T4& d, T5& e)
{ return read(a) && read(b) && read(c) && read(d) && read(e); }

const double eps = 1e-9;
const double pi = acos(-1.0);
const int inf = 0x0FFFFFFF;
const int nil = -1;

const int N = 111111;
const int M = 1111;
int64 mod = 1000000007;
