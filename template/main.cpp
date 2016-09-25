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
const int root = nil + 1;

const int N = 111111;
const int M = 1111;
int64 mod = 1000000007;

struct add_t {
    int val = 0;
    add_t(int val = -1): val(val) {}
    void operator+=(add_t a) { if (a.val != -1) val = a.val; }
};
struct sum_t {
    int len, cnt, l, r;
    sum_t(): len(0), cnt(0), l(nil), r(nil) {}
    sum_t(int len, int val = 0): len(len), cnt(1), l(val), r(val) {}
    void rev() { swap(l, r); }
    void operator+=(add_t a) {
        if (cnt != 0 && a.val != -1) { cnt = 1; l = r = a.val; }
    }
    void operator+=(sum_t b) {
        if (cnt == 0) *this = b;
        else if (b.cnt != 0) {
            len += b.len; cnt = cnt + b.cnt - (r == b.l); r = b.r;
        }
    }
};

struct segment_tree
{
    struct node {
        int l, r, Ls, Rs;
        add_t a; sum_t s;
        node(int l = 0, int r = 0): l(l), r(r), Ls(nil), Rs(nil), a(), s(r - l + 1) {}
        void add(add_t val) { a += val; s += val; }
    } X[4 * N];
    int id;

    int next(int l, int r) { X[id] = node(l, r); return id++; }
    int copy(int i) { return i; int j = id++; X[j] = X[i]; return j; }
    void down(node& x) {
        int m = (x.l + x.r) >> 1;
        X[x.Ls = x.Ls == nil ? next(x.l, m)     : copy(x.Ls)].add(x.a);
        X[x.Rs = x.Rs == nil ? next(m + 1, x.r) : copy(x.Rs)].add(x.a);
        x.a = add_t();
    }
    void up(node& x) { x.s = X[x.Ls].s; x.s += X[x.Rs].s; }

    void init_one(int i, int l, int r) {
    	id = i; next(l, r);
    }
    void init_all(int i, int l, int r, add_t val[]) {
        init_one(i, l, r); //ret == i
        if (l < r) {
            int m = (l + r) >> 1;
            init_all(X[i].Ls = id, l, m, val);
            init_all(X[i].Rs = id, m + 1, r, val);
            up(X[i]);
        } else {
        	if (val) X[i].add(val[l]);
        }
    }

    void add(node& x, int l, int r, add_t a) {
        if (l <= x.l && x.r <= r) {
            x.add(a);
        } else {
            down(x);
            if (l <= X[x.Ls].r) add(X[x.Ls], l, r, a);
            if (r >= X[x.Rs].l) add(X[x.Rs], l, r, a);
            up(x);
        }
    }
    sum_t sum(node& x, int l, int r) {
        if (l <= x.l && x.r <= r) {
            return x.s;
        } else {
        	sum_t ret;
        	if (x.Ls == nil) {
        		ret = sum_t(min(r, x.r) - max(l, x.l) + 1);
        	} else {
    			if (l <= X[x.Ls].r) ret += sum(X[x.Ls], l, r);
    			if (r >= X[x.Rs].l) ret += sum(X[x.Rs], l, r);
    		}
        	ret += x.a;
        	return ret;
        }
    }
    //t must be root;
    int add(int t, int l, int r, add_t a) { add(X[t = copy(t)], l, r, a); return t; }
    sum_t sum(int t, int l, int r) { return sum(X[t], l, r); }
} segment;

struct tree
{
    int n;
    int head[N];

    int id;
    int to[N];
    int next[N];
    int cost[N];
    void init(int n) {
        id = root;
        this->n = n;
        REP (i, n) head[i] = nil;
    }
    void add1(int u, int v, int val) {
        to[id] = v;
        cost[id] = val;
        next[id] = head[u];
        head[u] = id++;
    }
    void add2(int u, int v, int val) {
        add1(u, v, val); add1(v, u, val);
    }

    //chain_partition
    int val[N], parent[N], deep[N], size[N], heavy[N];
    void heavydfs(int u, int p) {
        parent[u] = p; deep[u] = p == nil ? 0 : deep[p] + 1;
        size[u] = 1; heavy[u] = nil;
        EDGE (u, v, e) if (v != p) {
            val[v] = cost[e];
            heavydfs(v, u);
            size[u] += size[v];
            if (heavy[u] == nil || size[heavy[u]] < size[v])
                heavy[u] = v;
        }
    }
    int top[N], rank[N], rid;
    void chaindfs(int t) {
        for (int u = t; u != nil; u = heavy[u]) {
            top[u] = t; rank[u] = --rid;
        }
        for (int u = t; u != nil; u = heavy[u]) {
            EDGE (u, v, e) if (v != parent[u] && v != heavy[u]) chaindfs(v);
        }
    }
    add_t val_rank[N];
    void initchain(int i, int u = 0) {
        heavydfs(u, nil); rid = n; chaindfs(u);
        REP (v, n) val_rank[rank[v]] = val[v];
        segment.init_all(i, 0, n - 1, val_rank);
    }
    int add(int i, int u, int v, add_t a) {
        int tu = top[u], tv = top[v];
        while (tu != tv) {
            if (deep[tu] < deep[tv]) { swap(u, v); swap(tu, tv); }
            segment.add(i, rank[u], rank[tu], a);
            u = parent[tu]; tu = top[u];
        }
        if (u != v) {
            if (deep[u] < deep[v]) { swap(u, v); }
            segment.add(i, rank[u], rank[heavy[v]], a);
        }
        return i;
    }
    sum_t sum(int i, int u, int v) {
        sum_t sum[2]; bool d = false;
        int tu = top[u], tv = top[v];
        while (tu != tv) {
            if (deep[tu] < deep[tv]) { swap(u, v); swap(tu, tv); d = !d; }
            sum[d] += segment.sum(i, rank[u], rank[tu]);
            u = parent[tu]; tu = top[u];
        }
        if (u != v) {
            if (deep[u] < deep[v]) { swap(u, v); d = !d;  }
            sum[d] += segment.sum(i, rank[u], rank[heavy[v]]);
        }
        sum[1].rev(); sum[0] += sum[1];
        return sum[0];
    }
} g;

int main()
{
    int n, m; while(read(n, m)) {
        g.init(n);
        REP (i, n - 1) {
            int a, b, v; read(a, b, v); a--; b--;
            g.add2(a, b, v);
        }
        int root; g.initchain(root = 0, 0);
        REP (i, m) {
            char cmd[100]; read(cmd);
            if (cmd[0] == 'Q') {
                int u, v; read(u, v); u--; v--;
                printf("%d\n", g.sum(root, u, v).cnt);
            } else {
                int u, v, a; read(u, v, a); u--; v--;
                g.add(root, u, v, a);
            }
        }
    }
    return 0;
}


