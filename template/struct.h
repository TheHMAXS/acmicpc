#include <algorithm>
using namespace std;
#define REP(i, n) for (int i = 0, _= (n); i < _; ++i)
#define DWN(i, n) for (int i = (n) - 1; i >= 0; --i)
#define FOR(i, l, r) for (int i = (l), _ = (r); i < _; ++i)
#define EDGE(u, v, e) for (int e = head[u], v; e != nil && (v = to[e], true); e = next[e])
const int N = 1111111;

struct rmq
{
	int st[20][N];
	int n;
	void init(int val[], int n) {
		this->n = n;
		REP (i, n) st[0][i] = val[i];
		REP (lg, 19) REP (i, n) {
			int len = 1 << lg;
			if (i + len < n)
				st[lg + 1][i] = min(st[lg][i], st[lg][i + len]);
			else
				st[lg + 1][i] = st[lg][i];
		}
	}
	int query(int l, int r) {
		int len = r - l + 1;
		int lg = 31 - __builtin_clz(len);
		len = 1 << lg;
		return min(st[lg][l], st[lg][r - len + 1]);
	}
};

struct rmqid
{
	int st[M][N], log2[N]; int n;
	void init(const int val[N], int n) {
		this->n = n; log2[0] = 0x0FFFFFFF;
		REP (j, n) st[0][j] = val[j]; log2[1] = 0;
		for (int i = 0, k = 1 << i; (k << 1) <= n; i++, k <<= 1) {
			REP (j, n) st[i + 1][j] = st[i][j];
			REP (j, n - k) st[i + 1][j] = min(st[i + 1][j], st[i][j + k]);
			FOR (j, k, k << 1) log2[j] = i;
		}
	}
	//[l, r]
	int query(int l, int r) {
		r++; int i = log2[r - l], k = 1 << i;
		return min(st[i][l], st[i][r - k]);
	}

	int stid[30][N];
	void initid(int n) {
		REP (j, n) stid[0][j] = j;
		for (int i = 0, k = 1 << i; (k << 1) <= n; i++, k <<= 1) {
			REP (j, n) stid[i + 1][j] = stid[i][j];
			REP (j, n - k) if (st[i][j + k] < st[i + 1][j])
				stid[i + 1][j] = stid[i][j + k];
		}
	}
	int queryid(int l, int r) { //initid()
		r++; int i = log2[r - l], k = 1 << i;
		return st[i][l] < st[i][r - k] ? stid[i][l] : stid[i][r - k];
	}
};

struct merge_set
{
	int P[N], C[N];
	void init(int n) { REP (i, n) P[i] = i, C[i] = 1; }
	int find(int a) {
		int p = a;
		while (p != P[p]) p = P[p];
		for (int pa = P[a]; pa != p; a = pa, pa = P[a]) P[a] = p;
		return p;
	}
	int merge(int a, int b) {
		if (a == b || a != P[a] || b != P[b]) return -1;
		if (C[a] < C[b]) swap(a, b);
		P[b] = a; C[a] += C[b]; C[b] = 0;
		return a;
	}
};

//A add  S sum  C count  L left  R right  M middle  LS left sub node  RS right sub node
// tree_array [1, n]
//segtree [0, n) [l, r) [l, m) [m, r)
struct tree_array //[1, n]
{
	typedef int type;
	type S[N], n;
	void clear(int n) {
		this->n = n;
		REP (i, n) S[i] = type();
	}
	void add(int i, type a) {
		for (;i <= n; i += i & (-i)) S[i] += a;
	}
	type sum(int i) {
		type a = type();
		for (; i > 0; i -= i & (-i)) a += S[i];
		return a;
	}
	type sum(int l, int r) { return sum(r) - sum(l - 1); }
	type get(int i) { return sum(i) - sum(i - 1); }
	void set(int i, type a) { add(i, a - get(i)); }
};

struct tree_array2
{
	typedef int type;
	type S[N][N]; int n; int m;
	void init(int n, int m) {
		this->n = n; this->m = m;
		REP (i, n) REP (j, m) S[i][j] = type();
	}
	void add(int i, int j, type a) {
		for (int x = i; x <= n; x += x & (-x))
			for (int y = j; y <= m; y += y & (-y))
				S[x][y] += a;
	}
	type sum(int i, int j) {
		type a = type();
		for (int x = i; x > 0; x -= x & (-x))
			for (int y = j; y > 0; y -= y & (-y))
				a += S[x][y];
		return a;
	}
	type sum(int i1, int j1, int i2, int j2) {
		i1--, j1--;
		return sum(i2, j2) + sum(i1, j1) - sum(i1, j2) - sum(i2, j1);
	}
	type get(int i, int j) { return sum(i, j, i, j); }
	void set(int i, int j, type x) { add(i, j, x - get(i, j)); }
};

struct add_t {
	int add; bool rev;
	add_t(int add = 0, bool rev = false): add(add), rev(rev) {}
	void operator+=(add_t a) { add += a.add; rev ^= a.rev; }
};
struct sum_t {
	int len, sum, max;
	sum_t(): len(0), sum(0), max(-inf) {}
	sum_t(int len, int val = 0): len(len), sum(len * val), max(val) {}
	void operator+=(add_t a) {
		sum += a.add * len; max += a.add;
	}
	void operator+=(sum_t b) {
		len += b.len; sum += b.sum; max = std::max(max, b.max);
	}
};
struct color_add {
    int val = 0;
    color_add(int val = -1): val(val) {}
    void operator+=(color_add a) { if (a.val != -1) val = a.val; }
};
struct color_sum {
    int len, cnt, l, r;
    color_sum(): len(0), cnt(0), l(nil), r(nil) {}
    color_sum(int len, int val = 0): len(len), cnt(1), l(val), r(val) {}
    void rev() { swap(l, r); }
    void operator+=(color_add a) {
        if (cnt != 0 && a.val != -1) { cnt = 1; l = r = a.val; }
    }
    void operator+=(color_sum b) {
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
    } X[2 * N];
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
    int add(int t, int l, int r, add_t a) {
    	add(X[t = copy(t)], l, r, a); return t;
    }
    sum_t sum(int t, int l, int r) { return sum(X[t], l, r); }
} segment;

struct splay_tree
{
	struct node {
		int p; int sub[2]; add_t a; sum_t s; sum_t v;
		node(): p(nil), a(), s(1), v(1) { sub[0] = sub[1] = nil; }
		void add(add_t val) {
			if (val.rev) swap(sub[0], sub[1]);
			a += val; s += val; v += val;
		}
	} X[4 * N];
	int id = 0;

	int next()  { X[id] = node(); return id++; }
	int key(node& x) { return x.sub[0] == nil ? 0 : X[x.sub[0]].s.len; }
	void down(node& x) {
		REP (d, 2) if (x.sub[d] != nil) X[x.sub[d]].add(x.a); x.a = add_t();
	}
	void up(node& x) {
		x.s = x.v; REP (d, 2) if (x.sub[d] != nil) x.s += X[x.sub[d]].s;
	}

	int setsub(int i, bool d, int j) {
		int r = X[i].sub[d];
		if (r != nil) X[r].p = nil;
		if (j != nil) X[j].p = i;
		X[i].sub[d] = j; up(X[i]);
		return r;
	}
	void rotate(int i, bool d) {
		int p = X[i].p;
		int j = X[i].sub[d];
		int k = X[j].sub[d ^ 1];
		X[k].p = i; X[i].sub[d] = k;
		X[i].p = j; X[j].sub[d ^ 1] = i;
		X[j].p = p; if (p != nil) X[p].sub[X[p].sub[1] == i] = j;
		up(X[i]); up(X[j]);
	}
	void splay(int i) {
		down(X[i]);
		while (X[i].p != nil) {
			int j = X[i].p;
			bool dj = X[j].sub[1] == i;
			if (X[j].p == nil) rotate(j, dj);
			else {
				int k = X[j].p;
				bool dk = X[k].sub[1] == j;
				if (dk == dj) rotate(k, dk), rotate(j, dj);
				else          rotate(j, dj), rotate(k, dk);
			}
		}
	}

	int init(int i) { id = i; return nil; }
	//t must be root; i can be node; t can be nil
	bool find(int& t, int index) { //index should be unique
		for (int i = t; i != nil; ) {
			int mid = key(X[i]);
			if (mid == index) {
				splay(t = i);
				return true;
			} else {
				down(X[i]);
				i = X[i].sub[mid < index];
				if (mid < index) index -= mid + 1;
			}
		}
		return false;
	}
	//ex = true : t = (-inf, index] return (index, +inf)
	//ex = false: t = (-inf, index) return [index, +inf)
	int splitr(int& t, int index, bool ex) {
		if (t == nil) return nil;
		int mid = key(X[t]);
		bool d = mid < index || (ex && mid == index);
		while (X[t].sub[d] != nil) {
			down(X[t]);
			t = X[t].sub[d];
			if (d) index -= (mid + 1);
			mid = key(X[t]);
			d = mid < index || (ex && mid == index);
		}
		splay(t); int ret = setsub(t, d, nil);
		if (d == 0) swap(t, ret);
		return ret;
	}
	int splitl(int& t, int index, bool ex) {
		int ret = splitr(t, index, !ex);
		swap(ret, t); return ret;
	}
	void merge(int& t1, int& t2) { //t1 t2 can be nil
		if (t1 == nil) { t1 = t2; return; }
		if (t2 == nil) { t2 = t1; return; }
		if (X[t2].sub[0] == nil) {
			splay(t2); setsub(t2, 0, t1); t1 = t2;
		} else {
			while (X[t1].sub[1] != nil) { down(X[t1]); t1 = X[t1].sub[1]; }
			splay(t1); setsub(t1, 1, t2); t2 = t1;
		}
	}
	void add(int& t, add_t a) { if (t != nil) return X[t].add(a); }
	sum_t sum(int& t) { return t == nil ? sum_t(): X[t].s; }
} splay;

struct tree
{
    int n;
    int head[N];

    int id;
    int to[N];
    int next[N];

    void init(int n, int val[]) {
        id = 0;
        this->n = n;
        REP (i, n) head[i] = nil;
    }
    void add_(int u, int v) {
        to[id] = v;
        next[id] = head[u];
        head[u] = id++;
    }
    void add(int u, int v) {
        add_(u, v); add_(v, u);
    }

    //lca
    int deep[N], dpp[N][M];
    //u = root, p = nil
    void initlca(int u, int p) {
        deep[u] = p == nil ? 0 : deep[p] + 1;
        dpp[u][0] = p;
        REP (i, M - 1)
            dpp[u][i + 1] = dpp[u][i] == nil ? nil : dpp[dpp[u][i]][i];
        for (int e = head[u]; e != nil; e = next[e])
            if (to[e] != p) initlca(to[e], u);
    }
    int lca(int u, int v) {
    	//initlca();
        if (deep[u] < deep[v]) swap(u, v);
        int d = deep[u] - deep[v];
        REP (i, M) if (d & (1 << i)) u = dpp[u][i];
        if (u != v) {
            DWN (i, M) if (dpp[u][i] != dpp[v][i])
                u = dpp[u][i], v = dpp[v][i];
            u = dpp[u][0]; v = dpp[v][0];
        }
        return u;
    }

    //chain_partition
    int parent[N], size[N], heavy[N]; //deep
    void heavydfs(int u, int p) {
    	parent[u] = p; deep[u] = p == nil ? 0 : deep[p] + 1;
    	size[u] = 1; heavy[u] = nil;
    	EDGE (u, v, e) if (v != p) {
    		heavydfs(v, u);
    		size[u] += size[v];
    		if (heavy[u] == nil || size[heavy[u]] < size[v])
    			heavy[u] = v;
    	}
    }
    int top[N], rank[N], rid;
    void chaindfs(int t, int p) {
    	for (int u = t; u != nil; p = u, u = heavy[u]) {
    		top[u] = t; rank[u] = rid++;
    	}
    	for (int u = t; u != nil; p = u, u = heavy[u]) {
    		EDGE (u, v, e) if (v != p) chaindfs(v, u);
    	}
    }

    void initchain(int u = 0, add_t val[]) {
    	heavydfs(u, nil);
    	chaindfs(u, nil);
    	segment.init_all(0, 0, n, val);
    }
    int add(int i, int u, int v, add_t a) {
    	while (top[u] != top[v]) {
    		if (deep[top[u]] > deep[top[v]]) swap(u, v);
    		i = segment.add(i, rank[top[u]], rank[u], a);
    		u = parent[top[u]];
    	}
    	if (u != v) {
    		if (deep[u] > deep[v]) swap(u, v);
    		i = segment.add(i, rank[u], rank[heavy[v]], a);
    	}
    	return i;
    }
    sum_t sum(int i, int u, int v) {
    	sum_t ret;
    	while (top[u] != top[v]) {
    		if (deep[top[u]] > deep[top[v]]) swap(u, v);
    		ret += segment.sum(i, rank[top[u]], rank[u]);
    		u = parent[top[u]];
    	}
    	if (u != v) {
    		if (deep[u] > deep[v]) swap(u, v);
    		ret += segment.sum(i, rank[u], rank[heavy[v]]);
    	}
    	return ret;
    }


};

