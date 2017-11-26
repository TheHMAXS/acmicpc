#include "template.h"

const int nil = -1;
struct hashtable {
	static const int n = 10000007;
	typedef int node;
	int head[n]; int next[n];
	node key[n]; type val[n];
	int id = 0;
	void init() { id = 0; REP (i, n) head[i] = nil; }
	type& operator[](node x) {
		int l = x % n, i = head[l];
		while (i != nil && key[i] != x) i = next[i];
		if (i == nil) {
			next[id] = head[l]; head[l] = id;
			key[id] = x; val[id] = 1e9;
			i = id++;
		}
		return val[i];
	}
};

//copy: for functional data structure
//init: should be call for each test case
//make: create tree/node
//lock: lock() to create a functional history version

//split:
//left = false  (-inf, index) [index, inf)
//left = true   (-inf, index] (index, inf)

//merge:
//input must be two different tree and return new tree
//input tree will be invalid if copy() is not enable

//parameter i: i is a node
//parameter t:
//t is a tree, and may be changed by reference
//the old tree will be invalid if copy() is not enable

struct rmq
{
	type st[20][N];
	int n;
	void init(type val[], int n) {
		this->n = n;
		REP (i, n) st[0][i] = val[i];
		REP (lg, 19) REP (i, n) {
			int len = 1 << lg;
			st[lg + 1][i] = st[lg][i];
			if (i + len < n && st[lg][i + len] < st[lg][i])
			     st[lg + 1][i] = st[lg][i + len];
		}
	}
	int query(int l, int r) {
		int lg = 31 - __builtin_clz(r - l + 1);
		return min(st[lg][l], st[lg][r - (1 << lg) + 1]);
	}
};

struct merge_set
{
	int P[N], C[N];
	void init(int n) {
		REP (i, n) P[i] = i, C[i] = 1;
	}
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

struct merge_tree {
    int P[N], val[N];
    void init(int n) {
        REP (i, n) P[i] = i, val[i] = 0;
    }
    int stack[N], top;
    int find(int i) {
        while (P[P[i]] != P[i]) {
            stack[top++] = i;
            i = P[i];
        }
        while (top > 0) {
            int j = stack[--top];
            val[j] += val[P[j]];
            P[j] = P[i];
        }
        return P[i];
    }
    int get(int i) {
        if (find(i) == i) return val[i];
        return val[i] + val[P[i]];
    }
};

//left_heap
template<class T>
struct merge_heap
{
	struct node {
		int sub[2], deep; T val;
		node(T val = 0): deep(1), val(val) {sub[0] = sub[1] = nil; }
	} poor[N + 1], *X; int id;
	merge_heap(): X(poor + 1), id(0) {}
	void init() { id = 0; X[nil].deep = 0; }
	int make(T val) { X[id] = node(val); return id++; }
	int copy(int i) { return i; X[id] = X[i]; return id++; }
	int& Ls(int i)  { return X[i].sub[0]; }
	int& Rs(int i)  { return X[i].sub[1]; }
	int merge(int t, int t2) {
		if (t  == nil) return t2;
		if (t2 == nil) return t;
		if (X[t2].val < X[t].val) swap(t, t2);
		t = copy(t);
		Rs(t) = merge(Rs(t), t2);
		if (X[Ls(t)].deep < X[Rs(t)].deep)
			swap(Ls(t), Rs(t));
		X[t].deep = X[Rs(t)].deep + 1;
		return t;
	}
	void push(int& t, T val) { t = merge(t, make(val)); }
	void pop(int& t)         { t = merge(Ls(t), Rs(t)); }// t must not be nil
	T top(int& t)            { return X[t].val; }// t must not be nil
};

//tree_array [1, n]
struct tree_array
{
	type S[N]; int n;
	void init(int n) {
		this->n = n; RE1 (i, n) S[i] = type();
	}
	void add(int i, type a) {
		for (int x = i; x <= n; x += x & (-x)) S[x] += a;
	}
	type sum(int i) {
		type a = type();
		for (int x = i; x >  0; x -= x & (-x)) a += S[x];
		return a;
	}
	//return [0, n] of sum[1, n]
	//upper_bound - 1
	int last(type value) {
		int l = 0; type sum = type();
		for (int k = 1 << 20; k >= 1; k >>= 1) {
			if (l + k <= n && sum + S[l + k] <= value) {
				sum += S[l + k]; l += k;
			}
		}
		return l;
	}
	type sum(int l, int r)  { return sum(r) - sum(l - 1); }
	type get(int i)         { return sum(i) - sum(i - 1); }
	void set(int i, type a) { add(i, a - get(i)); }
};

struct tree_array2
{
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
		return sum(i2, j2) + sum(i1, j1)
		     - sum(i1, j2) - sum(i2, j1);
	}
	type get(int i, int j)         { return sum(i, j, i, j); }
	void set(int i, int j, type x) { add(i, j, x - get(i, j)); }
};

struct add_t {
	int add; bool rev;
	add_t(type add = 0, bool rev = false): add(add), rev(rev) {}
	bool empty() { return add == 0 && rev == false; }
	void operator+=(add_t a) { rev ^= a.rev; add += a.add; }
};
struct sum_t {
	int len, sum, max;
	sum_t(): len(0), sum(0), max(INT_MIN) {}
	sum_t(int len, type val = 0): len(len), sum(len * val), max(val) {}
	void operator+=(add_t a) { sum += a.add * len; max += a.add; }
	friend sum_t operator+(sum_t a, sum_t b) {
		sum_t ret;
		ret.len = a.len + b.len;
		ret.sum = a.sum + b.sum;
		ret.max = std::max(a.max, b.max);
		return ret;
	}
	void rev() {}
};

struct color_add {
	int val = 0; bool rev;
	color_add(int val = -1, bool rev = false): val(val), rev(rev) {}
	bool empty() { return val == -1 && rev == false; }
	void operator+=(color_add a) { rev ^= a.rev; if (a.val != -1) val = a.val;}
};
struct color_sum { //no test
	int len, cnt, l, r;
	color_sum(): len(0), cnt(0), l(-1), r(-1) {}
	color_sum(int len, type val = 0): len(len), cnt(1), l(val), r(val) {}
	void operator+=(color_add a) {
		if (a.rev) swap(l, r);
		if (cnt && a.val != -1) { cnt = 1; l = r = a.val; }
	}
	friend color_sum operator+(color_sum a, color_sum b) {
		color_sum ret;
		ret.len = a.len + b.len;
		ret.cnt = a.cnt + b.cnt - (a.cnt && b.cnt && a.r == b.l);
		ret.l = (a.cnt ? a : b).l;
		ret.r = (b.cnt ? b : a).r;
		return ret;
	}
	void rev() { swap(l, r); }
};

//add_t and sum_t should satisfy the plus exchange law
struct zkw_tree
{
	add_t add[5 * N]; sum_t sum[5 * N]; int n;
	void up(int i) { sum[i] = sum[(i << 1)] + sum[(i << 1) + 1]; }
	//[1, n]
	void init(int n, type val[]) {
		int lg = 0; while (1 << lg < n + 2) lg++;
		int m = this->n = 1 << lg;
		if (val) RE1 (i, n) sum[i + m] = sum_t(1, val[i]);
		DWN (i, n) up(i);
	}
	//[l, r]
	void update(int l, int r, add_t a) {
		l += n; r += n; l--; r++;
		while ((l ^ r) != 1) {
			if ((l & 1) == 0) { sum[l + 1] += a; add[l + 1] += a; }
			if ((r & 1) == 1) { sum[r - 1] += a; add[r - 1] += a; }
			up(l >>= 1); up(r >>= 1);
		}
		while (l > 1) up(l >>= 1);
	}
	sum_t query(int l, int r) {
		l += n; r += n; l--; r++; sum_t sl, sr;
		while ((l ^ r) != 1) {
			if ((l & 1) == 0) sl = sl + sum[l + 1];
			if ((r & 1) == 1) sr = sum[r - 1] + sr;
			sl += add[l >>= 1]; sr += add[r >>= 1];
		}
		sum_t s = sl + sr;
		while (l > 1) s += add[l >>= 1];
		return s;
	}
};

struct segment_tree
{
	struct node {
		int sub[2]; add_t add; sum_t sum;
		node(int len = 0): add(), sum(len) { sub[0] = sub[1] = nil; }
		void update(add_t a) { add += a; sum += a;}
	} X[2 * N]; int id, nid;
	int& Ls(int i) { return X[i].sub[0]; }
	int& Rs(int i) { return X[i].sub[1]; }
	void init() { id = nid = 0; }
	//[0, n)
	int make(int n) { X[id] = node(n); return id++; }
	void lock() { nid = id; } //lock all node be constant
	void copy(int& i) { if (i < nid) { X[id] = X[i]; i = id++; } }
	void up  (int  i) { X[i].sum = X[Ls(i)].sum + X[Rs(i)].sum; }
	void down(int& i) {
		int len = X[i].sum.len, m = len >> 1;
		if (Ls(i) == nil) Ls(i) = make(m);
		if (Rs(i) == nil) Rs(i) = make(len - m);
		if (!X[i].add.empty()) {
			copy(Ls(i)); X[Ls(i)].update(X[i].add);
			copy(Rs(i)); X[Rs(i)].update(X[i].add);
			X[i].add = add_t();
		}
	}
	void set(int& t, type val[]) {
		copy(t);
		int len = X[t].sum.len, m = len >> 1;
		if (X[t].sum.len == 1) X[t].sum = sum_t(1, val[0]);
		else {
			down(t);
			set(Ls(t), val);
			set(Rs(t), val + m);
			up(t);
		}
	}
	void update(int& t, int l, int r, add_t add) {
		copy(t);
		int len = X[t].sum.len, m = len >> 1;
		if (r <  0 || len - 1 <  l) return;
		if (l <= 0 && len - 1 <= r) X[t].update(add);
		else {
			down(t);
			update(Ls(t), l, r, add);
			update(Rs(t), l - m, r - m, add);
			up(t);
		}
	}
	sum_t query(int& t, int l, int r) {
		copy(t);
		int len = X[t].sum.len, m = len >> 1;
		if (r <  0 || len - 1 <  l) return sum_t();
		if (l <= 0 && len - 1 <= r) return X[t].sum;
		else {
			down(t);
			sum_t ret = query(Ls(t), l, r) +
			            query(Rs(t), l - m, r - m);
			up(t); return ret;
		}
	}
} segment;

struct treap
{
	struct node {
		int sub[2]; add_t add; sum_t sum; sum_t val; int ran; //random
		node(type val = 0):
			add(), sum(1, val), val(1, val),
			ran(rand() * 10000 + rand()) {
			sub[0] = sub[1] = nil;
		}
		void update(add_t a) {
			add += a; sum += a; val += a;
			if (a.rev) swap(sub[0], sub[1]);
		}
	} X1[N + 1], *X; int id, nid;
	int& Ls(int i) { return X[i].sub[0]; }
	int& Rs(int i) { return X[i].sub[1]; }
	void init() { X = X1 + 1; id = nid = 0; X[nil].sum = sum_t(); }
	int make(type val) { X[id] = node(val); return id++; }
	void lock() { nid = id; } //lock all node be constant
	void copy(int& i)  { if (i < nid) { X[id] = X[i]; i = id++; } }
	int key(int i) { return  X[Ls(i)].sum.len; }
	void up(int i) { X[i].sum = X[Ls(i)].sum + X[i].val + X[Rs(i)].sum; }
	void down(int& i) {
		copy(i);
		if (!X[i].add.empty()) {
			if (Ls(i) != nil) { copy(Ls(i)); X[Ls(i)].update(X[i].add); }
			if (Rs(i) != nil) { copy(Rs(i)); X[Rs(i)].update(X[i].add); }
			X[i].add = add_t();
		}
	}
	int split(int& t, int index, bool left) {
		if (t == nil) return nil;
		down(t); int l = Ls(t), r = Rs(t), mid = key(t);
		if (mid < index || (left && mid == index))
		      { l = split(r = Rs(t), index - mid - 1, left); Rs(t) = l; l = t; }
		else  { l = split(r = Ls(t), index,           left); Ls(t) = r; r = t; }
		up(t); t = r; return l;
	}
	int merge(int t1, int t2) {
		if (t1 == nil) return t2;
		if (t2 == nil) return t1;
		if (X[t1].ran < X[t2].ran)
		     { down(t1); Rs(t1) = merge(Rs(t1), t2); up(t1); return t1; }
		else { down(t2); Ls(t2) = merge(t1, Ls(t2)); up(t2); return t2; }
	}
	void  update(int& t, add_t add) { copy(t); X[t].update(add); }
	sum_t query(int t) { return X[t].sum; }
};

struct splay_tree
{
	struct node {
		int p; int sub[2]; add_t add; sum_t sum; sum_t val;
		node(int val = INT_MAX):
			add(), sum(1, val), val(1, val) {
			p = sub[0] = sub[1] = nil;
		}
		void update(add_t a) {
			if (a.rev) swap(sub[0], sub[1]);
			add += a; sum += a; val += a;
		}
	} X1[N + 1], *X; int id;
	splay_tree(): X(X1 + 1), id(0) { }
	int& P (int i) { return X[i].p; }
	int& Ls(int i) { return X[i].sub[0]; }
	int& Rs(int i) { return X[i].sub[1]; }

	void init() { id = 0; X[nil].sum = sum_t(); }
	int make(type val) { X[id] = node(val); return id++; }
	int key(int i) { return X[Ls(i)].sum.len; }
	int dir(int i) { return i == Ls(P(i)) ? 0 : i == Rs(P(i)) ? 1 : -1; }
	void up(int i) { X[i].sum = X[Ls(i)].sum + X[i].val + X[Rs(i)].sum; }
	void down(int i) {
		if (Ls(i) != nil) { X[Ls(i)].update(X[i].add); }
		if (Rs(i) != nil) { X[Rs(i)].update(X[i].add); }
		X[i].add = add_t();
	}
	void rotate(int i) {
		int k = X[i].p, di = dir(i);
		int p = X[k].p, dk = dir(k);
		int j = X[i].sub[di ^ 1];
		X[j].p = k; X[k].sub[di	] = j;
		X[k].p = i; X[i].sub[di ^ 1] = k;
		X[i].p = p; if (dk != -1) X[p].sub[dk] = i;
		up(k); up(i);
	}
	void splay(int i) {
		down(i); int di, dj;
		while ((di = dir(i)) != -1) {
			int j = X[i].p;
			if ((dj = dir(j)) == -1) rotate(i);
			else {
				if (di == dj) rotate(j), rotate(i);
				else		  rotate(i), rotate(i);
			}
		}
	}

	//t must be root; t can not be nil
	void bound(int& t, bool d) {
		while (X[t].sub[d] != nil) {
			down(t); t = X[t].sub[d];
		}
		splay(t);
	}
	int setr(int t, int t2) {
		int r = Rs(t);
		down(t); Rs(t) = t2; P(t2) = t; up(t);
		return r;
	}
	int split(int& t, int index, bool left) {
		int p = nil;
		for (int d, i = t; i != nil; i = X[i].sub[d]) {
			down(i);
			int mid = key(i);
			d = mid < index || (left && mid == index);
			if (d) { index -= (mid + 1); p = i; }
		}
		if (p != nil) { splay(p); t = setr(p, nil); }
		return p;
	}
	int merge(int t, int t2) {
		if (t == nil) return t2;
		bound(t, 1); setr(t, t2); return t;
	}
	void update(int t, add_t add) { if (t != nil) X[t].update(add); }
	void reverse(int t) { add_t rev; rev.rev = true; update(t, rev); }
	sum_t query(int t) { return X[t].sum; }

	//begin link cut tree
	//access getroot setroot: return [root, u]
	//lca: return = [root, v]
	//input assert:
	//getroot(u) == getroot(v): path lca update query
	//getroot(u) != getroot(v): link
	int stack[N];
	void dsplay(int i) { //down and splay
		int top = 0;
		for (int j = i; dir(j) != -1; j = X[j].p) stack[top++] = X[j].p;
		while (top > 0) down(stack[--top]);
		splay(i);
	}
	int access(int u) { //return lca with prev access in same tree while t = [root, u]
		int t = nil;
		for (int p = u; p != nil; p = X[p].p) {
			dsplay(p), setr(p, t); t = p;
		}
		return t;
	}
	int getroot(int u) { int t = access(u); bound(t, 0); return t; }
	int setroot(int u) { int t = access(u); reverse(t);  return t; }
	void cut (int u)        { access(u); dsplay(u); P(Ls(u)) = nil; Ls(u) = nil; }
	void link(int u, int v) { P(setroot(v)) = u; }
	int  path(int u, int v) { setroot(u); return access(v); }
	int  lca (int u, int v) { access(u);  return access(v); } //no setroot
	void update(int u, int v, add_t add) { //no setroot
		int r = lca(u, v); int t = setr(r, nil); dsplay(u);
		if (r != u) update(u, add);
		if (r != v) update(t, add);
	}
	sum_t query(int u, int v) { //no setroot
		sum_t sum[2];
		int r = lca(u, v); int t = setr(r, nil); dsplay(u);
		if (r != u) sum[0] = query(u);
		if (r != v) sum[1] = query(t); sum[1].rev();
		return sum[0] + sum[1];
	}

	//maintain edge
	int U[N], V[N];
	void elink(int u, int v, int e) { link(U[e] = u, e); link(e, V[e] = v); }
	void ecut (int e) { setroot(e); cut(U[e]); cut(V[e]); }
} splay;

const int K = 2;
struct point {
	type val[K]; int c;
	type& operator[](int i) { return val[i]; }
	friend bool operator<(point a, point b) { return false; }
	friend type distance(point a, point b) {
		type ret = 0;
		REP (i, K) ret += (a[i] - b[i]) * (a[i] - b[i]);
		return ret;
	}
	friend type distance(point a, point b, int k) {
		return (a[k] - b[k]) * (a[k] - b[k]);
	}
};
struct disp {
	type dis; point p;
	disp(type dis, point p): dis(dis), p(p) {}
	friend bool operator<(disp a, disp b) {
		return a.dis < b.dis;
	}
	disp(): dis(0) {}
};
struct kdtree {
	struct cmp {
		int k; cmp(int k): k(k) {}
		bool operator()(point a, point b) {
			return a[k] < b[k];
		}
	};
	struct node {
		int sub[2]; point val; int div;
		node(point val, int div):
			val(val), div(div) {
			sub[0] = sub[1] = nil;
		}
		node(): div(0) {}
	} X[N]; int id;
	int& Ls(int i) { return X[i].sub[0]; }
	int& Rs(int i) { return X[i].sub[1]; }
	void init() { id = 0; }
	int make(point val, int k) { X[id] = node(val, k); return id++; }
	int divise(point P[], int n) {
		int ret = 0; double maxs2 = 0.0;
		REP (k, K) {
			double avg = 0, s2;
			REP (i, n) avg += P[i][k]; avg /= n;
			REP (i, n) s2 += (P[i][k] - avg) * (P[i][k] - avg);
			if (s2 > maxs2) { ret = k; maxs2 = s2; }
		}
		return ret;
	}
	int divise0(point P[], int n) {
		int ret = 0; type maxd = 0;
		REP (k, K) {
			int maxk = P[0][k], mink = -P[0][k];
			REP (i, n) {
				if (P[i][k] > maxk) maxk = P[i][k];
				if (P[i][k] < mink) mink = P[i][k];
			}
			if (maxk - mink > maxd) { ret = k; maxd = maxk - mink; }
		}
		return ret;
	}
	int make(point P[], int n, int k) {
		if (n == 0) return nil;
		int m = n / 2;
		std::nth_element(P, P + m, P + n, cmp(k));
		int ret = make(P[m], k);
		Ls(ret) = make(P, m, (k + 1) % K);
 		Rs(ret) = make(P + m + 1, n - m - 1, (k + 1) % K);
 		return ret;
	}

	//no need eps for double
	//ans is INPUT FOR PRUNING
	void near(int t, point p, disp& ans) {
		if (t == nil) return;
		disp cur(distance(p, X[t].val), X[t].val);
		if (cur.dis < ans.dis) ans = cur;

		int k = X[t].div, d = X[t].val[k] <= p[k];
		near(X[t].sub[d], p, ans);
		if (distance(p, X[t].val, k) <= ans.dis)
			near(X[t].sub[d^1], p, ans);
	}
	void nth_near(int t, point p, int n, disp ans[]) {
		if (t == nil) return;
		disp cur(distance(p, X[t].val), X[t].val);
		if (cur.dis < ans[0].dis) {
			pop_heap (ans, ans + n);
			ans[n - 1] = cur;
			push_heap(ans, ans + n);
		}

		int k = X[t].div, d = X[t].val[k] <= p[k];
		nth_near(X[t].sub[d], p, n, ans);
		if (distance(p, X[t].val, k) <= ans[0].dis)
			nth_near(X[t].sub[d^1], p, n, ans);
	}
} kdtree;


