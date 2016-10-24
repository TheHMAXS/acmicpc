#include <algorithm>
using namespace std;
#define REP(i, n) for (int i = 0, _ = (n); i < _; i++)
#define FOR(i, l, r) for (int i = (l), _ = (r); i < _; ++i)
#define DWN(i, n) for (int i = (n) - 1; i >= 0; --i)
#define EDGE(u, v, e) for (int e = head[u], v; e != nil && (v = to[e], true); e = next[e])
const int nil = -1, N = 1111111;
typedef double type;

struct graphics
{
	struct state {
		type dis; int p, u;
		state(type dis, int p, int u): dis(dis), p(p), u(u) {}
		friend bool operator<(state a, state b) { return a.dis > b.dis; }
	};
	int n;
	int head[N];

	int id;
	int to[N];
	int next[N];
	type cost[N];

	void init(int n) { id = 0; this->n = n; REP (i, n) head[i] = nil; }
	int add1(int u, int v, type val) {
		to[id] = v; cost[id] = val;
		next[id] = head[u]; head[u] = id;
		return id++;
	}
	void add2(int u, int v, type val) { add1(u, v, val); add1(v, u, val); }

	int vis[N];
	int stack[N], top;
	//edge (u, v)
	//for indirect graphics
	//if dfn[u] <= low[v] && u != root u = split point
	//if dfn[u] < low[v] (u, v) = split edge
	int belong[N], low[N], dfn[N], tj;
	void tarjandfs(int u) {
		stack[top++] = u;
		vis[u] = 1; low[u] = dfn[u] = tj++;
		EDGE (u, v, e) {
			if (vis[v] == 0) {
				tarjandfs(v);
				low[u] = min(low[u], low[v]);
			} else if (vis[v] == 1) {
				low[u] = min(low[u], dfn[v]);
			}
		}
		vis[u] = 2;
		if (low[u] == dfn[u])
			do belong[stack[--top]] = u;
			while (stack[top] != u);
	}
	void tarjan() {
		tj = 0; REP (i, n) vis[i] = 0;
		REP (i, n) if (vis[i] == 0) tarjandfs(i);
	}
	void topology(graphics& topo, int mp[], bool rev) { //no test
		tarjan();
		REP (i, n) mp[i] = nil;
		int nT = 0;
		REP (i, n) {
			if (mp[belong[i]] == nil)
				mp[belong[i]] = nT++;
			mp[i] = mp[belong[i]];
		}
		topo.init(nT);
		REP (u, n) EDGE(u, v, e)
			rev ? topo.add1(v, u, cost[e]) : topo.add1(u, v, cost[e]);
	}

	bool is2split() {
		REP (i, n) vis[i] = 0;
		bool loop = false; bool split2 = true;
		REP (i, n) if (!vis[i]) {
			vis[i] = 1; stack[top++] = i;
			while (top > 0) {
				int u = stack[--top];
				EDGE(u, v, e) if (!vis[v]) {
					vis[v] = 3 - vis[u];
					stack[top++] = i;
				} else {
					loop = true;
					if (vis[v] == vis[u]) split2 = false;
				}
			}
		}
		return split2;
	}
	type prim(int s, int prev[]) {
		type ret = 0; REP (i, n) vis[i] = false;
		priority_queue<state> que; que.push(state(0, nil, s));
		while (!que.empty()) {
			state cur = que.top(); que.pop(); int u = cur.u;
			if (!vis[u]) {
				vis[u] = true; ret += cur.dis; prev[u] = cur.p;
				EDGE (u, v, e) que.push(state(cost[e], u, v));
			}
		}
		return ret;
	}
	void dijkstra(int s, type dis[], int prev[]) {
		REP (i, n) dis[i] = inf;
		priority_queue<state> que; que.push(state(0, nil, s));
		while (!que.empty()) {
			state cur = que.top(); que.pop(); int u = cur.u;
			if (dis[u] == inf) {
				dis[u] = cur.dis; prev[u] = cur.p;
				EDGE (u, v, e) que.push(state(cur.dis + cost[e], u, v));
			}
		}
	}
	bool spfa(int s, type dis[], int prev[]) {
		static int cnt[N]; REP (i, n) { cnt[i] = 0; dis[i] = inf; }
		queue<state> que; que.push(state(0, nil, s));
		while (!que.empty()) {
			state cur = que.front(); que.pop(); int u = cur.u;
			if (dis[u] > cur.dis) {
				dis[u] = cur.dis; prev[u] = cur.p;
				cnt[u] = cnt[cur.p] + 1; if (cnt[u] > n) return false;
				EDGE (u, v, e) que.push(state(cur.dis + cost[e], u, v));
			}
		}
		return true;
	}
	int toposort(int ans[]) {
		static int in[N];
		REP (i, n) in[i] = 0;
		REP (u, n) EDGE(u, v, e) in[v]++;
		REP (u, n) if (in[u] == 0) stack[top++] = u;
		int i = 0;
		while (top != 0) {
			int u = stack[--top]; ans[i++] = u;
			EDGE(u, v, e) if (--in[v] == 0) stack[top++] = v;
		}
		return i;
	}

	int force2sat(int ans[]) {
		REP (i, n) vis[i] = false; int m = 0;
		REP (i, n) if (!vis[i] && !vis[i ^ 1]) {
			int j = m; bool ok = true;
			stack[top++] = i;
			while (top > 0) {
				int u = stack[--top];
				if (!vis[u]) {
					if (vis[u ^ 1]) ok = false;
					vis[u] = true; ans[m++] = u;
					EDGE(u, v, e) stack[top++] = v;
				}
			}
			if (!ok) while(m > j) vis[ans[--m]] = false;
		}
		sort(ans, ans + m);
		return m;
	}
	bool has2sat() {
		tarjan();
		REP (i, n) if (belong[i] == belong[i ^ 1])
			return false;
		return true;
	}

	//k-th short path
	void mpspush(priority_queue<state>& que, int dis, int e, type A[]) {
		int v = to[e];
		if (A[v] != inf) que.push(state(dis + cost[e] + A[v], e, v));
	}
	int mps(graphics& rev, int s, int t, type ans[], int k) { //return path count
		static type A[N];
		static int unused[N];
		rev.init(n);
		REP (u, n) EDGE(u, v, e) rev.add1(v, u, cost[e]);
		rev.dijkstra(t, A, unused);

		static state de[N];
		REP (u, n) {
			int m = 0; EDGE(u, v, e) de[m++] = state(cost[e] + A[v], e, u);
			sort(de, de + m); head[u] = nil;
			REP (i, m) { int e = de[i].p; next[e] = head[u]; head[u] = e; }
		}

		priority_queue<state> que;
		// if (s == t) ans[m++] = 0;
		if (head[s] != nil) mpspush(que, 0, head[s], A);
		int m = 0; while(m < k && !que.empty()) {
			state cur = que.top(); que.pop();
			ans[m++] = cur.dis; int e = cur.p, v = cur.u;
			type dis = cur.dis - cost[e] - A[v];
			do {
				if (next[e] != nil) mpspush(que, dis, next[e], A);
				dis += cost[e]; v = to[e]; e = head[v];
			} while(v != t);
			if (e != nil) mpspush(que, dis, e, A);
		}
		return m;
	}

	type nst(int s) { //next spinning tree
		static int dp[1111][1111], que[1111];
		REP (u, n) REP (v, n) dp[u][v] = nil;
		REP (i, n) vis[i] = false;
		REP (i, n) que[i] = nil;
		vis[s] = true; type mst = 0;
		EDGE(s, v, e) if (que[v] == nil || cost[que[v]] > cost[e]) que[v] = e;
		while(true) {
			int e = nil;
			REP (v, n) if (que[v] != nil)
				if (e == nil || cost[e] > cost[que[v]]) e = que[v];
			if (e == nil) break;

			int u = to[e], p = to[e ^ 1]; que[u] = nil;
			if (!vis[u]) {
				vis[u] = true; mst += cost[e]; dp[u][p] = e;
				REP (v, n) if (dp[p][v] != nil)
					dp[u][v] = cost[e] > cost[dp[p][v]] ? e : dp[p][v];
				REP (v, n) dp[v][u] = dp[u][v];
				EDGE (u, v, e) if (!vis[v])
					if (que[v] == nil || cost[que[v]] > cost[e]) que[v] = e;
			}
		}

		int edge = nil; type ret = inf;
		REP (i, n) if (!vis[i]) return ret;
		REP (u, n) EDGE (u, v, e) {
			int e0 = dp[u][v]; type cur = mst - cost[e0] + cost[e];
			if (ret > cur) { ret = cur; edge = e0; }
		}
		//remove(edge); ret = prim();
		return ret;
	}

	//vis: 1=delete 2=pick
	bool do2sat(graphics& rtopo, int ans[]) { //no test
		static int mp[N], ith[N];
		if (!has2sat()) return false;
		topology(rtopo, mp, true);
		rtopo.toposort(ith);
		REP (i, rtopo.n) rtopo.vis[i] = 0;
		REP (i, n) {
			int u = mp[ith[i]];
			int r = mp[ith[i] ^ 1];
			if (rtopo.vis[u]) continue;

			vis[u] = 2;
			stack[top++] = r;
			while (top > 0) {
				int p = stack[--top];
				if(!rtopo.vis[p]) {
					rtopo.vis[p] = 1;
					EDGE (p, v, e) stack[top++] = v;
				}
			}
		}
		int m = 0;
		REP (i, n) if (rtopo.vis[belong[i]] == 2) ans[m++] = i;
		//assert(2 * m == n);
		return true;
	}

	type flow[N], cap[N]; //edge
	void addf(int u, int v, int c, int cost = 0) {
		int e = add1(u, v, cost); flow[e] = 0; cap[e] = c;
			e = add1(v, u, cost); flow[e] = 0; cap[e] = 0;
	}
	int que[N], layer[N];
	bool dinicbfs(int s, int t) {
		REP (i, n) cur[i] = head[i];
		REP (i, n) layer[i] = -1;
		int l = 0, r = 0;
		layer[s] = 0; que[r++] = s;
		while (l < r) {
			int u = que[l++];
			EDGE (u, v, e) if (flow[e] < cap[e] && layer[v] == -1) {
				layer[v] = layer[u] + 1; que[r++] = v;
			}
		}
		return layer[t] != -1;
	}
	int cur[N];
	type dinicdfs(int u, int t, type maxf) {
		if (u == t) return maxf;
		int ret = 0;
		for (int& e = cur[u]; e != nil; e = next[e]) {
			int v = to[e];
			if (layer[v] == layer[u] + 1) {
				int f = dinicdfs(v, t, min(cap[e] - flow[e], maxf));
				flow[e  ] += f; ret += f;
				flow[e^1] -= f; maxf -= f;
				if (maxf == 0) break;
			}
		}
		return ret;
	}
	type dinic(int s, int t) {
		int ret = 0;
		while (dinicbfs(s, t))
			ret += dinicdfs(s, t, 0x7FFFFFFF);
		return ret;
	}
} g;

struct tree
{
	typedef int type;
	int n;
	int head[N];
	type val[N];

	int id;
	int to[N];
	int next[N];
	type cost[N];

	void init(int n) { id = 0; this->n = n; REP (i, n) head[i] = nil; }
	void add_(int u, int v, type val) {
		cost[id] = val; to[id] = v;
		next[id] = head[u]; head[u] = id++;
	}
	void add(int u, int v, type val) { add_(u, v, val); add_(v, u, val); }

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
	int lca(int u, int v) { //initlca();
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

	//tree partition solve algorithm
	int valid[N], size[N], maxsize[N];
	void sizedfs(int u, int p) {
		size[u] = 1;
		EDGE(u, v, e) if (valid[v] && v != p) {
			sizedfs(v, u); size[u] += size[v];
		}
	}
	void centerdfs(int u, int p, int sizep, int& c) {
		maxsize[u] = sizep;
		EDGE(u, v, e) if (valid[v] && v != p) {
			maxsize[u] = max(maxsize[u], size[v]);
			centerdfs(v, u, sizep + size[u] - size[v], c);
		}
		if (c == -1 || maxsize[u] < maxsize[c]) c = u;
	}
	void initpart() { REP (i, n) valid[i] = true; }


	int ith[N], L[N], R[N], dfi;
	void tinit(int u) { dfi = 0; } //init data for empty tree
	void tdfs(int u, int p, int64 d) {
		ith[dfi] = u; L[u] = dfi++;
		EDGE(u, v, e) if (valid[v] && v != p) tdfs(v, u, d);
		R[u] = dfi;
	}
	void tquery(int u, int i) { } //update ans
	void tinsert(int u, int i) { }
	void tremove(int u, int i) { }
	void partition(int t) {
		//init_part();
		int u = t; sizedfs(t, -1); centerdfs(t, -1, 0, u);
		valid[u] = false;
		EDGE (u, v, e) if (valid[v]) partition(v);
		valid[u] = true;

		//solve for path pass u
		tinit(u); tdfs(u, -1, 1);
		tquery(u, L[u]); tinsert(u, L[u]);
		EDGE(u, v, e) if (valid[v]) {
			FOR(i, L[v], R[v]) tquery (u, i);
			FOR(i, L[v], R[v]) tinsert(u, i);
		}
		FOR (i, L[u], R[u]) tremove(u, i);
	}


	//tree partition into chains
	int parent[N], deep[N], size[N], heavy[N];
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

	int val_rank[N];
	int make_chain(int u = 0) {
		heavydfs(u, nil); rid = n; chaindfs(u);
		REP (v, n) val_rank[rank[v]] = val[v];
		int ret = segment.make(n);
		segment.set(ret, val_rank);
		return ret;
	}
	//maintain edges in [u, v]
	void update(int& t, int u, int v, add_t a) {
		int tu = top[u], tv = top[v];
		while (tu != tv) {
			if (deep[tu] < deep[tv]) { swap(u, v); swap(tu, tv); }
			segment.update(t, rank[u], rank[tu], a);
			u = parent[tu]; tu = top[u];
		}
		if (u != v) {
			if (deep[u] < deep[v]) { swap(u, v); }
			segment.update(t, rank[u], rank[heavy[v]], a);
		}
	}
	sum_t query(int& t, int u, int v) {
		sum_t sum[2]; bool d = false;
		int tu = top[u], tv = top[v];
		while (tu != tv) {
			if (deep[tu] < deep[tv]) { swap(u, v); swap(tu, tv); d = !d; }
			sum[d] = sum[d] + segment.query(t, rank[u], rank[tu]);
			u = parent[tu]; tu = top[u];
		}
		if (u != v) {
			if (deep[u] < deep[v]) { swap(u, v); d = !d;  }
			sum[d] = sum[d] + segment.query(t, rank[u], rank[heavy[v]]);
		}
		sum[1].rev(); return sum[0] + sum[1];
	}
};
