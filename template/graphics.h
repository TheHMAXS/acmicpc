#include "template.h"

//need eps when using float as cost or cap for spfa and maxflow;
struct graphics
{
	typedef int type;
	static const type inf = INT_MAX;
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
	int com[N], low[N], dfn[N], tj, nc;
	void tarjan(int u) {
		stack[top++] = u;
		low[u] = dfn[u] = tj++;
		EDGE (u, v, e) {
			if (dfn[v] == -1) tarjan(v);
			if (com[v] == -1) low[u] = min(low[u], low[v]);
		}
		if (low[u] == dfn[u]) do {
			com[stack[--top]] = nc;
		} while (stack[top] != u);
		nc += low[u] == dfn[u];
	}
	void tarjan() {
		tj = nc = 0; REP (i, n) com[i] = dfn[i] = -1;
		REP (i, n) if (vis[i] == 0) tarjan(i);
	}
	void topology(graphics& topo) { //no test
		tarjan(); topo.init(nc);
		REP (u, n) EDGE(u, v, e) {
			topo.add1(com[u], com[v], cost[e]);
		}
	}

	bool is2split() {
		REP (i, n) vis[i] = 0;
		bool loop = false;
		bool split2 = true;
		REP (i, n) if (!vis[i]) {
			vis[i] = 1;
			stack[top++] = i;
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


	bool has2sat() {
		tarjan();
		REP (i, n) if (com[i] == com[i ^ 1])
			return false;
		return true;
	}
	//vis: 1=delete 2=pick
	bool do2sat(graphics& rtopo, int ans[]) { //no test
		static int ith[N];
		if (!has2sat()) return false;
		tarjan();
		rtopo.init(nc);
		REP (u, n) EDGE(u, v, e)
			rtopo.add1(com[u], com[v], cost[e]);
		rtopo.toposort(ith);
		REP (i, rtopo.n) rtopo.vis[i] = 0;
		REP (i, n) {
			int u = com[ith[i]];
			int r = com[ith[i] ^ 1];
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
		REP (i, n) if (rtopo.vis[com[i]] == 2) ans[m++] = i;
		//assert(2 * m == n);
		return true;
	}

	int flow[N], cap[N]; //edge
	void addf(int u, int v, int c, type cost = 0) {
		int e = add1(u, v,  cost); flow[e] = 0; cap[e] = c;
			e = add1(v, u, -cost); flow[e] = 0; cap[e] = 0;
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
	type dinicdfs(int u, int t, int maxf) {
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
			ret += dinicdfs(s, t, inf);
		return ret;
	}

	// return false if has negative loop
	bool spfa(int s, type dis[], int edge[]) {
		static int cnt[N];
		static bool in[N];
		REP (i, n) cnt[i] = 0;
		REP (i, n) in[i] = false;
		REP (i, n) dis[i] = inf;
		REP (i, n) edge[i] = nil;
		dis[s] = 0;
		edge[s] = nil;
		queue<int> que;
		que.push(s); in[s] = true;
		while (!que.empty()) {
			int u = que.front();
			que.pop(); in[u] = false;
			if (++cnt[u] > n) return false;
			EDGE (u, v, e) if (flow[e] < cap[e]) {
				if (dis[v] > dis[u] + cost[e]) { //dis[u] + cost[e] + eps
					dis[v] = dis[u] + cost[e];
					edge[v] = e;
					if (!in[v]) {
						in[v] = true; que.push(v);
					}
				}
			}
		}
		return true;
	}
	type mincost_maxflow(int s, int t) {
		static type dis[N];
		static int edge[N];
		int maxf = 0;
		while (true) {
			if (!spfa(s, dis, edge)) return 0;
			if (edge[t] == nil) break;
			int f = INT_MAX;
			for (int u = t; edge[u] != nil; u = to[edge[u] ^ 1])
				f = min(f, cap[edge[u]] - flow[edge[u]]);
			for (int u = t; edge[u] != nil; u = to[edge[u] ^ 1]) {
				flow[edge[u]] += f; flow[edge[u] ^ 1] -= f;
			}
			maxf += f;
		}
		type minc = 0;
		REP (e, id) if (cap[e] > 0)
			minc += flow[e] * cost[e];
		return minc;
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
	static const int M = 30;
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

	int ith[N], L[N], R[N], dfi;
	void tdfs(int u, int p, int64 d) {
		ith[dfi] = u; L[u] = dfi++;
		EDGE(u, v, e) if (valid[v] && v != p) tdfs(v, u, d);
		R[u] = dfi;
	}
	//u is the root of part tree, i is the dfi of node
	void tinit(int u) { dfi = 0; } //init data for empty tree, may add 0
	void tquery(int u, int i) { } //update ans
	void tinsert(int u, int i) { }
	void tremove(int u, int i) { }
	void initpartition() { REP (i, n) valid[i] = true; }
	void partition(int t) { //initpartition();
		int u = t; sizedfs(t, -1); centerdfs(t, -1, 0, u);
		valid[u] = false;
		EDGE (u, v, e) if (valid[v]) partition(v);
		valid[u] = true;

		//solve for path pass u
		tinit(u); tdfs(u, -1, 1);
		//tquery(u, L[u]); tinsert(u, L[u]); solve for node
		EDGE(u, v, e) if (valid[v]) {
			FOR(i, L[v], R[v]) tquery (u, i);
			FOR(i, L[v], R[v]) tinsert(u, i);
		}
		FOR (i, L[u] + 1, R[u]) tremove(u, i);
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
