#include <algorithm>
using namespace std;
#define REP(i, n) for (int i = 0, _ = (n); i < _; i++)
#define DWN(i, n) for (int i = (n) - 1; i >= 0; --i)
#define EDGE(u, v, e) for (int e = head[u], v; e != nil && (v = to[e], true); e = next[e])
const int nil = -1, N = 1111111;
struct graphics
{
	typedef int type;
	int n;
	int head[N];

	int id;
	int to[N];
	int next[N];
	type cost[N];

	void init(int n) {
		id = 0;
		this->n = n;
		REP (i, n) head[i] = nil;
	}
	int add1(int u, int v, type val) {
		to[id] = v;
		cost[id] = val;
		next[id] = head[u];
		head[u] = id;
		return id++;
	}

	int vis[N];
	int stack[N], top;

	//edge (u, v)
	//for indirect graphics
	//if dfn[u] <= low[v] && u != root u = split point
	//if dfn[u] < low[v] (u, v) = split edge
	int low[N], dfn[N], tj;
	void tarjandfs(int u, int belong[]) {
		stack[top++] = u;
		low[u] = dfn[u] = tj++;
		vis[u] = 1;
		EDGE (u, v, e) {
			if (vis[v] == 0) {
				tarjandfs(v, belong);
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
	void tarjan(int belong[]) {
		tj = 0;
		REP (i, n) vis[i] = 0;
		REP (i, n) if (vis[i] == 0) tarjandfs(i, belong);
	}

	int mbelong[N];
	void topology(graphics& topo, int belong[], bool rev = false) { //no test
		tarjan(mbelong);
		REP (i, n) belong[i] = nil;
		int nT = 0;
		REP (i, n) {
			if (belong[mbelong[i]] == nil)
				belong[mbelong[i]] = nT++;
			belong[i] = belong[mbelong[i]];
		}
		topo.init(nT);
		REP (u, n) EDGE(u, v, e)
			rev ? topo.add1(v, u, cost[e]) : topo.add1(u, v, cost[e]);
	}

	int in[N];
	int gsort(int ans[]) {
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

	//begin no test
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


	bool has2sat() { //no test
		tarjan(mbelong);
		REP (i, n) if (mbelong[i] == mbelong[i ^ 1])
			return false;
		return true;
	}

	//vis: 1=delete 2=pick
	bool do2sat(graphics& rtopo, int ans[]) { //no test
		static int belong[N], sorted[N];
		if (!has2sat()) return false;
		topology(rtopo, belong, true);
		rtopo.gsort(sorted);
		REP (i, rtopo.n) rtopo.vis[i] = 0;
		REP (i, n) {
			int u = belong[sorted[i]];
			int r = belong[sorted[i] ^ 1];
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
	bool split2dfs(int u) {
		REP (i, n) vis[u] = 0;
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
	//end no test

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
