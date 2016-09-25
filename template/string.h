#include <algorithm>
using namespace std;

#define REP(i, n) for (int i = 0, _= (n); i < _; ++i)
#define DWN(i, n) for (int i = (n) - 1; i >= 0; --i)
#define FOR(i, l, r) for (int i = (l), _ = (r); i < _; ++i)
const int nil = -1, N = 1111111, M = 26;
typedef int type;

struct KMP {
	int fail[N];
	type str[N];
	int n;
	int go(int i, type c) {
		while (i == n || (i != -1 && str[i] != c)) i = fail[i];
		return i + 1;
	}
	void init(type s[], int m) {
		n = m;
		REP (i, m) str[i] = s[i];
		fail[0] = -1; fail[1] = 0;
		FOR (i, 1, m) fail[i + 1] = go(fail[i], str[i]);
	}
	//-1 not find
	int find(type s[], int m) {
		int i = 0, j = 0;
		while (i < m && j < n) j = go(j, s[i++]);
		return j == n ? i - n : -1;
	}
} kmp;

namespace trie{
struct matrix {
	static const int n = 40;
	int64 val[n][n];
};
struct TRIE
{
    typedef int type;
    int to[N][M];
    int match[N];
    int id;
    int newnode() {
        match[id] = 0;
        REP (c, M) to[id][c] = nil;
        return id++;
    }
    void init() { id = root; newnode(); }
    void insert(type s[], int n) {
        int i = root;
        for (int j = 0; j < n; i = to[i][s[j++]])
            if (to[i][s[j]] == nil) to[i][s[j]] = newnode();
        match[i] = n;
    }
    int fail[N]; int que[N];
    int go(int i, type c) {
        while (i != nil && to[i][c] == nil) i = fail[i];
        return i == nil ? root : to[i][c];
    }
    void initac() {
        int l = 0, r = 0;
        fail[root] = nil; que[r++] = root;
        while (l < r) {
            int i = que[l++];
            REP (c, M) if (to[i][c] != nil) {
                int j = to[i][c];
                fail[j] = go(fail[i], c);
                match[j] = max(match[j], match[fail[j]]);
                que[r++] = j;
            }
        }
    }
	matrix fail_matrix() {
		matrix R;
		FOR (i, root, id) REP (c, M) {
			int j = go(i, c);
			if (match[j] == 0) R.val[j][i]++;
		}
		return R;
	}
};
struct SAM
{
	int fail[2*N], len[2*N], to[2*N][M];
	int id, root, last;
	int newnode(int l, int v = nil) {
		len[id] = l;
		fail[id] = v == nil ? nil : fail[v];
		if (v == nil) REP (x, M) to[id][x] = nil;
		else REP (x, M) to[id][x] = to[v][x];
		return id++;
	}
	void init(int root) {
		id = root; last = newnode(0);
	}
	void add(type c)
	{
		int end = newnode(len[last] + 1);
		int u = last;
		while(u != nil && to[u][c] == nil)
			to[u][c] = end, u = fail[u];

		if (u == nil) fail[end] = root;
		else {
			int v = to[u][c];
			if (len[u] + 1 == len[v]) fail[end] = v;
			else {
				int w = newnode(len[u] + 1, v);
				fail[end] = fail[v] = w;
				while (u != nil && to[u][c] == v)
					to[u][c] = w, u = fail[u];
			}
		}
		last = end;
	}
	int go(int i, type c) {
		while (i != nil && to[i][c] == nil) i = fail[i];
		return i == nil ? root : to[i][c];
	}
};

//not compelete
struct SA
{
	//suffix, rank, height;
	int S[N], R[N], H[N], n;

	//str[n - 1] = 0, 1 < str[i] < m
	int C[N], X[N];
	void init(const type str[N], int n, int m)
	{
		this->n = n;

		REP (i, n) R[i] = str[i];
		REP (i, m) C[i] = 0;
		REP (i, n) C[R[i]]++;
		FOR (i, 1, m) C[i] += C[i - 1];
		DWN (i, n) S[--C[R[i]]] = i;

		for (int k = 1; k < n; k <<= 1) {
			REP (i, n) X[i] = S[i];
			REP (i, n) {
				int j = X[i] - k;
				if (j < 0) j += n;
				S[C[R[j]]++] = j;
			}

			REP (i, n) X[i] = R[i];
			m = 0; REP (i, n) {
				if (i == 0 || X[S[i]] != X[S[i - 1]] ||
						X[S[i] + k] != X[S[i - 1] + k]) C[m++] = i;
				R[S[i]] = m - 1;
			}
			if (m == n) break;
		}

		int k = 0; REP (i, n) {
			int j = S[R[i] - 1];
			k = max(k - 1, 0);
			while (str[i + k] == str[j + k]) k++;
			H[R[i]] = k;
		}
	}

	void norm() { n--; REP (i, n) S[i] = S[i + 1], H[i] = H[i + 1], R[i]--; }
};

}

