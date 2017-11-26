#include "template.h"
static const int M = 27;

//[0, n]
template<class T>
void kmp0(T sub[], int next[], int m, T str[], int match[], int n) {
	int j = 0;
	REP (i, n) {
		while (j != -1 && (j == m || sub[j] != str[i])) j = next[j];
		match[i + 1] = ++j;
	}
}

template<class T>
void kmp(T sub[], int next[], int m, T str[], int match[], int n) {
	next[0] = -1; next[1] = 0;
	kmp0(sub, next, m, sub + 1, next + 1, m - 1);
	kmp0(sub, next, m, str, match, n);
}

//[0, n)
template<class T>
void extkmp0(T sub[], int next[], int m, T str[], int match[], int n) {
    int j = 0, r = 0;
    REP (i, n) {
        int l = max(0, min(next[i - j], r - i));
        while (l < m && i + l < n && sub[l] == str[i + l]) l++;
        if (i + l > r) { j = i; r = i + l; }
        match[i] = l;
    }
}

template<class T>
void extkmp(T sub[], int next[], int m, T str[], int match[], int n) {
    next[0] = m;
    extkmp0(sub, next, m, sub + 1, next + 1, m - 1);
    extkmp0(sub, next, m, str, match, n);
}

struct trie
{
	int to[N][M];
	int match[N];
	int id, root;
	int newnode() {
		match[id] = 0;
		REP (c, M) to[id][c] = nil;
		return id++;
	}
	void init() {
		id = root = 0;
		newnode();
	}
	void insert(int s[], int n) {
		int i = 0;
		REP (j, n) {
			if (to[i][s[j]] == nil)
				to[i][s[j]] = newnode();
			i = to[i][s[j]];
		}
		match[i] = n;
	}
	int fail[N];
	int go(int i, int c) {
		while (i != nil && to[i][c] == nil) i = fail[i];
		return i == nil ? root : to[i][c];
	}
	void initac() {
		static int que[N];
		int l = 0, r = 0;
		fail[root] = nil;
		que[r++] = root;
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
};

struct sam
{
	int fail[2*N], len[2*N], to[2*N][M];
	int id, root, last;
	int newnode(int l, int v = nil) {
		len[id] = l;
		fail[id] = v == nil ? nil : fail[v];
		REP (x, M) to[id][x] = v == nil ? nil : to[v][x];
		return id++;
	}
	void init(int root) {
		id = root;
		last = newnode(0);
	}
	void add(int c)
	{
		int end = newnode(len[last] + 1);
		int u = last;
		while (u != nil && to[u][c] == nil) {
			to[u][c] = end; u = fail[u];
		}
		if (u == nil) {
			fail[end] = root;
		} else {
			int v = to[u][c];
			if (len[u] + 1 == len[v]) {
				fail[end] = v;
			} else {
				int w = newnode(len[u] + 1, v);
				fail[end] = fail[v] = w;
				while (u != nil && to[u][c] == v) {
					to[u][c] = w; u = fail[u];
				}
			}
		}
		last = end;
	}
	int go(int i, int c) {
		while (i != nil && to[i][c] == nil) i = fail[i];
		return i == nil ? root : to[i][c];
	}
};

struct sa
{
	//suffix, rank, height;
	int S[N], R[N], H[N], n;

	int C[N], X[N];
	//str[n - 1] = 0, 1 < str[i] < m
	void init(const int str[], int n, int m)
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
			m = 0;
			REP (i, n) {
				if (i == 0 ||
					X[S[i] + 0] != X[S[i - 1] + 0] ||
					X[S[i] + k] != X[S[i - 1] + k]) C[m++] = i;
				R[S[i]] = m - 1;
			}
			if (m == n) break;
		}

		int k = 0;
		REP (i, n) {
			int j = S[R[i] - 1];
			k = max(k - 1, 0);
			while (str[i + k] == str[j + k]) k++;
			H[R[i]] = k;
		}
	}
	void norm() {
		n--;
		REP (i, n) {
			S[i] = S[i + 1];
			H[i] = H[i + 1];
			R[i]--;
		}
	}
};
