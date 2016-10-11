#include <complex>
using namespace std;
typedef complex<double> comp;

#define REP(i, n) for (int i = 0, _= (n); i < _; ++i)
#define FOR(i, l, r) for (int i = (l), _ = (r); i < _; ++i)
#define DWN(i, n) for (int i = (n) - 1; i >= 0; --i)

//lower_bound(val) in [l, r)
template<class T, class Int, class U>
int lower_bound(T f, Int l, Int r, U val) {
	while (l < r) {
		Int m = (l + r) / 2;
		if (f(m) < val) l = m + 1;
		else r = m;
	}
	return l;
}

//findl(l, r, val + 1)
template<class T, class Int, class U>
int upper_bound(T f, Int l, Int r, U val) {
	return lower_bound(f, l, r, ++val);
}

//on 1 -> DFT -1 -> IDFT
//n must be 2^k, DFT on = 1, IDFT on = -1
void fft(comp y[4*N], int n, int on) {
	for (int i = 1, j = n >> 1, k; i < n - 1; i++, j += k) {
		if (i < j) swap(y[i], y[j]);
		for (k = n >> 1; j >= k; k >>= 1) j -= k;
	}
	for(int h = 1; h < n; h <<= 1) {
		comp wn(cos(-on * pi / h), sin(-on * pi / h));
		for (int j = 0; j < n; j += h << 1) {
			comp w = 1.0;
			FOR (k, j, j + h) {
				comp u = y[k], t = w * y[k + h];
				y[k]     = u + t;
				y[k + h] = u - t;
				w *= wn;
			}
		}
	}
	if(on == -1) REP (i, n) y[i] /= n;
}

//x^0 + x^1 + x^2 + ... + x^(n - 1) n1 > 0, n2 > 0
comp y1[4*N], y2[4*N];
template<class T>
void mul(T x[4*N], T x1[4*N], T x2[4*N], int n) {
	REP (i, n) y1[i] = double(x1[i]);
	REP (i, n) y2[i] = double(x2[i]);
	fft(y1, n, 1); fft(y2, n, 1);
	REP (i, n) y1[i] *= y2[i];
	fft(y1, n, -1);
	REP (i, n) x[i] = T(y1[i].real() + 0.5);
}
template<class T>
int mul(T x[4*N], T x1[4*N], T x2[4*N], int n1, int n2) {
	int n = 1; while (n < 2*n1 || n < 2*n2) n <<= 1;
	FOR (i, n1, n) x1[i] = 0;
	FOR (i, n2, n) x2[i] = 0;
	mul(x, x1, x2, n);
	while (n > 1 && x[n - 1] == 0) n--;
	return n;
}

int64 x1[4*N], x2[4*N], x[4*N];
void mul(char s[2*N], char s1[N], char s2[N]) {
	int n1 = strlen(s1), n2 = strlen(s2);
	reverse(s1, s1 + n1); reverse(s2, s2 + n2);
	REP (i, n1) x1[i] = double(s1[i] - '0');
	REP (i, n2) x2[i] = double(s2[i] - '0');
	int n = mul(x, x1, x2, n1, n2);
	REP (i, n) { x[i + 1] += x[i] / 10; x[i] %= 10; }
	while (x[n] > 0) { x[n + 1] += x[n] / 10; x[n] %= 10; n++; }
	DWN (i, n) s[n - i - 1] = x[i] + '0'; s[n] = '\0';
}

//fast than fft and ntt when type is integer. O(n^log(3/2))
struct karatsuba {
	typedef int64 type;
	type poor[N]; int id;
	karatsuba(): id(0) {}
	void add(type x[], type y[], int n) { REP (i, n) x[i] += y[i]; }
	void sub(type x[], type y[], int n) { REP (i, n) x[i] -= y[i]; }
	//n must be 2^n
	void mul(type r[], type x[], type y[], int n) {
		if (n <= 16) {
			REP (i, n + n) r[i] = 0;
			REP (i, n) REP (j, n) r[i + j] += x[i] * y[j];
		} else {
			int n2 = n / 2;
			mul(r, x, y, n2); mul(r + n, x + n2, y + n2, n2);
			type* xy = poor + id; id += n;
			sub(x, x + n2, n2); sub(y + n2, y, n2);
			mul(xy, x, y + n2, n2);
			add(x, x + n2, n2); add(y + n2, y, n2);
			add(xy, r, n); add(xy, r + n, n);
			add(r + n2, xy, n);
			id -= n;
		}
	}
};

struct Dlx
{
#define EACH(i, h, D) for (int _ = h, i = D[_]; i != _; i = D[i])
	int L[N], R[N], U[N], D[N], row[N], col[N], id; //node
	int p, n, m, size[N];
	void link(int id, int ll, int rr, int uu, int dd) {
		R[ll] = id; L[rr] = id; D[uu] = id; U[dd] = id;
		L[id] = ll; R[id] = rr; U[id] = uu; D[id] = dd;
	}
	void init(int n, int m) {
		this->n = n; this->m = m; p = n + m; id = p + 1;
		FOR (i, 0, m) { col[i] = i; row[i] = p; size[i] = 0; }
		FOR (i, m, p) { row[i] = i; col[i] = p; size[i] = 0; }
		FOR (i, 0, m) { L[i] = i - 1; R[i] = i + 1; U[i] = D[i] = i; }
		FOR (i, m, p) { U[i] = i - 1; D[i] = i + 1; L[i] = R[i] = i; }
		col[p] = row[p] = size[p] = p; link(p, m - 1, 0, p - 1, m);
	}
	void set(int r, int c) {
		r += m; row[id] = r; col[id] = c; size[r]++; size[c]++;
		link(id++, L[r], r, U[c], c);
	}
	//repeat cover
	void remove(int x) {
		int r = row[x]; D[U[r]] = D[r]; U[D[r]] = U[r];
		EACH(i, x, D) { R[L[i]] = R[i]; L[R[i]] = L[i]; size[row[i]]--; }
	}
	void resume(int x) {
		int r = row[x]; D[U[r]] = r; U[D[r]] = r;
		EACH(i, x, U) { R[L[i]] = i; L[R[i]] = i;  size[row[i]]++; }
	}
	//exact cover
	void remove1(int x) {
		int c = col[x];               R[L[c]] = R[c]; L[R[c]] = L[c];
		EACH(i, c, D) EACH(j, i, R) { D[U[j]] = D[j]; U[D[j]] = U[j]; size[col[j]]--; }
	}
	void resume1(int x) {
		int c = col[x];               R[L[c]] = c; L[R[c]] = c;
		EACH(i, c, U) EACH(j, i, L) { D[U[j]] = j; U[D[j]] = j; size[col[j]]++; }
	}
	bool vis[N];
	int A() {
		int cnt = 0, num = 1, ret = 0;
		EACH(i, p, R) cnt++;
		EACH(i, p, D) num = max(num, size[i]);
		EACH(c, p, R) vis[c] = false;
		EACH(c, p, R) if (!vis[c]) {
			ret++; EACH(i, c, D) EACH(j, row[i], R) vis[col[j]] = true;
		}
		return max(ret, (cnt + num - 1) / num);
	}
	int best[N], nbest;
	void dfs(int ans[], int& nans) {
		if (nbest != -1 && !(nans + A() < nbest)) return;
		if (R[p] == p) {
			if (nbest == -1 || nans < nbest) {
				nbest = nans; REP (i, nans) best[i] = ans[i];
			}
		} else {
			int c = R[p]; EACH(i, p, R) if (size[i] < size[c]) c = i;
			EACH(i, c, D) {
				EACH(j, row[i], R) remove(j);
				ans[nans++] = row[i] - m; dfs(ans, nans); --nans;
				EACH(j, row[i], L) resume(j);
			}
		}
	}
	int solve(int ans[], int max = -2) { //return max + 1 if impossible
		nbest = max + 1; int nans = 0; dfs(ans, nans);
		nans = nbest; REP (i, nans) ans[i] = best[i];
		return nans;
	}
#undef EACH
} dlx;
