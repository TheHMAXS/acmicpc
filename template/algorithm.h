#include <complex>
using namespace std;
typedef long long int64;
typedef complex<double> comp;

const int N = 1111111;
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

//lower_bound(val + 1)
template<class T, class Int, class U>
int upper_bound(T f, Int l, Int r, U val) {
	return lower_bound(f, l, r, ++val);
}

void add(int64& a, int64 b, int64 mod) {
	a += b;
	if (a >= mod) a -= mod;
	if (a < 0)	a += mod;
}
struct vec {
	static const int n = 2;
	int64 val[n];
	vec(int x = 0) { REP (i, n) val[i] = x; }
};
struct matrix {
	static const int n = 2;
	int64 val[n][n];
	matrix(int x = 0) {
		REP (i, n) REP (j, n) val[i][j] = 0;
		REP (i, n) val[i][i] = x;
	}
	void operator+=(const matrix& A) {
		REP (i, n) REP (j, n)
			add(val[i][j], A.val[i][j], mod);
	}
	friend matrix operator*(const matrix& A, const matrix& B) {
		matrix R;
		REP (i, n) REP (j, n) REP (k, n)
			add(R.val[i][j], A.val[i][k] * B.val[k][j] % mod, mod);
		return R;
	}
	friend vec operator*(const matrix A, const vec& B) {
		vec R;
		REP (i, n) REP (k, n)
			add(R.val[i], A.val[i][k] * B.val[k] % mod, mod);
		return R;
	}
};
matrix sumpow(matrix a, int64 b) {
	matrix x = 1, sa = 1, sx = 0;
	for (; b != 0; b >>= 1, sa += a * sa, a = a * a)
		if (b & 1) sx += x * sa, x = x * a;
	return sx;
}
matrix pow(matrix a, int64 b) {
	matrix x = 1;
	for (; b != 0; b >>= 1, a = a * a)
		if (b & 1) x = x * a;
	return x;
}

template<class T> T gcd(T a, T b) {
	for (T r; b != 0; r = a % b, a = b, b = r);
	return a;
}

template<class T> T gcd(T a, T b, T &x, T &y) {
	T xa = 1, xb = 0;
	T ya = 0, yb = 1;
	while (b != 0) {
		x = xa - a / b * xb; xa = xb; xb = x;
		y = ya - a / b * yb; ya = yb; yb = y;
		T r = a % b; a = b; b = r;
	}
	x = xa; y = ya; return a;
}

int64 pow(int64 a, int64 b, int64 mod) {
	int64 x = 1;
	for (; b != 0; b >>= 1, a = a * a % mod)
		if (b & 1) x = x * a % mod;
	return x;
}
int64 sumpow(int64 a, int64 b, int64 mod) {
	int64 x = 1, sa = 1, sx = 0;
	for (; b != 0; b >>= 1, add(sa, a * sa % mod, mod), a = a * a % mod)
		if (b & 1) add(sx, x * sa % mod, mod), x = x * a % mod;
	return sx;
}
//a ^ b == a ^ (b % eular(c) + eular(c)) (mod c)
int eular(int n){
	int ret = 1;
	for(int i = 2; i * i <= n; i++) {
		if	  (n % i == 0) { n /= i; ret *= i - 1; }
		while (n % i == 0) { n /= i; ret *= i; }
	}
	if (n > 1) ret *= n - 1;
	return ret;
}

int64 rev(int64 a, int64 mod) {
	int64 x, y; gcd(a, mod, x, y);
	while (x < 0) x += mod;
	while (x >= mod) x -= mod;
	return x;
//  return pow(a, mod - 2, mod);
}
int64 china(int64 r[], int64 mod[], int n) {
	int64 x = 0, m = 1;
	REP (i, n) m *= mod[i];
	REP (i, n) {
		int64 mi = m / mod[i];
		x += r[i] * rev(mi, mod[i]) * mi;
	}
	return x % m;
}

template<int n, int m>
void calC(int64 (&C)[n][m], int64 mod) {
	REP (j, m) C[0][j] = 0;
	REP (i, n) C[i][0] = 1;
	FOR (i, 1, n) FOR (j, 1, m) C[i][j] = (C[i - 1][j] + C[i - 1][j - 1]) % mod;
}
int64 calCN(int64 n, int64 m, int64 mod) {
	if (m > n) return 0;
	int64 ret = 0;
	REP (i, n + 1) { //C(i, m)
		if (i == m) ret = 1;
		if (i > m) ret = ret * i % mod * rev(i - m, mod) % mod;
	}
	return ret;
}
int64 calCM(int64 n, int64 m, int64 mod) {
	if (m > n) return 0;
	int64 ret = 1;
	REP (i, m + 1) {
		if (i > 0) ret = ret * (n - i + 1) % mod * rev(i, mod) % mod; //C(n, i)
	}
	return ret;
}

namespace fft
{
	//with chain() can solve int64
	void ntt(int64 y[4*N], int n, int on, int64 mod = (479 << 21) + 1) {
		static const int64 unit = 3;
		for (int i = 1, j = n >> 1, k; i < n - 1; i++, j += k) {
			if (i < j) swap(y[i], y[j]);
			for (k = n >> 1; j >= k; k >>= 1) j -= k;
		}
		for(int h = 1; h < n; h <<= 1) {
			int64 wn = pow(unit, (mod - 1) / h / 2, mod);
			for (int j = 0; j < n; j += h << 1) {
				int64 w = 1;
				FOR (k, j, j + h) {
					int64 u = y[k] % mod;
					int64 t = w * y[k + h] % mod;
					y[k] = y[k + h] = u;
					add(y[k], t, mod); add(y[k + h], -t, mod);
					w = w * wn % mod;
				}
			}
		}
		if(on == -1) REP (i, n) y[i] = y[i] * rev(n, mod) % mod;
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
};

namespace polya //no test
{
	int loops(int p[], int n) { //count loops of permutation
		static bool vis[N];
		int ret = 0;
		REP (i, n) vis[i] = false;
		REP (i, n) if (!vis[i]) {
			ret++; int j = i;
			do { vis[j] = true; j = p[j]; } while(j != i);
		}
		return ret;
	}
	int64 burnside(int64 C[], int n) {//C: loops
		int64 ret = 0;
		REP (i, n) ret += C[i];
		return ret / n;
	}
	int64 polya(int64 m, int64 C[], int n, int64 mod) {//m: color count
		int64 ret = 0;
		REP (i, n) add(ret, pow(m, C[i], mod), mod);
		ret = ret * rev(ret, mod) % mod;
		return ret;
	}
};

//fast than fft and ntt when type is integer. O(n^log(3/2))
struct karatsuba
{
	typedef int64 type;
	type poor[N]; int id = 0;
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
		if (nans + A() <= nbest) return;
		if (R[p] == p) {
			if (nbest > nans) {
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
	int solve(int ans[], int max = inf - 1) { //return max + 1 if impossible
		nbest = max + 1; int nans = 0; dfs(ans, nans);
		nans = nbest; REP (i, nans) ans[i] = best[i];
		return nans;
	}
#undef EACH
} dlx;

const int PN = 7 + 1, PM = 2 * 3 * 5 * 7 * 11 * 13 * 17 + 1, M = 4111111;
struct prime
{
	int prime[M], n, count[M + 1], m; bool is[M + 1]; //count primes <= M
	void init(int m) {
		this->m = ++m; REP (i, m) is[i] = true;
		is[0] = is[1] = false;
		for (int i = 2; i * i < m; i++) if (is[i])
			for (int j = i * i; j < m; j += i) is[j] = false;
		n = 0; REP (i, m) if (is[i]) prime[n++] = i;
		count[0] = 0; FOR (i, 1, m) count[i] = count[i - 1] + is[i];
	}

	//lehmer O(n^(2/3))
	int64 dp[PM][PN], pmul[PN];
	void initphi() {
		init(M); REP (i, PM) dp[i][0] = i;
		FOR (m, 1, PM) FOR (n, 1, PN)
			dp[m][n] = dp[m][n - 1] - dp[m / prime[n - 1]][n - 1];
		pmul[0] = 1; FOR (n, 1, PN) pmul[n] = pmul[n - 1] * prime[n - 1];
	}
	int64 phi(int64 m, int n) { // m < M * M
		if (n == 0) return m;
		if (m < M && m <= prime[n - 1] * prime[n - 1]) return count[m] - n + 1;
		if (pmul[n] < PM && n < PN)
			return dp[m % pmul[n]][n] + (m / pmul[n]) * dp[pmul[n]][n];
		return phi(m, n - 1) - phi(m / prime[n - 1], n - 1);
	}
	int64 pi(int64 m) { //count primes <= m, m < M * M
		//initphi();
		if (m < M) return count[m];
		int m2 = sqrt(m + 0.5), m3 = cbrt(m + 0.5), a = pi(m3);
		int64 ret = phi(m, a) + a - 1;
		for (int i = a; prime[i] <= m2; i++)
			ret = ret - pi(m / prime[i]) + pi(prime[i]) - 1;
		return ret;
	}

	//lehmer O(n^(3/4))
	static int64 pi2(int64 n) { //count primes <= n, n < M * M
		static int64 lehmer[M], phi[M]; //[sqrt(n)]
		int64 m; for(m = 1; m * m <= n; m++) lehmer[m] = n / m - 1;
	    for (int64 i = 1; i <= m; i++) phi[i] = i - 1;
	    for (int64 i = 2; i <= m; i++) {
	        if (phi[i] == phi[i - 1]) continue;
	        for (int64 j = 1; j <= min(m - 1, n / i / i); j++) {
	            if(i * j < m) lehmer[j] -= lehmer[i * j] - phi[i - 1];
	            else lehmer[j] -= phi[n / i / j] - phi[i - 1];
	        }
	        for(int j = m; j >= i * i; j--) phi[j] -= phi[j / i] - phi[i - 1];
	    }
	    return lehmer[1];
	}
};

struct gauss {
	type val[N][N]; int n, m, l;
	void init(int n, int m, int l) {
		this->n = n; this->m = m; this->l = l;
		REP (i, n) REP (j, l) val[i][j] = 0;
	}
	int maxrow(int r, int c) {
		FOR (j, r, n) if (abs(val[r][c]) < abs(val[j][c])) r = j; return r;
	}
	void subrow(int i, int j, int c) {
		type mul = val[i][c] / val[j][c]; val[i][c] = 0;
		FOR (k, c + 1, l) val[i][k] -= mul * val[j][k];
		//type valj = val[j][c], vali = val[i][c]; val[i][c] = 0;
		//FOR (k, c, l) val[i][k] = valj * val[i][k] - vali * val[j][k];
	}
	int rank(int col[]) {
		for (int r = 0, c = 0; r < n; r++, c++) {
			int i; while (c < m && sign(val[i = maxrow(r, c)][c]) == 0) c++;
			if (c == m) return r; col[r] = c;
			REP (k, l) swap(val[i][k], val[r][k]);
			FOR (i, r + 1, n) subrow(i, r, c);
		}
		return n;
	}
	bool rev() {
		if (n != m) return false;
		static int col[N]; if (rank(col) < n) return false;
		DWN (r, n) REP (i, r) subrow(i, r, r);
		REP (r, n) FOR (i, n, l) val[r][i] /= val[r][r];
		REP (r, n) val[r][r] = 1;
	}
	int solve(type ans[]) { //-1 impossible, 1 many, 0 one.
		static int col[N]; int r = rank(col);
		for (int ec = m, i = r - 1; i >= 0; ec = col[i], i--){
			int c = col[i]; FOR (k, c, ec) ans[k] = 0;
			FOR (k, c + 1, m) ans[c] -= val[i][k] * ans[k];
			ans[c] = (ans[c] + val[i][m]) / val[i][c];
		}
		FOR (i, r, n) if (sign(val[i][m]) != 0) return -1;
		return r < m ? 1 : 0;
	}
};
struct xorgauss
{
	bool val[N][N]; int n, m, l;
	int  maxrow (int r, int c) {
		FOR (j, r, n) if (val[j][c]) r = j; return r;
	}
	void subrow (int i, int j, int c) {
		if(val[i][c]) FOR (k, c, l) val[i][k] ^= val[j][k];
	}
	int rank(int col[]) {
		for (int r = 0, c = 0; r < n; r++, c++) {
			int i; while (c < m && sign(val[i = maxrow(r, c)][c]) == 0) c++;
			if (c == m) return r; col[r] = c;
			REP (k, l) swap(val[i][k], val[r][k]);
			FOR (i, r + 1, n) subrow(i, r, c);
		}
		return n;
	}
	int solve(int col[], type ans[]) { //-1 impossible, 1 many, 0 one.
		int r = rank(col);
		for (int ec = m, i = r - 1; i >= 0; ec = col[i], i--){
			int c = col[i]; FOR (k, c, ec) ans[k] = 0;
			FOR (k, c + 1, m) if (val[i][k]) ans[c] ^= ans[k];
			ans[c] = (ans[c] ^ val[i][m]);
		}
		FOR (i, r, n) if (sign(val[i][m]) != 0) return -1;
		return r < n ? 1 : 0;
	}
};
