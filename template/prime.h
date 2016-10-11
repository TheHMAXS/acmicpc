#include <bits/stdc++.h>
using namespace std;
#define REP(i, n) for (int i = 0, _= (n); i < _; ++i)
#define FOR(i, l, r) for (int i = (l), _ = (r); i < _; ++i)

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

//with chain() can solve any large number!
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
	if(on == -1) {
		REP (i, n) y[i] = y[i] * rev(n, mod) % mod;
	}
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

namespace pcf {
	#define MAXN 100   // pre-calc max n for phi(m, n)
	#define MAXM 70010 // pre-calc max m for phi(m, n)
	#define MAXP 666666 // max primes counter
	#define MAX 320010	// max prime
	#define setbit(ar, i) (((ar[(i) >> 6]) |= (1 << (((i) >> 1) & 31))))
	#define chkbit(ar, i) (((ar[(i) >> 6]) & (1 << (((i) >> 1) & 31))))
	#define isprime(x) (( (x) && ((x)&1) && (!chkbit(ar, (x)))) || ((x) == 2))
	long long dp[MAXN][MAXM];
	unsigned int ar[(MAX >> 6) + 5] = { 0 };
	int len = 0, primes[MAXP], counter[MAX];

	void Sieve() {
		setbit(ar, 0), setbit(ar, 1);
		for (int i = 3; (i * i) < MAX; i++, i++) {
			if (!chkbit(ar, i)) {
				int k = i << 1;
				for (int j = (i * i); j < MAX; j += k) setbit(ar, j);
			}
		}

		for (int i = 1; i < MAX; i++) {
			counter[i] = counter[i - 1];
			if (isprime(i)) primes[len++] = i, counter[i]++;
		}
	}

	void init() {
		Sieve();
		for (int n = 0; n < MAXN; n++) {
			for (int m = 0; m < MAXM; m++) {
				if (!n) dp[n][m] = m;
				else dp[n][m] = dp[n - 1][m] - dp[n - 1][m / primes[n - 1]];
			}
		}
	}

	long long phi(long long m, int n) {
		if (n == 0) return m;
		if (primes[n - 1] >= m) return 1;
		if (m < MAXM && n < MAXN) return dp[n][m];
		return phi(m, n - 1) - phi(m / primes[n - 1], n - 1);
	}

	long long Lehmer(long long m){
		if (m < MAX) return counter[m];
		long long res = 0;
		int i, a, s, c, y;
		s = sqrt(0.9 + m), y = c = cbrt(0.9 + m);
		a = counter[y], res = phi(m, a) + a - 1;
		for (i = a; primes[i] <= s; i++) res = res - Lehmer(m / primes[i]) + Lehmer(primes[i]) - 1;
		return res;
	}
}

