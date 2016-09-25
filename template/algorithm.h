
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

//整体二分。。。
const int N = 1 << 20;
struct tree_array //[1, n]
{
	typedef long long type;
	type S[N + 10], n;
	void clear(int n) {
		this->n = n;
		REP (i, n) S[i] = type();
	}
	void add(int i, type a) {
		for (;i <= n; i += i & (-i)) S[i] += a;
	}
	type sum(int i) {
		type x = type();
		for (; i > 0; i -= i & (-i)) x += S[i];
		return x;
	}
	type sum(int l, int r) { return sum(r) - sum(l - 1); }
	type get(int i) { return sum(i) - sum(i - 1); }
	void set(int i, type a) { add(i, a - get(i)); }
};
struct query {
	int q, r, ans, i;
	bool operator<(query b)const { return i < b.i; }
} q[N], ql[N], qr[N];
int t[N];
tree_array sum, cnt;
void solve(int ll, int mm, int rr, int l, int r) {
	if (l == r) return;
	FOR (i, ll, mm) {
		sum.add(t[i], t[i]);
		cnt.add(t[i], 1);
	}
	int nl = 0, nr = 0;
	FOR (i, l, r) {
		long long cur = sum.sum(q[i].q, N) - cnt.sum(q[i].q, N) * q[i].q;
		if (q[i].r <= cur) ql[nl++] = q[i]; else qr[nr++] = q[i];
	}
	int m = l + nl;
	REP (i, nl) q[l + i] = ql[i];
	REP (i, nr) q[m + i] = qr[i];
	if (rr - ll <= 1) {
		FOR (i, l, r) q[i].ans = rr;
	} else {
		if (mm < rr) {
			solve(mm, (mm + rr) / 2, rr, m, r);
		}
		FOR (i, ll, mm) {
			sum.add(t[i], -t[i]);
			cnt.add(t[i], -1);
		}
		if (ll < mm) {
			solve(ll, (ll + mm) / 2, mm, l, m);
		}
	}
}


#include <complex>
using namespace std;
typedef complex<double> comp;
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

//fast than fft and ntt when type is integer
struct multiply {
	typedef int64 type;
	type poor[N]; int id;
	void add(type x[], type y[], int n) {
		REP (i, n) x[i] += y[i];
	}
	void sub(type x[], type y[], int n) {
		REP (i, n) x[i] -= y[i];
	}
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
} MUL;


