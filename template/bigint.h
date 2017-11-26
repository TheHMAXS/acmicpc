#include <template.h>

struct ubigint
{
	static const int base = 10;
	static const int mod = 10000;
	static const int k = 4;
	vector<int> data;
	size_t size()const {
		return data.size();
	}
	int& operator[](size_t i) {
		return data[i];
	}
	const int& operator[](size_t i)const {
		return data[i];
	}
	ubigint& trim() {
		while (!data.empty() && data.back() == 0) data.pop_back();
		return *this;
	}
	ubigint(uint64 val = 0) {
		while (val != 0) {
			data.push_back(val % mod);
			val /= mod;
		}
	}
	ubigint(const string& val) {
		data.resize(val.size() / k + 1);
		REP (i, val.size()) {
			int p = (val.size() - i - 1) / k;
			data[p] = data[p] * base + val[i] - '0';
		}
		trim();
	}
	string text()const {
		string val;
		REP (i, size()) {
			int x = data[i];
			REP (j, k) {
				val += (char)('0' + x % base);
				x /= base;
			}
		}

		size_t i = 0;
		if (size() == 0) return "0";
		reverse(val.begin(), val.end());
		while (i < val.size() && val[i] == '0') i++;
		return val.substr(i);
	}
	friend istream& operator>>(istream& in, ubigint& x) {
		string s; in >> s; x = s;
		return in;
	}
	friend ostream& operator<<(ostream& out, const ubigint& x) {
		return out << x.text();
	}

	ubigint& operator+=(const ubigint& b) {
		data.resize(max(size(), b.size()) + 1);
		REP (i, b.size()) {
			data[i] += b[i];
			if (data[i] >= mod) {
				data[i] -= mod;
				data[i + 1]++;
			}
		}
		return trim();
	}
	ubigint& operator-=(const ubigint& b) {
		REP (i, b.size()) {
			data[i] -= b[i];
			if (data[i] < 0) {
				data[i] += mod;
				data[i + 1]--;
			}
		}
		return trim();
	}
	friend ubigint operator+(ubigint a, const ubigint& b) {
		return a += b;
	}
	friend ubigint operator-(ubigint a, const ubigint& b) {
		return a -= b;
	}


	friend int cmp(const ubigint& a, const ubigint& b) {
		if (a.size() != b.size()) {
			return a.size() < b.size() ? -1 : 1;
		}
		DWN (i, a.size()) if (a[i] != b[i]) {
			return a[i] < b[i] ? -1 : 1;
		}
		return 0;
	}
	friend bool operator< (const ubigint& a, const ubigint& b) {
		return cmp(a, b) < 0;
	}
	friend bool operator> (const ubigint& a, const ubigint& b) {
		return cmp(a, b) > 0;
	}
	friend bool operator<=(const ubigint& a, const ubigint& b) {
		return cmp(a, b) <= 0;
	}
	friend bool operator>=(const ubigint& a, const ubigint& b) {
		return cmp(a, b) >= 0;
	}
	friend bool operator==(const ubigint& a, const ubigint& b) {
		return cmp(a, b) == 0;
	}
	friend bool operator!=(const ubigint& a, const ubigint& b) {
		return cmp(a, b) != 0;
	}


	friend ubigint operator*(const ubigint& a, const ubigint& b) {
		ubigint r;
		r.data.resize(a.size() + b.size());
		REP (i, a.size()) REP (j, b.size()) {
			r[i + j] += a[i] * b[j];
			for (int k = i + j; r[k] >= mod; k++) {
				r[k + 1] += r[k] / mod;
				r[k] %= mod;
			}
		}
		return r.trim();
	}
	ubigint& operator*=(ubigint b) {
		return *this = *this * b;
	}


	template<class T> ubigint& mul_(T b) {
		T r = 0;
		data.resize(data.size() + 22 / k);
		REP (i, data.size()) {
			r += b * data[i];
			data[i] = r % mod;
			r /= mod;
		}
		return trim();
	}
	template<class T> T divmod_(T b) {
		T r = 0;
		DWN (i, data.size()) {
			r = r * mod + data[i];
			data[i] = r / b;
			r -= data[i] * b;
		}
		trim();
		return r;
	}
	ubigint divmod(const ubigint& b) {
		int n = b.size();
		assert(n > 0);
		if (n == 1) return divmod_(b[0]);
		uint64 y = b[n - 1] * mod + b[n - 2];
		if (n == 2) return divmod_(y);

		ubigint r;
		int p = min(n - 1, (int)size());
		r.data.assign(data.end() - p, data.end());
		data.erase(data.end() - p, data.end());
		DWN (i, size()) {
			r.data.insert(r.data.begin(), data[i]);
			uint64 x = 0;
			for (int i = r.size() - 1; i >= n - 2; i--)
				x = x * mod + r[i];
			data[i] = x / (y + 1);
			ubigint cur = ubigint(b).mul_(data[i]);
			while ((cur += b) <= r) data[i]++;
			r -= (cur -= b);
		}
		trim();
		return r;
	}
	friend ubigint operator/(ubigint a, const ubigint& b) {
		a.divmod(b); return a;
	}
	friend ubigint operator%(ubigint a, const ubigint& b) {
		return a.divmod(b);
	}
	ubigint& operator/=(ubigint b) {
		return *this = *this / b;
	}
	ubigint& operator%=(ubigint b) {
		return *this = *this % b;
	}
	unsigned operator%(unsigned b)const {
		uint64 r = 0;
		DWN(i, size()) r = (r * mod + data[i]) % b;
		return r;
	}
	unsigned short operator%(unsigned short b)const {
		unsigned r = 0;
		DWN(i, size()) r = (r * mod + data[i]) % b;
		return r;
	}
};

struct bigint
{
	bool neg; ubigint val;
	bigint& norm() {
		if (val.trim() == 0) neg = false;
		return &this;
	}
	bigint(int64 val = 0): neg(val < 0), val(abs(val)) {}
	bigint(const ubigint& val, bool neg = false):
		val(val), neg(false) { norm(); }
	bigint(const string& s) {
		if (!s.empty() && (s[0] == '-' || s[0] == '+')) val = s.substr(1);
		else val = s;
		neg = !s.empty() && s[0] == '-';
	}
	string text()const {
		return (neg ? '-' : "") + val.text();
	}
	friend istream& operator>>(istream& in, bigint& x) {
		string s; in >> s; x = s;
		return in;
	}
	friend ostream& operator<<(ostream& out, const bigint& x) {
		return out << x.text();
	}

	friend ubigint abs(bigint a) {
		return a.val;
	}
	bigint operator-() {
		return bigint(val, !neg).norm();
	}
	bigint& operator+=(const bigint& b) {
		if (neg == b.neg) val += b.val;
		else if (val > b.val) val -= b.val;
		else { val = b.val - val; neg = !neg; }
		return norm();
	}
	bigint& operator-=(const bigint& b) {
		return *this += -b;
	}
	friend bigint operator+(bigint a, const bigint& b) {
		return a += b;
	}
	friend bigint operator-(bigint a, const bigint& b) {
		return a -= b;
	}

	friend int cmp(const bigint& a, const bigint& b) {
		if (a.neg != b.neg) return a.neg ? -1 : 1;
		return a.neg ? -cmp(a, b) : cmp(a, b);
	}
	friend bool operator< (const bigint a, const bigint b) {
		return cmp(a, b) < 0;
	}
	friend bool operator> (const bigint a, const bigint b) {
		return cmp(a, b) > 0;
	}
	friend bool operator<=(const bigint a, const bigint b) {
		return cmp(a, b) <= 0;
	}
	friend bool operator>=(const bigint a, const bigint b) {
		return cmp(a, b) >= 0;
	}
	friend bool operator==(const bigint a, const bigint b) {
		return cmp(a, b) == 0;
	}
	friend bool operator!=(const bigint a, const bigint b) {
		return cmp(a, b) != 0;
	}

	friend bigint operator*(const bigint& a, const bigint& b) {
		return bigint(a.val * b.val, a.neg != b.neg).norm();
	}
	bigint& operator*=(const bigint& b) {
		return *this = *this * b;
	}

	bigint divmod(bigint b) {
		bigint m(val.divmod(b.val), neg);
		this->neg = neg != b.neg;
		return m.norm();
	}
	friend bigint operator/(bigint a, const bigint& b) {
		a.divmod(b); return a;
	}
	friend ubigint operator%(bigint a, const bigint& b) {
		return a.divmod(b);
	}
	bigint& operator/=(bigint b) {
		return *this = *this / b;
	}
	bigint& operator%=(bigint b) {
		return *this = *this % b;
	}
	int operator%(int b)const {
		int r = val % (unsigned)abs(b);
		return neg ? -r : r;
	}
	short operator%(short b)const {
		int r = val % (unsigned short)abs(b);
		return neg ? -r : r;
	}
};

int hdu1002() {
	int ncase; cin >> ncase;
	REP (icase, ncase) {
		ubigint a, b; cin >> a >> b;
		cout << "Case " << icase + 1 << ":" << endl;
		cout << a << " + " << b << " = " << a + b << endl;
		if (a != 0 && b != 0) {
			if (a + b - b != a) cout << "error1";
			if (a * b / a != b) cout << "error2";
			b += a;
			if ((a * b + a) % b != a) cout << "error3";
			if ((a * b + 1) % b != 1) cout << "error4";
			if ((a * b + 0) % b != 0) cout << "error5";
			if ((a * b - 1) % b != b - 1) cout << "error6";
		}
		if (icase != ncase - 1) cout << endl;
	}
	return 0;
}

int hdu5050() {
	int ncase; cin >> ncase;
	REP (icase, ncase) {
		//also can change base to 2;
		string a, b, c;
		ubigint x, y, z;
		cin >> a >> b;
		REP (i, a.size()) x = x * 2 + a[i] - '0';
		REP (i, b.size()) y = y * 2 + b[i] - '0';
		z = gcd(x, y);
		while (z != 0) {
			c += (z % 2 + '0');
			z /= 2;
		}
		reverse(c.begin(), c.end());
		cout << "Case #" << icase + 1 << ": " << c << endl;
	}
	return 0;
}


