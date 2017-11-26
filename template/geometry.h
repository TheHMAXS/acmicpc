#include "template.h"

typedef int type;
struct point {
	type x, y;
	point(): x(), y() {}
	point(type x, type y): x(x), y(y) {}
	point operator*(type b)const {
		return point(x * b, y * b);
	}
	point operator/(type b)const {
		return point(x / b, y / b);
	}
	point operator-()const {
		return point(-x, -y);
	}
	friend point operator+(point a, point b) {
		return point(a.x + b.x, a.y + b.y);
	}
	friend point operator-(point a, point b) {
		return point(a.x - b.x, a.y - b.y);
	}
	friend type operator*(point a, point b) {
		return a.x * b.x + a.y * b.y;
	}
	friend type operator/(point a, point b) {
		return a.x * b.y - a.y * b.x;
	}
	friend bool operator<(point a, point b) {
		return a.x == b.x ? a.y < b.y : a.x < b.x;
	}
	friend bool operator>(point a, point b) {
		return a.x == b.x ? a.y > b.y : a.x > b.x;
	}
	friend bool operator==(point a, point b) {
		return a.x == b.x && a.y == b.y;
	}
	friend bool operator!=(point a, point b) {
		return a.x != b.x || a.y != b.y;
	}
};

int sign(int x) {
	return x < 0 ? -1 : x > 0 ? 1 : 0;
}

struct line {
	point a, b;
	line(point a, point b): a(a), b(b) {}
	int side(point c)const {
		return sign((b - a) / (c - a));
	}
	bool has(point c)const {
		return side(c) == 0 && sign((c - a) * (c - b)) <= 0;
	}
	friend bool parrel(line l1, line l2) {
		return (l1.b - l1.a) / (l2.b - l2.a) == 0;
	}
	//ab ^ cd not parrel!
	friend bool cross(line l1, line l2) {
		return !parrel(l1, l2) &&
				l1.side(l2.a) * l1.side(l2.b) <= 0 &&
				l2.side(l1.a) * l2.side(l1.b) <= 0;
	}
};

int convex(point P[N], int n) {
	sort(P, P + n);
	int m = 1;
	for (int i = 1; i < n; i++) {
		while (m > 1 && line(P[m - 2], P[m - 1]).side(P[i]) > 0) m--;
		swap(P[m++], P[i]);
	}
	int l = m - 1;
	sort(P + m, P + n, std::greater<point>());
	for (int i = m; i < n; i++) {
		while (m - l > 1 && line(P[m - 2], P[m - 1]).side(P[i]) > 0) m--;
		swap(P[m++], P[i]);
	}
	while (m - l > 1 && line(P[m - 2], P[m - 1]).side(P[0]) > 0) m--;
	return m;
}

bool on(point P[N], int n, point q) {
	REP (i, n) {
		line l(P[i], P[(i + 1) % n]);
		if (l.has(q)) return true;
	}
	return false;
}
bool in(point P[N], int n, point q) {
	if (on(P, n, q)) return false;
	type x = P[0].x;
	REP (i, n) x = min(x, P[i].x);
	line h(point(x - 1, q.y), q);
	int cnt = 0;
	REP (i, n) {
		line l(P[i], P[(i + 1) % n]);
		if (cross(l, h) && min(l.a.y, l.b.y) != q.y) cnt++;
	}
	return cnt % 2 == 1;
}


