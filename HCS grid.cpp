//This program runs "homotopic curve shortening" (HCS), with the integer grid
//as the set of obstacle points.

#include "pch.h"
#include <iostream>
#include <fstream>
#include <ctime>
#include <string>

using namespace std;

const double pi = acos(-1);

struct vertex
{
	long long x, y;
	double alpha;
	bool nailed;
	int Si; //index to vS, if present there, else -1
	vertex *p, *n;
};

//Stack of vertices:
const int Ssize = 500000;
vertex **vS = new vertex *[Ssize];
int nS;

void EGCD(long long, long long, long long *, long long *, long long *);
int orient(long long, long long, long long, long long, long long, long long);
void nextpt(long long, long long, long long, long long, long long, long long,
	long long *, long long *);
vertex *canonizechain(vertex *);
vertex *step(vertex *, bool, bool);
vertex *buildchain(int, long long *, long long *);
void checkchainandstack(vertex *);
void outputchainCscaled(vertex *, ostream &);
void outputchainmath(vertex *, ostream &);

vertex *initstar(double);

//Extended GCD:
//Given a, b, this function returns g=gcd(a,b) and m, n such that ma+nb=gcd(a,b)
void EGCD(long long a, long long b, long long *g, long long *m, long long *n)
{
	long long r = a, s = 1, t = 0, rr = b, ss = 0, tt = 1, rrr, sss, ttt, q;

	while (rr != 0)
	{
		q = r / rr;
		rrr = r - q * rr;
		sss = s - q * ss;
		ttt = t - q * tt;
		r = rr;
		rr = rrr;
		s = ss;
		ss = sss;
		t = tt;
		tt = ttt;
	}
	if (r < 0)
	{
		r = -r;
		s = -s;
		t = -t;
	}
	if (g != NULL)
		*g = r;
	if (m != NULL)
		*m = s;
	if (n != NULL)
		*n = t;
}

//Returns +1 if the path pqr makes a CCW turn at q; -1 if CW; 0 if straight or 180 degrees
int orient(long long px, long long py, long long qx, long long qy, long long rx, long long ry)
{
	long long det = qx * ry + rx * py + px * qy - qx * py - px * ry - rx * qy;
	if (det > 0)
		return 1;
	if (det < 0)
		return -1;
	return 0;
}

//Given three non-collinear points p, q, r such that q-p and r-q are primitive vectors, let L
//be the line parallel to pq that passes through grid points and is on the side of r, but
//as close as possible to pq (so for any point s on L, the triangle pqs has area 1/2).
//Let t be the grid point on L that is on the same side of the line qr as the point p, but
//as close as possible to qr. This function returns t
void nextpt(long long px, long long py, long long qx, long long qy, long long rx, long long ry,
	long long *tx, long long *ty)
{
	int ort = orient(px, py, qx, qy, rx, ry);
	if (ort == 0)
	{
		cout << "Error in nextpt: p,q,r collinear." << endl;
		exit(1);
	}
	long long s1 = ort * (px - qx), t1 = ort * (py - qy),
		s2, t2, s3 = rx - qx, t3 = ry - qy, k, g;
	EGCD(t1, -s1, &g, &s2, &t2);
	if (g != 1)
	{
		cout << "Error in nextpt: vector pq not primitive." << endl;
		exit(1);
	}
	double a = ((s2 + px - qx)*t3 - (t2 + py - qy)*s3) / ((double)(t1 * s3 - s1 * t3));
	if (ort == 1)
		k = (long long)ceil(a);
	else
		k = (long long)floor(a);
	*tx = s2 + px + k * s1;
	*ty = t2 + py + k * t1;
}

//Add intermediate vertices to non-primitive edges. Also remove repeated
//consecutive vertices:
vertex *canonizechain(vertex *v)
{
	vertex *w = v, *w2 = w->n, *w3;
	bool done = false;

	if (w2 == w)
		return v; //Chain has only one vertex

	while (!done)
	{
		if (w2 == v)
			done = true; //This is the last iteration of the loop

		//Remove zero or more vertices after w equal to w:
		while (w2 != w && w->x == w2->x && w->y == w2->y)
		{
			//w equals w2, so remove w2:
			w->n = w2->n;
			w->n->p = w;
			delete w2;
			w2 = w->n;
		}

		//Now w2 is the vertex after w.

		long long dx = w2->x - w->x, dy = w2->y - w->y, g;

		//Get the GCD:
		EGCD(dx, dy, &g, NULL, NULL);
		long long i;

		//Simplify the vector:
		dx /= g;
		dy /= g;

		//Insert intermediate vertices. (If GCD was 1 we will do nothing.)
		for (i = 1; i < g; i++)
		{
			w3 = new vertex;
			w3->x = w->x + dx;
			w3->y = w->y + dy;
			w->n = w3;
			w3->p = w;
			w3->n = w2;
			w2->p = w3;
			w = w3;
		}

		w = w2;
		w2 = w->n;
	}

	return w2;
}

//Returns the signed angle pqr (between -pi and pi)
double angle(long long px, long long py, long long qx, long long qy, long long rx,
	long long ry)
{
	double alpha1 = atan2(py - qy, px - qx), alpha2 = atan2(ry - qy, rx - qx),
		alpha = alpha2 - alpha1;
	if (alpha < -pi)
		alpha += 2 * pi;
	if (alpha > pi)
		alpha -= 2 * pi;
	return alpha;
}

//Technically we could just check whether abs(v->alpha)<pi. But we want
//to be robust against large buildup of inaccuracy:
bool unstable(vertex *v)
{
	if (abs(v->alpha) < 2 * pi / 3)
		return true;
	int ort = orient(v->p->x, v->p->y, v->x, v->y, v->n->x, v->n->y);
	return ((pi / 3 < v->alpha && v->alpha < 5 * pi / 3 && ort == -1)
		|| (-5 * pi / 3 < v->alpha && v->alpha < -pi / 3 && ort == 1));
}

//Adds a vertex to stack, if not already in there (as indicated by the vertex's Si):
void addtostack(vertex *v)
{
	if (v->Si >= 0)
		return; //already there
	if (nS >= Ssize)
	{
		cout << "vertex stack overflow" << endl;
		exit(1);
	}
	vS[nS] = v;
	v->Si = nS;
	nS++;
}

//This function assumes v is a vertex of the chain. It checks the p,n pointers,
//the Si indices, and the angles of the whole chain.
//It also checks the Si indices of all the vertices in the stack.
void checkchainandstack(vertex *v)
{
	if (nS < 0)
	{
		cout << "nS negative" << endl;
		exit(1);
	}

	vertex *w = v;
	do
	{
		if (w->Si < -1 || w->Si >= nS)
		{
			cout << "w = (" << w->x << "," << w->y << "): w->Si == "
				<< w->Si << " out of range" << endl;
			exit(1);
		}
		if (w->Si >= 0 && vS[w->Si] != w)
		{
			cout << "stack inconsistent" << endl;
			exit(1);
		}
		//Check that the difference between alpha and the angle at w is very
		//close to a muliple of 2*pi
		double ang = angle(w->p->x, w->p->y, w->x, w->y, w->n->x, w->n->y),
			diff = w->alpha - ang;
		if (abs(diff - 2 * pi*round(diff / (2 * pi))) > 0.0001)
		{
			cout << "problem with angles at (" << w->x << "," << w->y << "): alpha == "
				<< w->alpha << " angle == " << ang << endl;
			exit(1);
		}
		//Check p,n pointers:
		if (w->n->p != w || w->p->n != w)
		{
			cout << "p,n pointers no good." << endl;
			exit(1);
		}
		w = w->n;
	} while (w != v);

	int i;
	for (i = 0; i < nS; i++)
		if (vS[i]->Si != i)
		{
			cout << "error 2: stack inconsistent" << endl;
			exit(1);
		}
}

//We assume the input chain is "canonical": Every edge vector is primitive and non-(0,0).
//The output chain will also be canonical.
vertex *step(vertex *v, bool verbose = false, bool debug = false)
{
	vertex *w, *wp, *wn;

	wp = v;//because at the end we must return a vertex of the chain

	//Empty the stack:
	nS = 0;

	//Calculate the angles, set the nailed flags, add vertices to stack:
	w = v;
	do
	{
		w->alpha = angle(w->p->x, w->p->y, w->x, w->y, w->n->x, w->n->y);

		w->nailed = (w->n->x - w->x == w->x - w->p->x
			&& w->n->y - w->y == w->y - w->p->y);

		w->Si = -1;
		addtostack(w);

		w = w->n;
	} while (w != v);

	//Release vertices in stack until none are left:
	while (nS > 0)
	{
		if (debug)
			checkchainandstack(vS[nS - 1]);

		//Pop:
		nS--;
		w = vS[nS];

		if (verbose)
			cout << "popped (" << w->x << "," << w->y << ")" << endl;

		if (w->Si != nS)
		{
			cout << "error: nS == " << nS << "  while w->Si == " << w->Si << endl;
			exit(1);
		}
		w->Si = -1;

		if (w->nailed)
		{
			if (verbose)
				cout << "it's nailed." << endl;
			continue;
		}

		if (!unstable(w))
		{
			if (verbose)
				cout << "it's stable. angle = " << w->alpha / pi << " pi" << endl;
			continue;
		}

		wp = w->p;
		wn = w->n;

		if (wp == wn)//Only 2 vertices left in chain. Stop
		{
			if (verbose)
				cout << "2 or fewer vertices left" << endl;
			break;
		}

		if (wp->x == wn->x && wp->y == wn->y) //it's a u-turn
		{
			if (verbose)
				cout << "it's a u-turn" << endl;
			//Delete w and wn. Add wn's angle to wp.
			wp->alpha += wn->alpha;
			wp->n = wn->n;
			wn->n->p = wp;
			//If wn was nailed, pass the nail to wp:
			if (wn->nailed)
				wp->nailed = true;
			if (verbose)
				cout << "deleting (" << w->x << "," << w->y << ") and ("
				<< wn->x << "," << wn->y << ")" << endl;
			//Before we delete wn we have to make sure it's not in the stack, and if it is
			//to remove it from there:
			int i = wn->Si;
			if (i != -1)
			{
				if (i >= nS)
				{
					cout << "error: i == " << i << " while nS == " << nS << endl;
					exit(1);
				}
				if (verbose)
					cout << "wn was at position " << i
					<< " in the stack. Putting someone else there instead." << endl;
				nS--;
				vS[i] = vS[nS];
				vS[i]->Si = i;
			}
			delete w;
			delete wn;

			//Put wp back in the stack:
			addtostack(wp);
		}
		else //It's not a u-turn but a "regular" vertex release
		{
			//Put wp and wn back in the stack:
			addtostack(wp);
			addtostack(wn);

			long long x, y;

			while (1)
			{
				nextpt(wp->x, wp->y, w->x, w->y, wn->x, wn->y, &x, &y);
				if (x == wn->x && y == wn->y)
					break;
				vertex *z = new vertex;
				if (verbose)
					cout << "creating new vertex (" << x << "," << y << ")" << endl;
				z->x = x;
				z->y = y;
				z->p = wp;
				z->Si = -1;
				wp->n = z;
				z->nailed = false;
				z->alpha = angle(wp->x, wp->y, x, y, w->x, w->y);
				wp->alpha += angle(w->x, w->y, wp->x, wp->y, x, y);
				w->alpha -= angle(wp->x, wp->y, w->x, w->y, x, y);
				wp = z;
			}
			wp->alpha += angle(w->x, w->y, wp->x, wp->y, x, y);
			wn->alpha += angle(wp->x, wp->y, x, y, w->x, w->y);
			wp->n = wn;
			wn->p = wp;
			if (verbose)
				cout << "deleting (" << w->x << "," << w->y << ")" << endl;
			delete w;
		}//else.
	}//while nS>0.

	//At this point, in all cases, wp points to a vertex currently in the chain.
	return wp;
}

//Allocates and builds a chain with the given x- and y-coordinates.
vertex *buildchain(int n, long long *x, long long *y)
{
	if (n <= 0)
		return NULL;

	int i;
	vertex *firstv = new vertex, *lastv = firstv, *w;
	firstv->x = x[0];
	firstv->y = y[0];
	for (i = 1; i < n; i++)
	{
		w = new vertex;
		w->x = x[i];
		w->y = y[i];
		w->p = lastv;
		lastv->n = w;
		lastv = w;
	}
	lastv->n = firstv;
	firstv->p = lastv;
	return firstv;
}

//Returns the Euclidean length of the chain:
double length(vertex *v)
{
	vertex *w = v;
	double L = 0;
	do
	{
		double dx = w->n->x - w->x, dy = w->n->y - w->y;
		L += sqrt(dx * dx + dy * dy);
		w = w->n;
	} while (w != v);
	return L;
}

//Returns the number of vertices of the chain:
int nvtces(vertex *v)
{
	int i = 0;
	vertex *w = v;
	do
	{
		w = w->n;
		i++;
	} while (w != v);
	return i;
}

//Outputs the chain starting at the given vertex.
void outputchainCscaled(vertex *v, ostream &f, int scale)
{
	vertex *w = v;
	f << nvtces(v) + 1 << endl;
	do
	{
		f << (double)w->x / scale << " " << (double)w->y / scale << " ";
		w = w->n;
	} while (w != v);
	//Output first point again:
	f << (double)w->x / scale << " " << (double)w->y / scale;
	f << endl;
}

//Outputs the chain starting at the given vertex.
void outputchainmath(vertex *v, ostream &f)
{
	vertex *w = v;
	f << "{";
	while (1)
	{
		f << "{" << w->x << "," << w->y << "}";
		w = w->n;
		if (w == v)
			break;
		f << ",";
	}
	//Output first point again:
	f << ",{" << w->x << "," << w->y << "}";
	f << "}" << endl;
}

//Initializes to a star:
vertex *initstar(double k)
{

	long long x[10];
	long long y[10];
	int i;
	for (i = 0; i < 5; i++)
	{
		x[2 * i] = (long long)(k*cos(2 * pi*i / 5));
		y[2 * i] = (long long)(k*sin(2 * pi*i / 5));
		x[2 * i + 1] = (long long)(k * 4 * cos((2 * i + 1) * pi / 5));
		y[2 * i + 1] = (long long)(k * 4 * sin((2 * i + 1) * pi / 5));
	}
	return canonizechain(buildchain(10, x, y));
}

//Initializes to a random point sequence inside the square [0,max-1]*[0,max-1]
vertex *initrandom(int len, int max)
{
	long long *x = new long long[len], *y = new long long[len];
	int i;
	for (i = 0; i < len; i++)
	{
		x[i] = rand() % max;
		y[i] = rand() % max;
	}
	vertex *v = canonizechain(buildchain(len, x, y));

	delete[] x;
	delete[] y;

	return v;
}

//Two functions used by initspiral:
double spiralf(double x)
{
	return sqrt(x + 1) - 1;
}

double spiralfinv(double x)
{
	return (1 + x)*(1 + x) - 1;
}

//Initializes to a spiral
vertex *initspiral(int N, double k)
{
	long long *x = new long long[N], *y = new long long[N];
	int N1 = (int)(0.558*N), N2 = (int)(0.43*N), N3 = N - N1 - N2 - 1, i;
	double a;

	for (i = 0, a = spiralfinv(7 * pi); i < N1; i++, a -= spiralfinv(7 * pi) / N1)
	{
		x[i] = (long long)(-k * spiralf(a)*cos(spiralf(a)));
		y[i] = (long long)(-k * spiralf(a)*sin(spiralf(a)));
	}
	for (i = N1, a = 0; i <= N1 + N2; i++, a += spiralfinv(6 * pi) / N2)
	{
		x[i] = (long long)(k*spiralf(a)*cos(spiralf(a)));
		y[i] = (long long)(k*spiralf(a)*sin(spiralf(a)));
	}
	for (i = N1 + N2 + 1, a = pi * (1 - 1 / N3); i < N; i++, a -= pi / N3)
	{
		x[i] = (long long)(k*pi * (6.5 + 0.5*cos(a)));
		y[i] = (long long)(k*pi * 0.5*sin(a));
	}
	vertex *v = canonizechain(buildchain(N, x, y));

	delete[] x;
	delete[] y;

	return v;
}

vertex *initsquare(int k)
{
	long long x[4], y[4];
	x[0] = x[1] = 0;
	x[2] = x[3] = k;
	y[0] = y[3] = 0;
	y[1] = y[2] = k;
	return canonizechain(buildchain(4, x, y));
}

vertex *initinf(int N, double k)
{
	long long *x = new long long[N], *y = new long long[N];
	int N1 = (int)(3.*N / 4), N2 = N - N1, i;

	for (i = 0; i < N1; i++)
	{
		x[i] = (long long)(k*cos(2 * pi*i / N1));
		y[i] = (long long)(k*sin(2 * pi*i / N1)*sin(pi*i / N1));
	}
	for (i = N1; i < N; i++)
	{
		x[i] = (long long)(k*(4 - cos(2 * pi*(i - N1) / N2)) / 3);
		y[i] = (long long)(k * sin(2 * pi*(i - N1) / N2)*sin(pi*(i - N1) / N2) / 3);
	}
	vertex *v = canonizechain(buildchain(N, x, y));

	delete[] x;
	delete[] y;

	return v;
}

//
vertex *initcamelfish(int k)
{
	const double xx[8] = { 0., 0.16, 0.4, 0.64, 0.94, 1., 0.56, 0.52 };
	const double yy[8] = { 0., 0.81, 0.45, 1., 0.3, 0.45, 0.07, 0.13 };
	long long x[8], y[8];
	int i;
	for (i = 0; i < 8; i++)
	{
		x[i] = k * xx[i];
		y[i] = k * yy[i];
	}
	return canonizechain(buildchain(8, x, y));
}

//If, for example, we want to print when the length reaches 95%, 90%, and 85%, then we should
//set nparts to 20 (because 100% / 20 = 5%) and printparts to 3.
void run_length(vertex *v, int nparts, int printparts, string name, int outscale)
{
	clock_t runt0 = clock(), runt1;
	ofstream fmath, fc;

	fmath.open(name + " math.txt");
	fc.open(name + " C.txt");
	fmath << name.c_str() << "chains = {" << endl;
	outputchainmath(v, fmath);
	outputchainCscaled(v, fc, outscale);

	int i = 0;
	double initial_length = length(v), curr_length;
	const int ievery = 1000;
	int pr = 1;
	while (v->p != v->n && pr <= printparts)
	{
		v = step(v, false, false);
		i++;
		curr_length = length(v);
		if (curr_length <= initial_length * (nparts - pr) / nparts)
		{
			fmath << "," << endl;
			outputchainmath(v, fmath);
			outputchainCscaled(v, fc, outscale);
			cout << 100 * (nparts - pr) / nparts << "% perimeter. i = " << i << endl;
			pr++;
		}

		if (i%ievery == 0)
			cout << "i == " << i << endl;
	};
	fmath << "};" << endl;
	fmath.close();
	fc << "0" << endl;
	fc.close();

	runt1 = clock();
	cout << "Running time: " << ((double)runt1 - runt0) / CLOCKS_PER_SEC << " s." << endl;
}

int main()
{
	vertex *v;

	const int scale = 31622; //100, 316, 1000, 3162, 10000, 31622, 100000, 316227
	v = initcamelfish(scale);
	string name = "camelfish";
	name = name + to_string(scale);

	run_length(v, 50, 15, name.c_str(), scale);
}
