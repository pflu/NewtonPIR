#include <iostream>
#include <NTL/ZZ.h>
#include <vector>
#include <time.h>

#define BITSIZE 1024

using namespace std;
using namespace NTL;


void KeyGen(int lambda, ZZ& n, ZZ& p, ZZ& q, ZZ& phin, ZZ& d, ZZ& a, ZZ& b, ZZ& u, ZZ& v) {
	// generate p and q with lambda/2 bits and gcd(p-1, 3) = 1, gcd(q-1, 3) = 1
	GenPrime(p, lambda/2);
	while((p - 1) % 3 != 1)
		NextPrime(p, p + 1);
	GenPrime(q, lambda/2);
	while((q - 1) % 3 != 1 || p == q)
		NextPrime(q, q + 1);
		
	n = p * q;
	phin = (p - 1) * (q - 1);
		
	// generate random a and b between 0 and n - 1
	RandomBnd(a, n);
	RandomBnd(b, n);
	
	// u = a^3 mod n, v = b^3 mod n
	u = (a * a) % n;
	u = (u * a) % n;
	v = (b * b) % n;
	v = (v * b) % n;
	
	// compute d = 3^{-1} mod n
	ZZ e(3);
	InvMod(d, e, n);
	
	cout << "p = " << p << endl;
	cout << "q = " << q << endl;
	cout << "n = " << n << endl;
	cout << "phi(n) = " << phin << endl;
	cout << "d = " << d << endl;
	cout << "a = " << a << endl;
	cout << "b = " << b << endl;
	cout << "u = " << u << endl;
	cout << "v = " << v << endl;
}

void Enc(vector<vector<ZZ> >& ctxt, ZZ& n, ZZ& a, ZZ& b, const ZZ& m) {
	// generate random a_{ij} for i,j = 0,1,2
	for(int i = 0; i < 3; i++)
		for(int j = 0; j < 3; j++)
			RandomBnd(ctxt[i][j], n);
	// compute f(a, b)
	ZZ fab(0);
	ZZ ab = (a * b) % n; 
	ZZ a2b = (ab * a) % n;
	ZZ b2 = (b * b) % n;
	ZZ a2 = (a * a) % n;
	ZZ ab2 = (ab * b) % n;
	ZZ a2b2 = (ab * ab) % n;
	fab += ctxt[0][0];
	fab = (fab + ctxt[0][1] * b) % n;
	fab = (fab + ctxt[1][0] * a) % n;
	fab = (fab + ctxt[1][1] * ab) % n;
	fab = (fab + ctxt[0][2] * b2) % n;
	fab = (fab + ctxt[2][0] * a2) % n;
	fab = (fab + ctxt[1][2] * ab2) % n;
	fab = (fab + ctxt[2][1] * a2b) % n;
	fab = (fab + ctxt[2][2] * a2b2) % n;

	ctxt[0][0] = (ctxt[0][0] - fab) % n;
	ctxt[0][0] = (ctxt[0][0] + m) % n;
}

void Dec(ZZ& m, vector<vector<ZZ> >& ctxt, const ZZ& a, const ZZ& b, const ZZ& n) {
	// compute m = ctxt(a,b)
	m = ctxt[0][0];
	ZZ ab = (a * b) % n; 
	ZZ a2b = (ab * a) % n;
	ZZ b2 = (b * b) % n;
	ZZ a2 = (a * a) % n;
	ZZ ab2 = (ab * b) % n;
	ZZ a2b2 = (ab * ab) % n;

	m = (m + ctxt[0][1] * b) % n;
	m = (m + ctxt[1][0] * a) % n;
	m = (m + ctxt[1][1] * ab) % n;
	m = (m + ctxt[0][2] * b2) % n;
	m = (m + ctxt[2][0] * a2) % n;
	m = (m + ctxt[1][2] * ab2) % n;
	m = (m + ctxt[2][1] * a2b) % n;
	m = (m + ctxt[2][2] * a2b2) % n;
}

void mul_mod(vector<vector<ZZ> >& res, const vector<vector<ZZ> >& a, const vector<vector<ZZ> >& b, const ZZ& n, const ZZ& u, const ZZ& v) {  // res = a * b mod n, mod x^3-u, mod y^3-v
	ZZ temp;
 	int index1 = 0;
 	int index2 = 0;
	vector<vector<ZZ> > restmp(3);
 	for(int i = 0; i < 3; i++) {
		restmp[i] = vector<ZZ>(3);
	}
   
	for(int i = 0; i < 3; i++) {
  		for(int j = 0; j < 3; j++) {
   			// a * b_{ij}x^iy^j mod n, mod x^3-u, mod y^3-v
   			for(int k = 0; k < 3; k++) {
    				for(int l = 0; l < 3; l++) {
     					temp = (a[k][l] * b[i][j]) % n;

     					// mod x^3 - u   mod y^3 - v
     					index1 = k + i;
     					index2 = l + j;
     					if(index1 >= 3) {
      						index1 -= 3;
      						temp = (temp * u) % n;
     					}
     					if(index2 >= 3) {
      						index2 -= 3;
      						temp = (temp * v) % n;
     					}
						
     					restmp[index1][index2] += temp;
     					restmp[index1][index2] %= n;
    				}
   			}
  		}
 	}
	for(int i = 0; i < 3; i++)
		for(int j = 0; j < 3; j++)
			res[i][j] = restmp[i][j];
}

void Eval(vector<vector<ZZ> >& res, const vector<ZZ>& poly, vector<vector<ZZ> >& ctxt, const ZZ& n, const ZZ& u, const ZZ& v) {
	int deg = poly.size() - 1;
	if(deg == 0) {
		for(int i = 0; i < 3; i++)
			for(int j = 0; j < 3; j++)
				res[i][j] = 0;
		res[0][0] = poly[0] % n;
		return;
	}
	// deg >= 1
	for(int i = 0; i < 3; i++) {
		for(int j = 0; j < 3; j++) {
			res[i][j] = (poly[deg] * ctxt[i][j]) % n;
		}
	}
	for(int i = deg - 1; i > 0; i--) {
		res[0][0] = (res[0][0] + poly[i]) % n;
		mul_mod(res, res, ctxt, n, u, v);
	}
	res[0][0] = (res[0][0] + poly[0]) % n; 
}

void PreCom(vector<ZZ>& newton, const vector<ZZ>& data) {
	int size = data.size();
	vector<ZZ> temp(size);
	for(int i = 0; i < size; i++) {
		temp[i] = 0;
	}

	for(int i = 0 ; i < size; i++) {
		newton[i] = data[i];
	}

	for(int j = 1; j < size; j++) {
		for(int i = j; i < size; i++) {
			temp[i] = (newton[i] - newton[i - 1]) / (j);
		}
		for(int i = j; i < size; i++) {
			newton[i] = temp[i];
		}
	}
}

void Newton(vector<vector<ZZ> >& res, vector<vector<ZZ> >& ctxt, const vector<ZZ>& coeff, const vector<ZZ>& points, ZZ& n, ZZ& u, ZZ& v) {			// Newton interpolation
	int s = points.size();
	// compute coeff[0] + coeff[1] * (ctxt - points[0]) + coeff[2] * (ctxt - points[0]) * (ctxt - points[1]) * ...
	vector<vector<ZZ> > restmp(3);
	vector<vector<ZZ> > temp(3);
	for(int i = 0; i < 3; i++) {
		restmp[i] = vector<ZZ>(3);
		temp[i] = vector<ZZ>(3);
	}
			
	for(int i = 0; i < 3; i++)
		for(int j = 0; j < 3; j++) {
			restmp[i][j] = 0;
			temp[i][j] = 0;
		}
			
	restmp[0][0] = coeff[0];
	temp[0][0] = 1;
	for(int i = 0; i < s; i++) {
		// compute temp * (ctxt - points[i])
		ctxt[0][0] = (ctxt[0][0] - points[i]) % n;
		mul_mod(temp, temp, ctxt, n, u, v);
		ctxt[0][0] = (ctxt[0][0] + points[i]) % n;
		// compute restmp + coeff[i + 1] * temp
		for(int k = 0; k  < 3; k++) {
			for(int j = 0; j < 3; j++) {
				restmp[k][j] = (restmp[k][j] + coeff[i + 1] * temp[k][j]) % n;
			}
		}
	}

	for(int i = 0; i < 3; i++)
		for(int j = 0; j < 3; j++)
			res[i][j] = restmp[i][j];
}

int main() {
	clock_t start, end;
	int lambda = 2048;
	ZZ n, p, q, phin, d, a, b, u, v;
	KeyGen(lambda, n, p, q, phin, d, a, b, u, v);
	ZZ m(300);
	vector<vector<ZZ> > ctxt(3);
	for(int i = 0; i < 3; i++) {
		ctxt[i] = vector<ZZ>(3);
	}

	vector<vector<ZZ> > ceva(3);
	for(int i = 0; i < 3; i++) {
		ceva[i] = vector<ZZ>(3);
	}

	Enc(ctxt, n, a, b, m);
	Dec(m, ctxt, a, b, n);
	cout << m << endl;

	vector<ZZ> poly(3);
	poly[0] = 2;
	poly[1] = 1;
	poly[2] = 1;		// x^2
	Eval(ceva, poly, ctxt, n, u, v);
	Dec(m, ceva, a, b, n);
	cout << m << endl;
	

	for(int t = 1; t <= 10; t++) {
		int size = 1000 * t;
		m = 10;
		start = clock();
		Enc(ctxt, n, a, b, m);
		end = clock();
		cout << "Encryption time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl;

		vector<ZZ> data(size + 1);
		vector<ZZ> coeff(size + 1);
		vector<ZZ> points(size);
		for(int i = 0; i < size; i++) {
			RandomBits(data[i], BITSIZE);
			points[i] = i;
		}
		RandomBits(data[size], BITSIZE);

		start = clock();
		PreCom(coeff, data);
		end = clock();
		cout << "Precomputation time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl; 
		for(int i = 0; i <= size; i++)
			coeff[i] = data[i];
		
		start = clock();
		Newton(ceva, ctxt, coeff, points, n, u, v);
		end = clock();
		cout << "Newton interpolation time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl;

		start = clock();
		Dec(m, ceva, a, b, n);
		end = clock();
		cout << "Decryption time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl;
		cout << endl;
	}

	for(int t = 1; t <= 10; t++) {
		int size = 10000 * t;
		m = 10;
		start = clock();
		Enc(ctxt, n, a, b, m);
		end = clock();
		cout << "Encryption time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl;

		vector<ZZ> data(size + 1);
		vector<ZZ> coeff(size + 1);
		vector<ZZ> points(size);
		for(int i = 0; i < size; i++) {
			RandomBits(data[i], BITSIZE);
			points[i] = i;
		}
		RandomBits(data[size], BITSIZE);

		start = clock();
		PreCom(coeff, data);
		end = clock();
		cout << "Precomputation time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl; 
		for(int i = 0; i <= size; i++)
			coeff[i] = data[i];
		
		start = clock();
		Newton(ceva, ctxt, coeff, points, n, u, v);
		end = clock();
		cout << "Newton interpolation time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl;

		start = clock();
		Dec(m, ceva, a, b, n);
		end = clock();
		cout << "Decryption time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl;
		cout << endl;
	}

	for(int t = 1; t <= 10; t++) {
		int size = 100000 * t;
		m = 10;
		start = clock();
		Enc(ctxt, n, a, b, m);
		end = clock();
		cout << "Encryption time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl;

		vector<ZZ> data(size + 1);
		vector<ZZ> coeff(size + 1);
		vector<ZZ> points(size);
		for(int i = 0; i < size; i++) {
			RandomBits(data[i], BITSIZE);
			points[i] = i;
		}
		RandomBits(data[size], BITSIZE);

		start = clock();
		PreCom(coeff, data);
		end = clock();
		cout << "Precomputation time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl; 
		for(int i = 0; i <= size; i++)
			coeff[i] = data[i];
		
		start = clock();
		Newton(ceva, ctxt, coeff, points, n, u, v);
		end = clock();
		cout << "Newton interpolation time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl;

		start = clock();
		Dec(m, ceva, a, b, n);
		end = clock();
		cout << "Decryption time for " << size << " items : " << (double)(end - start) / CLOCKS_PER_SEC << endl;
		cout << endl;
	}
}	
