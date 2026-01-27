#define N 100
#define EMPTY
#define F() 3
#define G(...) (1, __VA_ARGS__)
#define H(X) +X
#define I(X,...) -X
#define J(X,Y) (X)+(Y)
#define K(X,Y,...) ((X)*(Y),__VA_ARGS__)
#define N 100
#define H(X) +X

char[N] buffer;

int x = EMPTY 0;

int y = F();

int z1 = G();
int z2 = G(i);
int z3 = G(a,b);
int z4 = G(a, b);
int z5 = G(a,        b);
int z6 = G((a,b));

H();
H(3);
H(5.7e88);
H(x);
H(+uu); // needs a space: + +uu
H(x+y);
H(H(7)); // needs a space: + +7

I(,);
I(3,);
I(5.7e88,);
I(x,);
I(+uu,);
I(x+y,);
I(0,lots of other stuff is ignored, including commas);

J(a, b);
J(a * b, a / b);
J(, 78);
J(87, );
J(,);
J(f(x,y), g(w));

K(a, b, );
K(a + b, a - b, );
K(, 78, );
K(87, , );
K(,,);
K(f(x,y), g(w), );
K(1, 2, 3);
K(1, 2, 3, 4);
