#include "ac_int.h"

// RAC begin

//typedef int a[4 + 2];
//typedef int b[4 - 2];
//typedef int c[4 * 2];
//typedef int d[4 / 2];
//typedef int e[4 % 2];
//typedef int f[4 << 2];
//typedef int g[4 >> 2];
////typedef int h[4 & 2];
////typedef int i[4 | 2];
//typedef int j[4 < 2];
//typedef int k[4 > 2];
//typedef int l[4 <= 2];
//typedef int m[4 >= 2];
//typedef int n[4 == 2];
//typedef int l[4 != 2];
//typedef int o[4 && 2];
//typedef int p[4 || 2];

enum NUMS_EXPR 
{
  A = 3 + 4,
  B = 3 - 4,
  C = 3 * 4,
  D = 3 / 4,
  E = 3 % 4,
  F = 3 << 4,
  G = 3 >> 4,
  H = 3 & 4,
  I = 3 ^ 4,
  J = 3 | 4,
  K = 3 < 4,
  L = 3 > 4,
  M = 3 <= 4,
  N = 3 >= 4,
  O = 3 == 4,
  P = 3 != 4,
  Q = 3 && 4,
  Q2 = 0 && 4,
  Q3 = 3 && 0,
  R = 3 || 4,
  R2 = 0 || 4,
  R3 = 3 || 0,
  UNARY = +3,
  UNARY2 = -(3), // Force unary operator instead of parsing "-3"
  UNARY3 = ~3,
  UNARY4 = ! 3
};

int a_val() { return A; }
int b_val() { return B; }
int c_val() { return C; }
int d_val() { return D; }
int e_val() { return E; }
int f_val() { return F; }
int g_val() { return G; }
int h_val() { return H; }
int i_val() { return I; }
int j_val() { return J; }
int k_val() { return K; }
int l_val() { return L; }
int m_val() { return M; }
int n_val() { return N; }
int o_val() { return O; }
int p_val() { return P; }
int q_val() { return Q; }
int q2_val() { return Q2; }
int q3_val() { return Q3; }
int r_val() { return R; }
int r2_val() { return R2; }
int r3_val() { return R3; }
int unary_val() { return UNARY; }
int unary2_val() { return UNARY2; }
int unary3_val() { return UNARY3; }
int unary4_val() { return UNARY4; }

// RAC end
