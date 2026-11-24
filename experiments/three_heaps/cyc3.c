/* three_heaps/cyc3.c — budgeted directed n-cycle on three heaps: node v plays Sub(S_v) on any heap, may push to v+1 (mod n).
   X_0(v) = P-set of Sub(S_v)^3 (no pushes left); X_k(v) = Phi_v(X_{k-1}(v+1)).
   Prints onset mu and period lambda of the sequence of joint states (X_k(0..n-1)), found by Brent's algorithm.
   usage: cyc3 N KMAX S0 S1 ... S_{n-1}      (n = 1 gives a self-loop) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static long M, V; static int n, S[8][16], ns[8];
static void phi(int v, const unsigned char *T, unsigned char *Y) {
  for (long a = 0; a < M; a++) for (long b = 0; b < M; b++) for (long c = 0; c < M; c++) {
    long x = (a * M + b) * M + c; int win = T ? T[x] : 0;
    for (int i = 0; i < ns[v] && !win; i++) { int s = S[v][i];
      if (s <= a && Y[x - s * M * M]) win = 1; else if (s <= b && Y[x - s * M]) win = 1; else if (s <= c && Y[x - s]) win = 1; }
    Y[x] = !win; } }
static void step(const unsigned char *X, unsigned char *Y) { for (int v = 0; v < n; v++) phi(v, X + ((v + 1) % n) * V, Y + v * V); }
int main(int argc, char **argv) {
  int N = atoi(argv[1]); long KMAX = atol(argv[2]); n = argc - 3; M = N + 1; V = M * M * M;
  for (int v = 0; v < n; v++) { char *t; ns[v] = 0; for (t = strtok(argv[3 + v], ","); t; t = strtok(0, ",")) S[v][ns[v]++] = atoi(t); }
  long W = n * V; unsigned char *x0 = malloc(W), *tort = malloc(W), *hare = malloc(W), *tmp = malloc(W);
  for (int v = 0; v < n; v++) phi(v, 0, x0 + v * V);
  /* Brent: find lambda */
  long power = 1, lam = 1; memcpy(tort, x0, W); step(x0, hare);
  while (memcmp(tort, hare, W)) {
    if (power == lam) { memcpy(tort, hare, W); power *= 2; lam = 0; }
    step(hare, tmp); memcpy(hare, tmp, W); lam++;
    if (power > KMAX) { printf("none %ld\n", KMAX); return 0; } }
  /* find mu */
  memcpy(tort, x0, W); memcpy(hare, x0, W);
  for (long i = 0; i < lam; i++) { step(hare, tmp); memcpy(hare, tmp, W); }
  long mu = 0; while (memcmp(tort, hare, W)) { step(tort, tmp); memcpy(tort, tmp, W); step(hare, tmp); memcpy(hare, tmp, W); mu++; }
  printf("%ld %ld\n", mu, lam); return 0; }
