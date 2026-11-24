/* three_heaps/chain3.c — chain of nodes on three heaps.
   usage: chain3 N OUT S1 S2 ... Sk   (each Si a csv subtraction set; '+' joins sets into a fork target union
          at the LAST position only is not supported; forks are handled in Python via the tail law)
   Node k (last) = Sub(Sk)^3 with no push: P iff g_k(a)^g_k(b)^g_k(c)==0.
   Node i<k: P-set Phi_i(X_{i+1}): x is N if x in X_{i+1} (push wins) or some Sub(Si) move reaches a P cell.
   Writes (N+1)^3 bytes, index (a*(N+1)+b)*(N+1)+c, 1 = P, for node 1. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int parse(char *s, int *S) { int n = 0; char *t; for (t = strtok(s, ","); t; t = strtok(0, ",")) S[n++] = atoi(t); return n; }
int main(int argc, char **argv) {
  int N = atoi(argv[1]); int k = argc - 3; long M = N + 1, V = M * M * M;
  int S[16][16], n[16];
  for (int i = 0; i < k; i++) n[i] = parse(argv[3 + i], S[i]);
  unsigned char *X = malloc(V), *Y = malloc(V);
  int *g = malloc(sizeof(int) * M);
  { int *Sl = S[k - 1], nl = n[k - 1];
    for (int h = 0; h <= N; h++) { unsigned long long seen = 0; for (int i = 0; i < nl; i++) if (Sl[i] <= h) seen |= 1ULL << g[h - Sl[i]]; int m = 0; while (seen >> m & 1) m++; g[h] = m; }
    for (int a = 0; a <= N; a++) for (int b = 0; b <= N; b++) for (int c = 0; c <= N; c++) X[(a * M + b) * M + c] = ((g[a] ^ g[b] ^ g[c]) == 0); }
  for (int j = k - 2; j >= 0; j--) {
    int *Sj = S[j], nj = n[j];
    for (int a = 0; a <= N; a++) for (int b = 0; b <= N; b++) for (int c = 0; c <= N; c++) {
      long x = (a * M + b) * M + c; int win = X[x];
      for (int i = 0; i < nj && !win; i++) { int s = Sj[i];
        if (s <= a && Y[x - s * M * M]) win = 1;
        else if (s <= b && Y[x - s * M]) win = 1;
        else if (s <= c && Y[x - s]) win = 1; }
      Y[x] = !win; }
    unsigned char *t = X; X = Y; Y = t; }
  FILE *f = fopen(argv[2], "wb"); fwrite(X, 1, V, f); fclose(f); return 0; }
