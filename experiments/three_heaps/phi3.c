/* three_heaps/phi3.c — one Phi step on three heaps: phi3 N S TARGET OUT.
   TARGET: file of (N+1)^3 bytes (1 = in T) or "-" for T = empty. Output P-set of Sub(S)^3 with T forced N. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  int N = atoi(argv[1]); long M = N + 1, V = M * M * M; int S[16], n = 0; char *t;
  for (t = strtok(argv[2], ","); t; t = strtok(0, ",")) S[n++] = atoi(t);
  unsigned char *T = calloc(V, 1), *Y = malloc(V);
  if (strcmp(argv[3], "-")) { FILE *f = fopen(argv[3], "rb"); if (fread(T, 1, V, f) != (size_t)V) return 2; fclose(f); }
  for (int a = 0; a <= N; a++) for (int b = 0; b <= N; b++) for (int c = 0; c <= N; c++) {
    long x = (a * M + b) * M + c; int win = T[x];
    for (int i = 0; i < n && !win; i++) { int s = S[i];
      if (s <= a && Y[x - s * M * M]) win = 1;
      else if (s <= b && Y[x - s * M]) win = 1;
      else if (s <= c && Y[x - s]) win = 1; }
    Y[x] = !win; }
  FILE *f = fopen(argv[4], "wb"); fwrite(Y, 1, V, f); fclose(f); return 0; }
