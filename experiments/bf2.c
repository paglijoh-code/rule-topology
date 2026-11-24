/* Independent brute force for two-heap Sub(S1) -push-> Sub(S2) outcomes (used by pump2.py).
   P(a,b) = 1 (P-position) iff g(a) == g(b) is false (the push is not a winning move: the pushed
   position is a Sub(S2) sum with Grundy g(a)^g(b), a P-position of the sum iff g(a) == g(b), and pushing
   to it wins) and no S1 move reaches a P-position.  Same rule as lead_a2.solve2, written again in C.
   Usage: bf2 N "s1,s1,.." "s2,s2,.." OUTFILE   -> writes (N+1)*(N+1) bytes, row-major P[a][b]. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int parse(const char *s, int *out) {
    int n = 0; char buf[256]; strncpy(buf, s, 255); buf[255] = 0;
    for (char *t = strtok(buf, ","); t; t = strtok(NULL, ",")) out[n++] = atoi(t);
    return n;
}

int main(int argc, char **argv) {
    if (argc != 5) { fprintf(stderr, "usage: bf2 N S1 S2 OUT\n"); return 2; }
    long N = atol(argv[1]);
    int S1[16], S2[16];
    int n1 = parse(argv[2], S1), n2 = parse(argv[3], S2);
    int *g = malloc((N + 1) * sizeof(int));
    for (long h = 0; h <= N; h++) {
        unsigned long long seen = 0;
        for (int i = 0; i < n2; i++) if (S2[i] <= h) seen |= 1ULL << g[h - S2[i]];
        int m = 0; while (seen >> m & 1) m++;
        g[h] = m;
    }
    long W = N + 1;
    unsigned char *P = calloc(W * W, 1);
    if (!P) { fprintf(stderr, "oom\n"); return 1; }
    for (long a = 0; a <= N; a++)
        for (long b = a; b <= N; b++) {
            int v = 0;
            if (g[a] != g[b]) {
                v = 1;
                for (int i = 0; i < n1 && v; i++) {
                    long s = S1[i];
                    if (s <= a && P[(a - s) * W + b]) v = 0;          /* row a-s < a is complete */
                    else if (s <= b && P[a * W + (b - s)]) v = 0;    /* (a, b-s): filled, or mirrored */
                }
            }
            P[a * W + b] = (unsigned char)v; P[b * W + a] = (unsigned char)v;
        }
    FILE *f = fopen(argv[4], "wb");
    fwrite(P, 1, W * W, f); fclose(f);
    return 0;
}
