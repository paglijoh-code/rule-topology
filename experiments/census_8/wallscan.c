/* wallscan N D PMAX S1csv gpre gper gpatterncsv [ROWFILE]
   Row-streaming scanner for two-heap Sub(S1) -push-> game with g given as pre/per/pattern.
   Rows r_a(d)=P(a,a+d), d<D; a ring of max(S1)+1 rows is kept. Columns x>=D of an earlier row
   are read from its periodic extension row[ts + ((x-ts)%p)], ts = D-4*PMAX, p = detected tail period.
   Stops on noperiod / overflow (status field; a_stop = index of the row that failed, i.e. rows
   completed OK; for "ok" a_stop = N). Env WS_DUMP=FILE dumps all rows (N*D bytes). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int gpre, gper, gpat[4096];
static inline int g(long h) { return h < gpre ? gpat[h] : gpat[gpre + (h - gpre) % gper]; }

static int cmpi(const void *x, const void *y) { return *(const int *)x - *(const int *)y; }

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: wallscan N D PMAX S1 gpre gper gpat [ROWFILE]\n"); return 2; }
    long N = atol(argv[1]), D = atol(argv[2]), PMAX = atol(argv[3]);
    int S[32], n = 0, smax = 0;
    for (char *t = strtok(argv[4], ","); t; t = strtok(NULL, ",")) { S[n] = atoi(t); if (S[n] > smax) smax = S[n]; n++; }
    gpre = atoi(argv[5]); gper = atoi(argv[6]);
    { int k = 0; for (char *t = strtok(argv[7], ","); t; t = strtok(NULL, ",")) gpat[k++] = atoi(t);
      if (k != gpre + gper) { fprintf(stderr, "pattern length != pre+per\n"); return 2; } }
    if (D < 6 * PMAX) { fprintf(stderr, "need D >= 6*PMAX\n"); return 2; }
    const char *rowfile = argc > 8 ? argv[8] : NULL;
    const char *dumpf = getenv("WS_DUMP");
    FILE *fd = dumpf ? fopen(dumpf, "wb") : NULL;
    FILE *fp = NULL, *fq = NULL;
    if (rowfile) { char nm[1024]; fp = fopen(rowfile, "wb"); snprintf(nm, sizeof nm, "%s.per", rowfile); fq = fopen(nm, "wb"); }

    int R = smax + 1;
    long ts = D - 4 * PMAX;
    unsigned char *ring = calloc((size_t)R * D, 1);
    int *rp = calloc(R, sizeof(int));
    int *pers = malloc(N * sizeof(int));
    int *pres = malloc(N * sizeof(int));
    long (*rec)[2] = malloc(5000 * sizeof(long[2])); int nrec = 0;
    int maxpre = -1, prevp = 1;
    const char *status = "ok"; long astop = N;

    for (long a = 0; a < N; a++) {
        unsigned char *r = ring + (size_t)(a % R) * D;
        int ga = g(a);
        for (long d = 0; d < D; d++) {
            int val = (g(a + d) != ga);
            for (int i = 0; i < n && val; i++) {
                long s = S[i];
                if (s <= a) {
                    long x = d + s; long b = (a - s) % R;
                    unsigned char *q = ring + (size_t)b * D;
                    int pv = x < D ? q[x] : q[ts + ((x - ts) % rp[b])];
                    if (pv) { val = 0; break; }
                }
                if (s <= a + d) {
                    if (d >= s) { if (r[d - s]) { val = 0; break; } }
                    else { long a2 = a - (s - d);
                        if (a2 >= 0 && ring[(size_t)(a2 % R) * D + (s - d)]) { val = 0; break; } }
                }
            }
            r[d] = (unsigned char)val;
        }
        if (fd) fwrite(r, 1, D, fd);
        /* tail period */
        int p = 0;
        for (int pass = 0; pass < 2 && !p; pass++) {
            long lo = pass == 0 ? prevp : 1, hi = pass == 0 ? prevp : PMAX;
            for (long c = lo; c <= hi; c++) {
                long x = D - 4 * PMAX;
                for (; x < D - c; x++) if (r[x] != r[x + c]) break;
                if (x >= D - c) { p = (int)c; break; }
            }
        }
        if (!p) { status = "noperiod"; astop = a; break; }
        /* least p: prevp found first may not be least; search smaller ones */
        for (int c = 1; c < p; c++) {
            long x = D - 4 * PMAX;
            for (; x < D - c; x++) if (r[x] != r[x + c]) break;
            if (x >= D - c) { p = c; break; }
        }
        prevp = p;
        long y = D - p - 1;
        while (y >= 0 && r[y] == r[y + p]) y--;
        long pre = y + 1;
        rp[a % R] = p; pers[a] = p; pres[a] = (int)pre;
        if (fp) { int v = (int)pre; fwrite(&v, 4, 1, fp); fwrite(&p, 4, 1, fq); }
        if (pre > maxpre) { maxpre = (int)pre; if (nrec < 5000) { rec[nrec][0] = a; rec[nrec][1] = pre; nrec++; } }
        if (pre > D - 4 * PMAX - PMAX) { status = "overflow"; astop = a; break; }
    }
    /* summary */
    printf("{\"status\":\"%s\",\"a_stop\":%ld,\"N\":%ld,\"D\":%ld,\"PMAX\":%ld,\"tail_periods\":[", status, astop, N, D, PMAX);
    long done = astop;   /* rows with pres[] valid: 0..done-1 (plus failing row for overflow) */
    int ps[4096], np = 0;
    { char seen[4097] = {0};
      for (long a = done / 2; a < done; a++) if (!seen[pers[a]]) { seen[pers[a]] = 1; }
      for (int k = 1; k <= 4096 && k <= PMAX; k++) if (seen[k]) ps[np++] = k; }
    for (int i = 0; i < np; i++) printf("%s%d", i ? "," : "", ps[i]);
    printf("],\"block_max_pre\":[");
    for (long b = 0; b < done; b += 250) {
        int m = 0; for (long a = b; a < b + 250 && a < done; a++) if (pres[a] > m) m = pres[a];
        printf("%s%d", b ? "," : "", m);
    }
    printf("],\"records\":[");
    for (int i = 0; i < nrec; i++) printf("%s[%ld,%ld]", i ? "," : "", rec[i][0], rec[i][1]);
    printf("],\"max_pre\":%d}\n", maxpre < 0 ? 0 : maxpre);
    if (fd) fclose(fd);
    if (fp) { fclose(fp); fclose(fq); }
    (void)cmpi;
    return 0;
}
