/* three_heaps/stream3.c — one-push game S1->S2 on [0,N]^3, computed plane by plane in a (ring of planes, memory ~ 40 M^2 bytes),
   with streaming analyses.  usage:
     stream3 N S1 S2 OUTPREFIX [R_diag] [P_defect] [L a0 b0 c0]...
   Table: T(x)=1 iff P-position of Phi_{S1}(P2), P2 = {g2(a)^g2(b)^g2(c)=0}, g2 = Grundy of Sub(S2).
   Outputs:
     OUT.cx      : for n = 8..N, number of distinct 4x4x4 blocks with chamber corner (a<=b<=c) inside [0,n-1]^3
                   (block code bit i*16+j*4+l = T(a+i,b+j,c+l), same as big.py)
     OUT.prof    : rows "s r tot rare2 defect": chamber corners binned by s=a+b+c (bin 20) and r = distance to diagonal (bin 4);
                   rare2 = corners whose block occurs <= 2 times among all chamber corners of the cube;
                   defect = cells with T(x) != T(x+P e_c) or T(x) != T(x+P e_b) (both inside the cube)
     OUT.diag    : uint8 [(N+1)][2R+1][2R+1], X[a][i][j] = T(a, a+i-R, a+j-R), 2 outside the cube
     OUT.win<k>  : uint8 L^3 window with corner (a0,b0,c0), index ((a-a0)*L+(b-b0))*L+(c-c0)
     OUT.T       : (only if env DUMP_T=1) the full table, (N+1)^3 bytes, for validation against chain3 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
static int parse(char *s, int *S) { int n = 0; char *t; for (t = strtok(s, ","); t; t = strtok(0, ",")) S[n++] = atoi(t); return n; }
static int N, M, n1, S1[16], g[100000];
#define RING 8
static uint8_t *P[RING]; static uint16_t *Q[RING];
static void plane(int a) { /* compute T plane a into P[a%RING] and Q */
  uint8_t *Y = P[a % RING];
  for (int b = 0; b <= N; b++) for (int c = 0; c <= N; c++) {
    int win = (g[a] ^ g[b] ^ g[c]) == 0; long x = (long)b * M + c;
    for (int i = 0; i < n1 && !win; i++) { int s = S1[i];
      if (s <= a && P[(a - s) % RING][x]) win = 1;
      else if (s <= b && Y[x - (long)s * M]) win = 1;
      else if (s <= c && Y[x - s]) win = 1; }
    Y[x] = !win; }
  uint16_t *q = Q[a % RING];
  for (int b = 0; b + 3 <= N; b++) for (int c = 0; c + 3 <= N; c++) { uint16_t v = 0; int sh = 0;
    for (int j = 0; j < 4; j++) for (int l = 0; l < 4; l++, sh++) v |= (uint16_t)Y[(long)(b + j) * M + c + l] << sh;
    q[(long)b * M + c] = v; }
}
/* hash map uint64 -> (count, minN) */
static uint64_t *HK, *HL; static uint32_t *HC, *HN; static uint64_t CUR; static uint8_t *HU; static uint64_t HS, HF;
static uint64_t hsh(uint64_t k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL; k ^= k >> 33; return k; }
static void hinit(uint64_t s) { HS = s; HF = 0; HK = calloc(s, 8); HL = calloc(s, 8); HC = calloc(s, 4); HN = calloc(s, 4); HU = calloc(s, 1); }
static void hput(uint64_t k, uint32_t n);
static void grow(void) { uint64_t os = HS, *ok = HK, *ol = HL; uint32_t *oc = HC, *on = HN; uint8_t *ou = HU; hinit(os * 2);
  for (uint64_t i = 0; i < os; i++) if (ou[i]) { uint64_t h = hsh(ok[i]) & (HS - 1); while (HU[h]) h = (h + 1) & (HS - 1);
      HU[h] = 1; HK[h] = ok[i]; HL[h] = ol[i]; HC[h] = oc[i]; HN[h] = on[i]; HF++; }
  free(ok); free(ol); free(oc); free(on); free(ou); }
static void hput(uint64_t k, uint32_t n) { uint64_t h = hsh(k) & (HS - 1);
  while (HU[h]) { if (HK[h] == k) { HC[h]++; if (n < HN[h]) { HN[h] = n; HL[h] = CUR; } return; } h = (h + 1) & (HS - 1); }
  HU[h] = 1; HK[h] = k; HC[h] = 1; HN[h] = n; HL[h] = CUR; if (++HF * 10 > HS * 7) grow(); }
static uint32_t hget(uint64_t k) { uint64_t h = hsh(k) & (HS - 1); while (HU[h]) { if (HK[h] == k) return HC[h]; h = (h + 1) & (HS - 1); } return 0; }
static uint64_t code(int a, int b, int c) { long x = (long)b * M + c; return (uint64_t)Q[a % RING][x] | (uint64_t)Q[(a + 1) % RING][x] << 16 |
  (uint64_t)Q[(a + 2) % RING][x] << 32 | (uint64_t)Q[(a + 3) % RING][x] << 48; }
#define SB 20
#define RB 4
#define NR 400
int main(int argc, char **argv) {
  N = atoi(argv[1]); M = N + 1; n1 = parse(argv[2], S1); int S2[16], n2 = parse(argv[3], S2); char *out = argv[4];
  int R = argc > 5 ? atoi(argv[5]) : 100, PD = argc > 6 ? atoi(argv[6]) : 60;
  int nw = argc > 7 ? (argc - 7) / 4 : 0, WL[16], WA[16], WB[16], WC[16]; uint8_t *W[16];
  for (int k = 0; k < nw; k++) { WL[k] = atoi(argv[7 + 4 * k]); WA[k] = atoi(argv[8 + 4 * k]); WB[k] = atoi(argv[9 + 4 * k]); WC[k] = atoi(argv[10 + 4 * k]);
    W[k] = calloc((long)WL[k] * WL[k] * WL[k], 1); }
  for (int h = 0; h <= N; h++) { unsigned long long seen = 0; for (int i = 0; i < n2; i++) if (S2[i] <= h) seen |= 1ULL << g[h - S2[i]];
    int m = 0; while (seen >> m & 1) m++; g[h] = m; }
  for (int i = 0; i < RING; i++) { P[i] = malloc((long)M * M); Q[i] = calloc((long)M * M, 2); }
  char fn[1024]; int D = 2 * R + 1; uint8_t *dg = malloc((long)D * D);
  sprintf(fn, "%s.diag", out); FILE *fd = fopen(fn, "wb");
  FILE *ft = getenv("DUMP_T") ? (sprintf(fn, "%s.T", out), fopen(fn, "wb")) : 0;
  uint64_t *nh = calloc(N + 8, 8);
  hinit(1 << 20); int nohash = getenv("NOHASH") != 0;
  for (int pass = 0; pass < 2; pass++) {
    static uint64_t tot[400][NR], rare[400][NR], dfc[400][NR];
    for (int a = 0; a <= N + 3; a++) {
      if (a <= N) {
        plane(a); uint8_t *Y = P[a % RING];
        if (pass == 0) {
          if (ft) fwrite(Y, 1, (long)M * M, ft);
          for (int i = 0; i < D; i++) for (int j = 0; j < D; j++) { int b = a + i - R, c = a + j - R;
            dg[i * D + j] = (b < 0 || c < 0 || b > N || c > N) ? 2 : Y[(long)b * M + c]; }
          fwrite(dg, 1, (long)D * D, fd);
          for (int k = 0; k < nw; k++) if (a >= WA[k] && a < WA[k] + WL[k]) for (int i = 0; i < WL[k]; i++) for (int j = 0; j < WL[k]; j++) {
            int b = WB[k] + i, c = WC[k] + j; W[k][((long)(a - WA[k]) * WL[k] + i) * WL[k] + j] = (b <= N && c <= N) ? Y[(long)b * M + c] : 2; }
        } else { /* defect profile on cells of plane a in the chamber */
          for (int b = a; b <= N; b++) for (int c = b; c <= N; c++) { long x = (long)b * M + c; int t = Y[x];
            if (c + PD > N || b + PD > N) continue;
            int s = a + b + c; double m = s / 3.0; double r = sqrt((a - m) * (a - m) + (b - m) * (b - m) + (c - m) * (c - m));
            int rb = (int)(r / RB); if (rb >= NR || s / SB >= 400) continue;
            if (Y[x + PD] != t || Y[x + (long)PD * M] != t) dfc[s / SB][rb]++; }
        }
      }
      int a0 = a - 3; if (a0 < 0 || a0 + 3 > N) continue;
      for (int b = a0; b + 3 <= N; b++) for (int c = b; c + 3 <= N; c++) { uint64_t k = code(a0, b, c);
        if (nohash && pass == 0) continue;
        if (pass == 0) { CUR = (uint64_t)a0 << 42 | (uint64_t)b << 21 | c; hput(k, c + 4); }
        else { int s = a0 + b + c; double m = s / 3.0; double r = sqrt((a0 - m) * (a0 - m) + (b - m) * (b - m) + (c - m) * (c - m));
          int rb = (int)(r / RB); if (rb >= NR || s / SB >= 400) continue; tot[s / SB][rb]++; if (!nohash && hget(k) <= 2) rare[s / SB][rb]++; } }
    }
    if (pass == 0) {
      fclose(fd); if (ft) fclose(ft);
      for (int k = 0; k < nw; k++) { sprintf(fn, "%s.win%d", out, k); FILE *f = fopen(fn, "wb"); fwrite(W[k], 1, (long)WL[k] * WL[k] * WL[k], f); fclose(f); }
      for (uint64_t i = 0; i < HS; i++) if (HU[i]) nh[HN[i]]++;
      sprintf(fn, "%s.cx", out); FILE *f = fopen(fn, "w"); uint64_t cum = 0;
      for (int n = 0; n <= N + 4; n++) { cum += nh[n]; if (n >= 8 && n <= N + 1) fprintf(f, "%d %llu\n", n, (unsigned long long)cum); } fclose(f);
      { sprintf(fn, "%s.new", out); FILE *fn2 = fopen(fn, "w"); long w = 0;   /* first-occurrence corner of blocks new after 0.75 N (sample) */
        for (uint64_t i = 0; i < HS && w < 500000; i++) if (HU[i] && HN[i] > 3 * N / 4) { w++;
          fprintf(fn2, "%u %llu %llu %llu\n", HN[i], (unsigned long long)(HL[i] >> 42), (unsigned long long)(HL[i] >> 21 & 0x1fffff), (unsigned long long)(HL[i] & 0x1fffff)); }
        fclose(fn2); }
      fprintf(stderr, "pass0 distinct %llu\n", (unsigned long long)HF);
    } else {
      sprintf(fn, "%s.prof", out); FILE *f = fopen(fn, "w");
      for (int s = 0; s < 400; s++) for (int r = 0; r < NR; r++) if (tot[s][r] || dfc[s][r])
        fprintf(f, "%d %d %llu %llu %llu\n", s * SB, r * RB, (unsigned long long)tot[s][r], (unsigned long long)rare[s][r], (unsigned long long)dfc[s][r]);
      fclose(f);
    }
  }
  return 0;
}
