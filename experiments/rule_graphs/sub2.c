/* Two modes A, B on two piles; a turn is a subtraction move in the current mode, or a switch to
   the other mode that also removes exactly c from one pile (c >= 1, so the game is finite and no
   budget is needed). outA/outB[a*N1+b] = 1 (P) / 0 (N). */
#include <stdint.h>
static int pos(int N1, const int *S, int ns, const int8_t *o, int a, int b) {
    for (int i = 0; i < ns; i++) {
        int s = S[i];
        if (s <= a && o[(long)(a - s) * N1 + b] == 1) return 0;
        if (s <= b && o[(long)a * N1 + b - s] == 1) return 0;
    }
    return 1;
}
void solve_pair(int N1, int nA, const int *SA, int nB, const int *SB, int c, int8_t *outA, int8_t *outB) {
    for (int a = 0; a < N1; a++)
        for (int b = 0; b < N1; b++) {
            long i = (long)a * N1 + b;
            int vA = pos(N1, SA, nA, outA, a, b), vB = pos(N1, SB, nB, outB, a, b);
            if (c <= a) { if (outB[i - (long)c * N1] == 1) vA = 0; if (outA[i - (long)c * N1] == 1) vB = 0; }
            if (c <= b) { if (outB[i - c] == 1) vA = 0; if (outA[i - c] == 1) vB = 0; }
            outA[i] = (int8_t)vA; outB[i] = (int8_t)vB;
        }
}
