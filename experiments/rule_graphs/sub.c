/* One node of a rule-graph subtraction game on two piles (N1 x N1 table).
   out[a*N1+b] = 1 (P) / 0 (N). pushP[a*N1+b] != 0 means some push target is P (so N). */
#include <stdint.h>
void solve_node(int N1, int ns, const int *S, const uint8_t *pushP, int8_t *out) {
    for (int a = 0; a < N1; a++)
        for (int b = 0; b < N1; b++) {
            int v = 1;
            if (pushP && pushP[(long)a * N1 + b]) v = 0;
            for (int i = 0; i < ns && v; i++) {
                int s = S[i];
                if (s <= a && out[(long)(a - s) * N1 + b] == 1) v = 0;
                else if (s <= b && out[(long)a * N1 + b - s] == 1) v = 0;
            }
            out[(long)a * N1 + b] = (int8_t)v;
        }
}
