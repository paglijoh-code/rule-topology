# Pre-registration: wall step Δ and second difference s from the right bulk (2026-11-22)

Committed **before** the prediction scan (`prediction/scan.sh`) is run. Nothing in the test range has been scanned past the short far-tail runs of `predict.py` described below.

## The rule (R1)
For a pair (S1, g), let the **right bulk** be the far tail of the rows R_a(d) = P(a, a+d). From a short run only (rows a ∈ [700, 1300), columns d ∈ [2000, 3800); `prediction/predict.py`), measure
- T_R = the least d-period that holds exactly on every cell of the window;
- P_R = the least P ≥ 1 with R_a(d) = R_{a−P}(d) exactly on the window (a pure row period, no shift).

The predictor never reads pre(a), the running max M, records or any fit; it uses only those cells.

**R1 prediction.** If (S1, g) has an exact √a wall, then
- Δ = T_R, and
- s = T_R · P_R / per(g). Equivalently λ = s/Δ = P_R / per(g).

A pair with no T_R or P_R (the short run overflowed or had no tail period, or there was no P_R < 700) has no prediction. If it turns out to have a wall, that **counts as a miss**.

**R0 (weaker, lattice compatibility).** If the pair has an exact √a wall, then Δ ≡ 0 (mod T_R), s ≡ 0 (mod P_R), and in every class the first gap ≡ 0 (mod P_R). This says that one round translates the wall's neighbourhood by a vector of the right-bulk lattice.

**B0 (baseline to beat).** Δ = 2·per(g).

## In-sample record (all 32 known walls; contaminated, for calibration only)
`results/known_pred.jsonl` comes from the same predictor:

| rule | hits / 32 |
|---|---|
| R1 Δ | 21 |
| R1 s | 17 |
| R1 λ | 21 |
| R0 | 30 (the 2 misses have no P_R) |
| B0 Δ | 10 |

R1 misses Δ mostly on q > 1 walls (Δ = 2T_R or 3T_R) and on B (Δ = 6T_R).

## The test range (fixed; `prediction/jobs.py`)
g = x mod n, that is pre 0, per n, pattern 0..n−1 (realised by S2 = {1..n−1}).
- For n = 5..11: S1 ⊆ {1..12} containing 11 or 12. Pairs with S1 ⊆ {1..10} were already scanned by census_10/census_8.
- For n = 12, 13: every nonempty S1 ⊆ {1..12}.

That makes **29,694 pairs**. `predict.py` gave predictions for 27,762 of them. The other 1,932 have none: 945 overflowed and 331 had no period in the short run, and 656 had no exact T_R or P_R.

The predictions are in `results/pred_all.jsonl.gz`. After gunzip, the file is `out/pred_all.jsonl` with sha256 `c2862edb9e510bc2e1779f8bcba12e0f3eb7132b9c3217ff8e704ccd6452111d`. Jobs are in `results/jobs.jsonl.gz` (sha256 of the uncompressed file `48501ad636d176274f69002ebb11512adc6f60153bcb2ad6095602cef29120fd`).

## What counts as a wall (fixed; `prediction/scan.sh`, `prediction/score.py`)
The scan has four stages:
1. **Stage 1:** every pair at N = 2500, D = 1600, PMAX = 200 (as in census_10).
2. **Routing:** `census_10/select2.py` sends on every growing pair, every noperiod pair, and every overflow with a_stop > N/3.
3. **Stage 2a:** N = 12,000, D = 6000, PMAX = 600. Every routed pair goes on unless it is bounded, meaning status ok and max pre already reached in the first half.
4. **Stage 2b:** N = 100,000, D = 8000, PMAX = 400. A pair that overflows there is rerun with D = 20,000 and PMAX = 600.

A **√a wall** is a stage-2b/2c run with status ok to a = 100,000 on which `census_10/fit3.py` returns kind "sqrt" with exact = true. Everything else is not a wall (bounded, linear, no fit, or unresolved). Each of those groups is counted and reported.

## What is and is not predicted
- **Existence is not predicted.** R1 and R0 are conditional on a wall existing. The number of walls found is reported, but it is not scored.
- **Scoring:** the number of walls found, then for each rule the number of hits among them. Abstentions count as misses. False positives do not apply, because nothing is claimed for pairs without a wall.
- **Success criteria, stated now:**
  - R1 Δ is supported if its hit rate beats B0's and is at least 50%.
  - R0 is supported if it holds on every wall that has a prediction.
  - Any R0 failure refutes the lattice-compatibility claim as stated.
