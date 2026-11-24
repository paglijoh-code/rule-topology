# Certificate format and checker

The Python generator (`certgen/`) and the Lean checker (`lean/Family*.lean`) implement these definitions.

## Game
- `S1 : List Nat`, all entries ≥ 1; `m = max S1`.
- g: `gpre : List Nat` (length N ≥ 0), `gper : List Nat` (length p ≥ 1). `gv x = if x < N then gpre[x] else gper[(x − N) % p]`.
- `PG S1 g a b : Bool` (true = P): P iff `gv a ≠ gv b` and for every s ∈ S1: (s ≤ a → PG (a−s) b = false) and (s ≤ b → PG a (b−s) = false). Defined by well-founded recursion on a + b. For realised g (g = sg of Sub(S2)) it equals `LeadA.outcome S1 S2` (bridge via `LeadA.outcome_eq` and `LeadA.gOk_sound`).
- Row: `R a d = PG a (a+d)`; rows with negative index are all false.

## Letters and stacks
- A letter is a Nat < 2^m. Bit i of the stack letter at column x after row a is `R (a−i) (x+i)`, i < m.
- `St n : Nat → Nat` is the stack after row a = n − 1 (so `St 0 = fun _ => 0`, no rows yet).

## The row transducer (computes row A = n from `St n`, giving `St (n+1)`)
Input word `u x = St n (x + 1)` (tail of the stack). Run left to right over d = 0, 1, 2, …
- **State** `(u0, hist, dtag, cnt)` (Lean `TState`; `cnt = min d m` distinguishes d = 0 and d < m): `u0` = the first input letter while d < m, else 0; `hist` = last m output bits (bit j = new row bit at d−1−j, 0 if d−1−j < 0); `dtag = if d < N then d else N + (d − N) % p`.
- **Row tag** `rtag A = if A < N then A else N + (A − N) % p`; `test(rtag, dtag) = (gv A ≠ gv (A + d))`, computable from the two tags.
- **New bit** at d: `test ∧ ∀ s ∈ S1: bit (s−1) of u d = 0 ∧ (if s ≤ d then hist bit (s−1) = 0 else bit (s−d−1) of u0' = 0)`, where u0' is the first input letter (at d = 0 it is u 0 itself). Rows with negative index are already 0 in the letters, so no `s ≤ A` side conditions appear.
- **Output letter** at d: `(newbit + 2 * (u d % 2^(m−1))) % 2^m`. Test is computed as `gv rt ≠ gv (rt + dtag)` on tags (Lean `tg_add`).
- Claim to prove (Lean, general): `St (n+1) d = output letter at d of the run on u`, for all S1, g, n, d.

## Shapes (symbolic stacks)
`shape = (x0, [(y1, x1), …, (yj, xj)], z)` with words = lists of letters, z nonempty, counters `n : List Nat` (one per block). `decode shape n = x0 ++ y1^{n1} ++ x1 ++ … ++ yj^{nj} ++ xj ++ z ++ z ++ …` as a function Nat → Nat.

## Symbolic step (with row tag)
`sstep rtag shape` returns `(shape', δ : List Int, γ : List Nat)` or failure: drop the first letter of x0 (|x0| ≥ 2 required), run the transducer concretely over boundaries; over each block y from state q: if the run over y returns to q, emit y' (output) and keep the block; else unroll one copy into the preceding boundary (counter −1, guard +1) and retry, at most U = 8 times, else fail. The tail z: same, unrolled copies go into xj; emit z'. Soundness: ∀ n ≥ γ, `decode shape' (n + δ) = output of the run on tail (decode shape n)`.
Fixed-point comparison of states needs dtag periodic, so blocks and z must have length ≡ 0 mod p, and |x0| ≥ max(N, m) + 2.

## Normalisation
`norm shape` moves whole copies of yi between yi^{ni} and its neighbouring boundaries (prefix of x_i equal to y_i, suffix of x_{i−1} equal to y_i), and copies of z out of xj, to reach margins chosen by the generator (target: each boundary keeps between Mmin and Mmin + |y| letters of each neighbouring block's pattern). Only `decode (norm shape) n' = decode shape n` (with the stated counter change) is proved; the margin policy is generator-only.

## Certificate file (one per wall)
The Lean checker needs only: drop-first-letter + `sstep`, the explicit moves below, word equality, and affine arithmetic in `j`.

**Row/shape conventions.** `Init_k` is the shape of `Σ_{t_k}` (the stack after row `t_k − 1`, before row `t_k` is computed); the step number `r` computes row `r` from the shape of `Σ_r` and gives the shape of `Σ_{r+1}`. The row tag of step `r` is `r mod p` (N = 0 here; in general `tg`). Shapes are identified without counters and without the row tag, except through the transducer class of the tag (rows whose `tst` tables coincide are one class), so `R` does not pick up a factor `p`.

**Step = `sstep` then moves.** One entry of `steps`/`phases` is a list of moves applied (in order) to the output of `sstep`. A shape is `b = [x0..xj]` (boundaries), `y = [y1..yj]` (block words), `n = [n1..nj]` (counters), `z`. Moves (all decode-preserving; guards on counters in brackets):
- `["rot", i, r]` (block i, 0-based): `y_i := y_i[r:] ++ y_i[:r]`; `x_{i} ++= old y_i[:r]`; `x_{i+1} := old y_i[r:] ++ x_{i+1}`; `n_i -= 1`. [n_i ≥ 1]
- `["pull", i, "R"|"L"]`: one copy of `y_i` moves to the start of `x_{i+1}` (R) or the end of `x_i` (L); `n_i -= 1`. [n_i ≥ 1]
- `["abs", i, "R"|"L"]`: inverse (the boundary must start (R) / end (L) with `y_i`); `n_i += 1`.
- `["trot", r]`: `x_j ++= z[:r]`, `z := z[r:] ++ z[:r]`. `["tpull"]`: `x_j ++= z`. `["tabs"]`: `x_j` must end with `z`; drop it.
- `["fold", b, s, c, y]`: boundary `x_b = u ++ y^c ++ v` with `|u| = s`; replace by boundary `u`, new block `(y, n = c)`, boundary `v` (numeric `c`; only these two moves change the number of blocks).
- `["drop", i]`: block i removed, boundaries merged. [n_i = 0 as an affine identity in j]
`sstep` guards: `n_i ≥ γ_i` (copies unrolled from block i); the unrolled count is also what `δ` records. For the tail, the state sequence at `z`-block starts may have a cycle of length c > 1; the output tail is then c copies of `z` (reduced to its least period that is a multiple of p after the step, `canon_z`), unrolled pre-period copies go into `x_j`. This is the one deviation from "fixed point" for blocks (see below).

**JSON.** All numbers are integers; `[a, b]` denotes the affine function `a·j + b` of the class index `j` (the round is `k = R·j + i`); `"cnt"` is a list of such pairs, one per block counter, valid for `j ≥ j0`.
```
{ "format": "m6-cert-1",
  "wall":  {"name", "S1": [..], "gpre": [..], "gper": [..]},
  "m": 6, "p": 5, "blockLen": 35, "margin": 8, "cf": 2,        // normalisation parameters (generator-only; informational)
  "R": 7, "k0": 33,                                              // residue modulus; first steady round
  "law":   {"pi": 10, "w0": 35, "delta": 10, "alpha": 14, "beta": 42, "c": 20},
        // pre(t_k) = w0 + delta*k, t_{k+1} - t_k = alpha*k + beta, |pre(a) - w_k| <= c on round k for rows with pre(a) > 0
  "initial": {"rows": 8791, "steps": [ [move,..], ... ]},         // concrete run: rows 0..t_{k0}-1 from Sigma_0 = shape ([[]],[],[],z=0^p);
                                                                  // counters are numbers; ends in Init_{k0} (checked equal to class k0 mod R at j = k0 div R)
  "classes": [ { "i": 0, "j0": 5,
        "init":   {"b": [[..],[..]], "y": [[..]], "z": [..], "cnt": [[2,-2]]},
        "phases": [ {"kind": "step",  "moves": [move,..]},                       // one row
                    {"kind": "cycle", "len": 42, "count": [2,-7],               // P rows repeated count(j) times
                     "steps": [[move,..], ... 42 entries]}, ... ],
        "rows":   [98, 42] },                                                   // total rows of the round = rows(j) = 14*(7j+i)+42
      ... R classes ] }
```
**Checker semantics (per class `i`, symbolic in `j ≥ j0`).** Start from `init` with counters affine in `j`. `step`: apply drop-first-letter, `sstep`, the moves; every guard is an affine inequality (or, for `drop`, identity) in `j`, checked for all `j ≥ j0` by coefficient/constant arithmetic. `cycle`: run the `len` steps once from the current shape `X` (counters `n`); the shape reached must equal `X` word for word and the counters change by a constant vector `d` (the same affine expression for every iteration); guards are then affine in the iteration index `t` and are checked at `t = 0` and `t = count(j) − 1` (both ends, linear in between), after which the counters are `n + count(j)·d`. At the end of the round the shape must equal `init` of class `(i+1) mod R` word for word, with counters equal to its `cnt` evaluated at `j' = j + [i+1 = R]` (affine identities), and the number of rows must equal `rows(j)` (affine identity), which must equal `alpha*k + beta` at `k = R*j + i`. `initial` is the same with numeric counters. `law.pi/w0/delta`: `preOf` of bit 0 of `decode(init)` (least onset of tail period `pi`, lying inside a boundary) is `w0 + delta*k + const`, evaluated with the affine counters; `c` is checked from the shapes of the round (every distinct shape of the round gives its `pre`).


## Initial run in Lean
1. Moves `rot i r` and `tshrink c` exist in Lean (`Move.rot`, `Move.tshrink`, sound in `applyMove_sound`). JSON `canon_z` is not a move in the certificate: `sstep` in the generator already applies it, so the Lean `rowStep` applies `tshrink (shrinkC p z)` automatically after `sstep` (least period of z that is a multiple of p). Move mapping in `certgen/emit_lean3.py`.
2. The initial run starts from Sigma_0 = `sigma0 p` (x0 = [], no blocks, z = 0^p) and needs the generator's initial normalisation moves (`tpull`, `tpull` for A and B) as a `start` list; they are not in `initial.steps`.
3. Kernel cost forces checkpoints: the initial run is split into segments, each ending in a literal shape and counters (`Seg`, `runSegs`). The JSON holds them in `initial.checkpoints` (every `initial.K` rows). `certgen/emit_lean3.py` writes one `decide +kernel` module `I<nn>.lean` per segment, `Wall.lean` (data) and `Init.lean` (glue: `initial_run`, chained by `seg_next` and `start_sound`).
4. Fast checker `lean/FamilyFast.lean`: `tstepF` (raw `Nat` ops, mask form of `newBit`, bit table `tmOf`), `decFast` (Bool-based `DecidableEq TState`, proved equal to the derived one), `shapeEqB`/`listEqB`. Proved equal to the slow path: `tstepF_eq`, `rowStepF_eq`, `runRowsF_eq`, `runSegsF_eq`, `checkInitialF_sound`; per-segment `segCheckF_sound`/`seg_next`. `rowStep`/`rowStep_sound` unchanged.

## Rounds in Lean
Files: `lean/FamilyRound.lean` (affine counters, `symRow`), `FamilyWall.lean` (`IsPreG`, periodic-from checks), `FamilyPhase.lean` (phases, cycle iteration lemma, tags), `FamilyMain.lean` (`CertD`, `check`, `family_wall`), emitter `certgen/emit_round.py`, certificate `lean/Cert/<W>/Round.lean`.
1. **Counters** are `a*j + e*t + b` (`A3`; `t` the iteration inside a cycle). A guard is linear in `t`, so it is checked at `t = 0` and `t = count(j) - 1`; positivity of `a*j + b` for all `j >= j0` is `a >= 0 && a*j0 + b >= 0`.
2. **JSON additions** (computed by `emit_round.py`, checked in Lean): per step the representative row tag `rt` (the tag of the row at `j0`; Lean `tagOk` re-checks `eqTags` for the rows of `j0 .. j0+2p-1` and, in cycles, of `t < p`; equality for all `j` follows from the 2p-periodicity of `t_{Rj+i} mod p`, which holds for every law, proved in `CertD.t_per`). Per cycle the counter shift `d` (one `Int` per counter; shape returns to itself and counters move by `d` per iteration), found by `probeRun` (one iteration at `t = 0`).
3. **Law data** in `CertD`: `π α β Δ w0 c R k0 T0` (`T0 = t_{k0}` = rows of the initial run), no `w_of_k`. `t k0 = T0`, `t (k+1) = t k + α k + β` is the *definition* (`tRec`). Class `i` must have `k0 <= R*j0 + i < k0 + R` (its `j0` is the first `j` with `k >= k0`). Wall bounds per row: `PerFrom` the word at column `P = w0 + Δ k + c` (`wallOk`, both ends of the iteration range); exactness `IsPreG (t k) (w0 + Δ k)` is `wallEx` on the first row of each round (first phase must be a `step`).
4. **Initial-run fact** is the Prop field `Cert.initOk : decode init(k0 % R) cnt(k0 / R) = St T0` (`CertD.InitOk`); `Cert/<W>/Round.lean` proves it from `Cert.<W>.initial_run` by `decide +kernel` on the two literal equalities.
5. **Kernel cost forces chunks.** One `decide +kernel` over a class of wall B (337 phases) did not finish in 590 s; 40 phases take 5 s, 150 phases more than 300 s (superlinear). The class is therefore cut into `Chunk`s (about 20 phases, every cycle alone) with literal start/end state (`shape | counters | row offset`, printed by `probeRun`), each chunk its own `decide +kernel` theorem `ck<i>_<k>`; `chunksOk_cons` chains them and `check_of_parts` splits `check` into the cheap part (globals, ranges, shape/counter equality at the class boundary, `linksB`) and the chunk runs. Times: wall B, 16 chunks of 1 to 18 s each, about 152 s of kernel time, 114 to 161 s per build; wall A, 7 classes, about 1077 s wall (714 s CPU) per build.
6. **Statement** (`FamilyMain.lean`, depends only on propext, Classical.choice, Quot.sound): `family_wall (C : Cert) (h : check C.toCertD = true) : WallLaw C.toCertD`, i.e. `t k0 = T0` and for every `k >= k0`: `t (k+1) = t k + α k + β`, `2 t k = 2 T0 + 2β(k-k0) + α(k(k-1) - k0(k0-1))`, `IsPreG S1 gpre gper π (t k) (w0 + Δ k)` and for every `a` with `t k <= a < t (k+1)` some `q <= w0 + Δ k + c` with `IsPreG S1 gpre gper π a q`. `IsPreG` is stated with `PG`. `family_wall_outcome` is the same with `LeadA.outcome S1 S2` (`IsPreO`) under `hg : ∀ x, LeadA.sgFn S2 x = gv gpre gper x` (from `LeadA.gOk` via `sgFn_eq_gv`).
