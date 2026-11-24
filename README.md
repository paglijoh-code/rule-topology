# Square-root outcome walls in push-subtraction games

Code, data and Lean 4 proofs for the paper *Square-root outcome walls in two-heap push-subtraction games, with Lean 4 proofs* by Johnny Paglino. MIT license.

## What is proved and what is not

**Proved in Lean 4** (axioms `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`, no `native_decide`), in the main library:

- the √a wall of the game S1 = {1,2,5,6}, S2 = {1,2,3,4}: `sqrt_wall` and corollaries (`lean/SqrtMain.lean`, `lean/SqrtCor.lean`), and the table beyond the wall (`lean/SqrtFar.lean`);
- a sound checker for doubly periodic certificates, with one instance, `leadA_3_14` (`lean/LeadAMain.lean`);
- a sound checker for wall certificates, `family_wall_law` (`lean/FamilyMain.lean`), with the instances wall A and wall B (`lean/Cert/WA`, `lean/Cert/WB`).

**Status of the 62 walls** (one row each, with the constants of the law, in `certificates/walls.csv`):

| status | walls | meaning |
|---|---|---|
| LEAN | 34 | The wall's theorem compiled and its axiom report is recorded. |
| PENDING | 13 | The Python checker accepts a certificate; the Lean build was not run or did not complete. Not proved. Seven builds failed. |
| COMP | 15 | The law was computed up to a = 100,000. No usable certificate. Not proved. |

How the 34 LEAN walls were built:

- 2 (A and B): built with the main library, and rebuilt whenever it is.
- 26: each built **once**, on a rented 32-vCPU machine (24 November 2026). **These builds have not been repeated, and no hashes of the sources that machine built were recorded.** The logs are `certificates/logs/run_rented_machine.log`, `builds_rented_machine.csv` and `axioms_rented_machine.txt`.
- 6: each built once on a laptop. Axiom reports: `axioms_laptop.txt`.

The sources of the 32 walls other than A and B are too large to ship (half a gigabyte with the pending walls), so the generator is shipped instead. `certificates/reference.json` has SHA-256 digests of the source files kept on the author's laptop. These digests are of the laptop's files, not of the rented machine's. They are known to differ in places: the rented machine's `Init.lean` for nine walls had an extra `set_option maxHeartbeats 1000000` line, added after a time-out. This is a resource limit and does not change what is checked.

The scope of a wall theorem (`WallLaw`) is limited:

- It says that pre(t_k) = w0 + Δk and that pre(a) ≤ w0 + Δk + c for t_k ≤ a < t_{k+1}, for all k ≥ k0. The second part is an upper bound only, and c is not optimised.
- It says nothing about rows below T0 (8,791 for A, larger for some others).
- It is about the table built from S1 and the sequence g. `family_wall_outcome` transfers it to a game when g is the Grundy sequence of S2; that hypothesis has been proved in Lean for wall A only.
- The √(2a/s) asymptotics is a consequence proved on paper, not in Lean, for walls other than A.

Everything under `experiments/` is computation; nothing there is proved in Lean.

**This repository was exported from a working repository.** The export removed unrelated libraries, changed the Lake package name and edited comments. The complete Lean build has not been run on this export.

## Layout

- `lean/`: the Lean library (toolchain in `lean/lean-toolchain`, no dependencies).
- `certgen/`: the untrusted generator of wall certificates and of their Lean sources. Format: `docs/certificate-format.md`.
- `certificates/`: the 48 certificates found (xz-compressed JSON), `walls.csv`, `generator_summary.jsonl`, the digests and the recorded logs. The 48 are the 34 LEAN and 13 PENDING walls and one COMP wall whose certificate is incomplete.
- `experiments/`: scripts and recorded outputs of the computations in the paper. `sqrt_model` (the row model and its test against brute force), `census_8` and `census_10` (wall scans), `prediction` (second census and its preregistration), `three_heaps` and `column_periods`, `game_classes`, `rule_graph_laws`, `rule_graphs`; the scripts at the top level are the census of pairs, certificates for it, and the first experiments. Build the C programs with `make -C experiments`; scripts run from their folder or from `experiments/`, some for hours. Large intermediate tables are not included. Quick tests: `census_8/test_wallscan.py`, `three_heaps/selftest.py`, `game_classes/test_classes.py`, `rule_graphs/test_rule_graphs.py`; and the row model against brute force: `sqrt_model/rowgen 24000 800 1,2,5,6 5 /tmp/R.bin`, then `SQ_TMP=/tmp python3 sqrt_model/verify_bf.py 2000`.

## Checking

Needs Python 3.9 or later with `numpy` (`pip install -r requirements.txt`), a C compiler, and for Lean [elan](https://github.com/leanprover/elan).

    scripts/check_light.sh      # minutes; no Lean
    scripts/check.sh            # forbidden constructs, then `lake build`: main library with walls A and B

`check_light.sh` searches for forbidden constructs, tests the generator (including finding the certificates of A and B again), and compares the generated initial-run sources of the 32 walls with the recorded digests.

**Generating the round sources needs Lean**, not only Python: the generator runs the checker's code to obtain intermediate states (one Lean process, about 1.5 GB in the part of the run we watched).

    (cd lean && lake build FamilyMain)                       # seconds to a minute
    cp -R lean /tmp/lean-copy                                # or generate in place
    python3 -m certgen.emit_all    --lean-dir /tmp/lean-copy --no-limits
    python3 -m certgen.emit_rounds --lean-dir /tmp/lean-copy --no-limits     # about 30 minutes
    python3 -m certgen.verify_sources /tmp/lean-copy

On 24 November 2026 this was run once from a fresh clone, with one Lean process at a time: **for 32 of the 32 walls every generated file was byte-identical to the reference file (34,529 files in all)**. No generated proof was compiled in that run; it shows that the generator reproduces the sources, not that they check. Without `--no-limits` the same files get `set_option` lines and are not byte-identical; `verify_sources` ignores those lines in its second digest.

To build a wall, generate it without `--no-limits` (heavy walls need the resource limits lifted) and build its last module:

    python3 -m certgen.emit_all ID && python3 -m certgen.emit_rounds ID
    (cd lean && lake build +Cert.NAME.Round)                 # NAME: certificates/names.json

`lake build CertAll` builds 44 of the 45 generated walls, pending ones included (generate them with `--all`); the one left out, {1,4,5,7,9,10,12}, was regenerated after a wrong row period and has never been built.

Cost, from the recorded builds: main library about 100 s, walls A and B about 15 min of CPU time. The six laptop walls took 170 to 3,114 s of CPU time each. The 26 others took 28 to 4,796 s each on 32 vCPU, so building all of them on a laptop should take days.
