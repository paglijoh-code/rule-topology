/-
Lean port of the H.A certificate check of `lead_a3.py` (class `Pair`, methods `next_row` and
`certify`).  The certificate is a list of rows (each an eventually periodic 0/1 word, 1 = P:
row a is d -> outcome(a, a+d)) plus the numbers A0, q, a0, T, p and the SG preperiod and period.

`checkCert S1 S2 c = true` means that, finitely checked:
 (1) the SG sequence g of Sub(S2) is eventually periodic with preperiod gpre and period gper;
 (2) every listed row is exactly what the row recursion produces from the earlier listed rows:
     the recursion in d has finite state (the last max(S1) outputs, d mod L) once all its inputs
     are inside their cycles, so one repeat of that state proves the claimed (pre, cyc);
 (3) the window of max(S1) rows at a0 equals the window at a0 + q, a0 >= max(S1) + gpre and
     gper | q, so the row recursion (which depends on a only through a mod gper there) repeats:
     every row a >= A0 equals row a + q;
 (4) the rows A0 .. A0+q-1 have preperiod <= T and cycle lengths dividing p.

Soundness (`checkCert = true` implies eventual double periodicity of `outcome`) is proved in
LeadASound.lean (`checkCert_sound`).  Its d-periodicity clause covers rows a >= A0 only.
Everything is structurally recursive (explicit fuel) so `decide` can run it in the kernel.
-/
import LeadADefs
namespace LeadA

/-- An eventually periodic 0/1 word: `pre` followed by `cyc` repeated forever (`cyc` nonempty). -/
structure Row where
  pre : List Bool
  cyc : List Bool
deriving BEq, Inhabited, Repr

/-- The certificate (the `cert` dict of `lead_a3.Pair.certify` plus the rows). -/
structure Cert where
  rows : List Row
  gpre : Nat
  gper : Nat
  q : Nat
  A0 : Nat
  a0 : Nat
  p : Nat
  T : Nat
deriving Inhabited

/-- Letter d of the word. -/
def Row.at (R : Row) (d : Nat) : Bool :=
  if d < R.pre.length then R.pre.getD d false
  else R.cyc.getD ((d - R.pre.length) % R.cyc.length) false

/-- Row number i of the list (a dummy row if out of range). -/
def rowAt (rows : List Row) (i : Nat) : Row := rows.getD i default

/-- g x, from the listed values `gl` (preperiod gpre, period gper). -/
def gval (gl : List Nat) (gpre gper x : Nat) : Nat :=
  if x < gpre + gper then gl.getD x 0 else gl.getD (gpre + (x - gpre) % gper) 0

/-- Check (1): g is periodic from gpre with period gper, because the window of max(S2) values at
gpre equals the window at gpre + gper (g x depends only on the previous max(S2) values, x >= max S2). -/
def gOk (S2 : List Nat) (gpre gper : Nat) : Bool :=
  let M2 := S2.foldl max 0
  let g := sgList S2 (gpre + gper + M2)
  decide (0 < gper) && decide (0 < M2) && S2.all (fun s => decide (0 < s)) &&
  (List.range M2).all fun i => g.getD (gpre + i) 0 == g.getD (gpre + gper + i) 0

/-- Cell d of row a (a <= b = a + d), computed from the claimed earlier rows and the cells `r`
of row a already computed (those with index < d).  1 = P (`true`), exactly the rule of the game:
N if g a = g b (push to a P position); else N if some S1 move reaches a P position:
 - heap a reduced by s: position (a - s, b), row a-s at column d+s;
 - heap b reduced by s, staying >= a: position (a, b - s), own cell d - s;
 - heap b reduced by s below a: position (b - s, a), row b-s at column s - d. -/
def cell (S1 : List Nat) (gl : List Nat) (gpre gper : Nat) (rows : List Row) (a : Nat)
    (r : List Bool) (d : Nat) : Bool :=
  if gval gl gpre gper a == gval gl gpre gper (a + d) then false
  else !(S1.any fun s =>
    (decide (s ≤ a) && (rowAt rows (a - s)).at (d + s)) ||
    (decide (s ≤ a + d) &&
      (if s ≤ d then r.getD (d - s) false else (rowAt rows (a + d - s)).at (s - d))))

/-- Run the row recursion for `fuel` more columns. -/
def sim (S1 : List Nat) (gl : List Nat) (gpre gper : Nat) (rows : List Row) (a : Nat) :
    Nat → List Bool → List Bool
  | 0, r => r
  | fuel + 1, r => sim S1 gl gpre gper rows a fuel (r ++ [cell S1 gl gpre gper rows a r r.length])

/-- Check (2) for row a: the claimed (pre, cyc) is the row.  The inputs are the claimed rows
a - s (s in S1, s <= a) read at d + s, g, and the row's own last M outputs.  After column D0
(all input preperiods, gpre and M passed) the cell is a function of (last M outputs, d mod L),
L = lcm of the input cycle lengths and gper.  We simulate to d1 = max D0 (preperiod + M) (so the last M outputs before d1 lie in the cycle) and to
d2 = d1 + lcm(cycle length, L), require the simulated cells to equal the claimed row and the
state at d1 to equal the state at d2 (same d mod L by construction); then the row is the claimed
word forever. -/
def rowOk (S1 : List Nat) (gl : List Nat) (gpre gper : Nat) (rows : List Row) (a : Nat) : Bool :=
  let R := rowAt rows a
  let M := S1.foldl max 0
  let ins := (S1.filter (fun s => s ≤ a)).map fun s => rowAt rows (a - s)
  let D0 := (ins.map (fun x => x.pre.length) ++ [gpre, M]).foldl max 0 + M
  let L := (ins.map (fun x => x.cyc.length) ++ [gper]).foldl Nat.lcm 1
  let d1 := max D0 (R.pre.length + M)
  let d2 := d1 + Nat.lcm R.cyc.length L
  let r := sim S1 gl gpre gper rows a d2 []
  decide (0 < R.cyc.length) && ins.all (fun x => decide (0 < x.cyc.length)) &&
  (List.range d2).all (fun d => r.getD d false == R.at d) &&
  (List.range M).all (fun i => r.getD (d1 - M + i) false == r.getD (d2 - M + i) false)

/-- Cycle length and preperiod bounds on rows A0 .. A0+q-1 (check (4)). -/
def boundsOk (rows : List Row) (A0 q T p : Nat) : Bool :=
  decide (0 < p) && (List.range q).all fun i =>
    decide ((rowAt rows (A0 + i)).pre.length ≤ T) && decide (p % (rowAt rows (A0 + i)).cyc.length = 0)

/-- The whole check. -/
def checkCert (S1 S2 : List Nat) (c : Cert) : Bool :=
  let M := S1.foldl max 0
  let gl := sgList S2 (c.gpre + c.gper)
  S1.all (fun s => decide (0 < s)) && decide (0 < M) &&
  gOk S2 c.gpre c.gper &&
  -- rows 0 .. a0 + q + M - 1 are listed, and each is correct
  decide (c.a0 + c.q + M ≤ c.rows.length) &&
  (List.range c.rows.length).all (fun a => rowOk S1 gl c.gpre c.gper c.rows a) &&
  -- window repeat: a0 large enough, gper | q, the windows equal, and rows A0.. repeat with period q
  decide (0 < c.q) && decide (c.q % c.gper = 0) && decide (M + c.gpre ≤ c.a0) && decide (c.A0 ≤ c.a0) &&
  (List.range (c.a0 + M - c.A0)).all (fun i => rowAt c.rows (c.A0 + i) == rowAt c.rows (c.A0 + i + c.q)) &&
  boundsOk c.rows c.A0 c.q c.T c.p

end LeadA
