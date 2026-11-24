/-
The explicit row model of the sqrt-wall pair (S1 = [1,2,5,6], S2 = [1,2,3,4], g n = n mod 5), as a
Lean function.  The same model in Python is `experiments/sqrt_model/model.py`.

Rows.  `Mrow a d` is the outcome (true = P) of the position (a, a + d), d >= 0.
Rounds.  `tk k = 7k^2 + 35k + 13` is the first row of round k, `wk k = 35 + 10 k` the wall position,
`gap k = 14 (k + 3)` the length of the round.  The row `a = tk k + r` (0 <= r < gap k) is, in the
column `e = d - wk k`:
* L phase (r < 12 k + 32): `alpha` left of the seam `p1L r`, `beta` up to the wall seam `pw (r mod 7)`,
  then the 10-periodic tail `tl (r mod 7)`.  `Lrow r e`.
* R phase (r >= 12 k + 32), s = gap k - r rows before the next jump: `gamma` left of the glider word
  `gword` (at `p1R s`), `beta` up to the wall seam, then the tail; the last row (s = 1) is the explicit
  word `eword` on e in [-10, 40).  `Rrow s e`.
Both are functions of the media phase u = (e - 5 r) mod 35 (lattice step: 1 row = +5 cells).
Rows 0..12 (before the first round) are explicit data (`early`).
The media words are bit masks (bit i = cell i; `#` = P = 1); the strings are checked below.
-/
import LeadADefs
namespace SqrtM

/-- bit i of the word m -/
def bit (m i : Nat) : Bool := m.testBit i

def alphaM : Nat := 17322549828   -- ..#...#..#...#..#......#...#......#
def betaM : Nat := 8665506372     -- ..#...#..#...#..#......#..#......#.
def gM : Nat := 9225              -- #..#......#..#
def eM : Nat := 158484444364936   -- ...#...#......#..#......#..#......#..#......#..#..
/-- the 7 tail words of 10 cells, indexed by the row phase z = r mod 7 -/
def tailM (z : Nat) : Nat := [516, 72, 258, 72, 258, 72, 144].getD z 0
/-- wall seam P[z] (L and R phase use the same table) -/
def pwN (z : Nat) : Nat := [6, 6, 11, 16, 21, 26, 1].getD z 0
/-- rows 0..12: cells 0..44, then period 10 from cell 35 -/
def earlyM (a : Nat) : Nat := [2476319443218, 8873478005316, 2476319459464, 8873478525186,
  2476336095304, 4952638621970, 17746947547712, 2476319459346, 8873478521412, 2476335974536,
  8874007007490, 2493247529032, 4952638621970].getD a 0

def alpha (i : Int) : Bool := bit alphaM (i % 35).toNat
def beta (i : Int) : Bool := bit betaM (i % 35).toNat
/-- gamma is alpha with its phase shifted by 10 (anchored at the next wall) -/
def gamma (i : Int) : Bool := alpha (i - 10)
def gword (i : Nat) : Bool := bit gM i
def eword (i : Nat) : Bool := bit eM i
def tl (z : Nat) (e : Int) : Bool := bit (tailM z) (e % 10).toNat
def pw (z : Nat) : Int := (pwN z : Int)

def tk (k : Nat) : Nat := 7 * (k * k) + 35 * k + 13
def wk (k : Nat) : Int := 35 + 10 * (k : Int)
def gap (k : Nat) : Nat := 14 * (k + 3)

/-- seam alpha | beta of the L phase, relative to the wall: p1 = w - 9 + 5 (r mod 6) - 5 (r div 6) -/
def p1L (r : Nat) : Int := -9 + 5 * ((r % 6 : Nat) : Int) - 5 * ((r / 6 : Nat) : Int)

/-- Row r of the L phase in the column e = d - w_k. -/
def Lrow (r : Nat) (e : Int) : Bool :=
  if e < p1L r then alpha (e - 5 * (r : Int))
  else if e < pw (r % 7) then beta (e - 5 * (r : Int))
  else tl (r % 7) e

/-- row phase z = r mod 7 of the R phase row with s rows to go (r = gap k - s, 7 | gap k) -/
def zR (s : Nat) : Nat := (7 - s % 7) % 7
/-- seam gamma | glider word of the R phase: p1 = w + 6 - 5 s -/
def p1R (s : Nat) : Int := 6 - 5 * (s : Int)

/-- Row of the R phase with s = gap k - r rows to go (s = 1: the last row before the jump). -/
def Rrow (s : Nat) (e : Int) : Bool :=
  if s = 1 then
    (if e < -10 then gamma (e + 5) else if e < 40 then eword (e + 10).toNat else tl (zR s) e)
  else if e < p1R s then gamma (e + 5 * (s : Int))
  else if e < p1R s + 14 then gword (e - p1R s).toNat
  else if e < pw (zR s) then beta (e + 5 * (s : Int))
  else tl (zR s) e

/-- Row t_k + r of the model, column d (d = b - a). -/
def Mk (k r : Nat) (d : Int) : Bool :=
  if r < 12 * k + 32 then Lrow r (d - wk k) else Rrow (gap k - r) (d - wk k)

/-- Rows 0..12 (before the first round). -/
def early (a d : Nat) : Bool := bit (earlyM a) (if d < 45 then d else 35 + (d - 35) % 10)

/-- Round of row a: the k with tk k <= a < tk (k+1) (fuel-bounded search upward from `k`). -/
def roundAux (a : Nat) : Nat → Nat → Nat
  | 0, k => k
  | f + 1, k => if tk (k + 1) ≤ a then roundAux a f (k + 1) else k
def roundOf (a : Nat) : Nat := roundAux a a 0

/-- Outcome (true = P) of the position (a, a + d). -/
def Mrow (a d : Nat) : Bool :=
  if a < 13 then early a d else Mk (roundOf a) (a - tk (roundOf a)) (d : Int)

/-- The model: outcome of the position with heaps a, b (true = P). -/
def model (a b : Nat) : Bool := if a ≤ b then Mrow a (b - a) else Mrow b (a - b)

end SqrtM
