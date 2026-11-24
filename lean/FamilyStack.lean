/-
Stacks of rows of the game `PG` and the row transducer of `docs/certificate-format.md`.

`St n x` packs the last `m = max S1` row bits above column `x` after rows `0 .. n-1`
(bit `i` is `R (n-1-i) (x+i)`).  `tstep` is the finite-state transducer that turns the tail
`fun x => St n (x+1)` into `St (n+1)`; the main theorem is `St_succ`.

SPEC deviation (needed for finiteness): `TState` carries a fourth field `cnt = min d m` (the
number of letters read, capped at `m`).  Without it the transducer cannot tell `d < m` (is `u0`
valid, is `s ≤ d`) from the state `(u0, hist, dtag)` alone.  It is finite-valued, so block fixed
points still exist.  Also the output letter is reduced mod `2^m` so that `m = 0` (`S1 = []`) is
covered without a side hypothesis; for `m ≥ 1` the reduction is the identity.
-/
import FamilyRun
import FamilyGame
namespace Family

/-! ### Tags -/

/-- Normal form of a position modulo the eventual periodicity of `gv`. -/
def tg (N p s : Nat) : Nat := if s < N then s else N + (s - N) % p

theorem gv_tg (gpre gper : List Nat) (x : Nat) :
    gv gpre gper (tg gpre.length gper.length x) = gv gpre gper x := by
  unfold tg gv
  by_cases h : x < gpre.length
  · simp [h]
  · have h2 : ¬ (gpre.length + (x - gpre.length) % gper.length < gpre.length) := by omega
    simp only [h, h2, ite_false]
    rw [Nat.add_sub_cancel_left, Nat.mod_mod]

theorem tg_add (N p a b : Nat) : tg N p (tg N p a + tg N p b) = tg N p (a + b) := by
  unfold tg
  by_cases ha : a < N <;> by_cases hb : b < N
  · simp [ha, hb]
  · have h1 : ¬ (a + (N + (b - N) % p) < N) := by omega
    have h2 : ¬ (a + b < N) := by omega
    simp only [ha, hb, h1, h2, ite_true, ite_false]
    have : a + (N + (b - N) % p) - N = a + (b - N) % p := by omega
    rw [this, Nat.add_mod_mod]
    congr 2; omega
  · have h1 : ¬ (N + (a - N) % p + b < N) := by omega
    have h2 : ¬ (a + b < N) := by omega
    simp only [ha, hb, h1, h2, ite_true, ite_false]
    have : N + (a - N) % p + b - N = (a - N) % p + b := by omega
    rw [this, Nat.mod_add_mod]
    congr 2; omega
  · have h1 : ¬ (N + (a - N) % p + (N + (b - N) % p) < N) := by omega
    have h2 : ¬ (a + b < N) := by omega
    simp only [ha, hb, h1, h2, ite_false]
    have : N + (a - N) % p + (N + (b - N) % p) - N = N + (a - N) % p + (b - N) % p := by omega
    rw [this]
    have e : (N + (a - N) % p + (b - N) % p) % p = (N + (a - N) + (b - N)) % p := by
      simp [Nat.add_mod]
    rw [e]
    congr 2; omega

/-- Row tag of row `A`. -/
def rtag (gpre gper : List Nat) (A : Nat) : Nat := tg gpre.length gper.length A

/-! ### Letters -/

/-- `stackSum f k = Σ_{i<k} 2^i * [f i]`, built so that bit `i` is `f i` (shift-friendly form). -/
def stackSum (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => (if f 0 then 1 else 0) + 2 * stackSum (fun i => f (i + 1)) k

theorem testBit_cons (b : Bool) (y i : Nat) :
    ((if b then 1 else 0) + 2 * y).testBit i = (match i with | 0 => b | i + 1 => y.testBit i) := by
  cases i with
  | zero => cases b <;> simp [Nat.testBit_zero] <;> omega
  | succ i =>
    rw [Nat.testBit_succ]
    have : ((if b then 1 else 0) + 2 * y) / 2 = y := by cases b <;> simp <;> omega
    rw [this]

theorem testBit_stackSum (f : Nat → Bool) (k i : Nat) :
    (stackSum f k).testBit i = (decide (i < k) && f i) := by
  induction k generalizing f i with
  | zero => simp [stackSum]
  | succ k ih =>
    rw [stackSum, testBit_cons]
    cases i with
    | zero => simp
    | succ i => simp [ih]

theorem sum_map_two_mul (l : List Nat) (g : Nat → Nat) :
    (l.map fun i => 2 * g i).sum = 2 * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x t ih => simp [ih, Nat.mul_add]

theorem stackSum_eq_sum (f : Nat → Bool) (k : Nat) :
    stackSum f k = ((List.range k).map fun i => 2 ^ i * if f i then 1 else 0).sum := by
  induction k generalizing f with
  | zero => simp [stackSum]
  | succ k ih =>
    rw [stackSum, ih, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [Function.comp_def, Nat.pow_zero, Nat.one_mul]
    congr 1
    rw [← sum_map_two_mul]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [Nat.pow_succ]; ac_rfl

def mOf (S1 : List Nat) : Nat := S1.foldl max 0

/-- Cell `(row, col)` of the row table: row `row` at offset `col` (false for negative rows). -/
def bitR (S1 gpre gper : List Nat) (row : Int) (col : Nat) : Bool :=
  if row < 0 then false else PG S1 gpre gper row.toNat (row.toNat + col)

def R (S1 gpre gper : List Nat) (a d : Nat) : Bool := PG S1 gpre gper a (a + d)

/-- Stack letter at column `x` after rows `0 .. n-1`. -/
def St (S1 gpre gper : List Nat) (n x : Nat) : Nat :=
  stackSum (fun i => bitR S1 gpre gper ((n : Int) - 1 - i) (x + i)) (mOf S1)

theorem bitR_nat (S1 gpre gper : List Nat) (n i c : Nat) :
    bitR S1 gpre gper ((n : Int) - 1 - i) c =
      if i < n then PG S1 gpre gper (n - 1 - i) (n - 1 - i + c) else false := by
  by_cases h : i < n
  · have e : ((n : Int) - 1 - i).toNat = n - 1 - i := by omega
    have h' : ¬ ((n : Int) - 1 - i < 0) := by omega
    simp [bitR, h, h', e]
  · have h' : (n : Int) - 1 - i < 0 := by omega
    simp [bitR, h, h']

theorem St_zero (S1 gpre gper : List Nat) (x : Nat) : St S1 gpre gper 0 x = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [St, testBit_stackSum]
  rw [bitR_nat]
  simp

theorem testBit_St (S1 gpre gper : List Nat) (n x i : Nat) :
    (St S1 gpre gper n x).testBit i =
      (decide (i < mOf S1) && bitR S1 gpre gper ((n : Int) - 1 - i) (x + i)) := by
  rw [St, testBit_stackSum]

/-! ### The transducer -/

structure TState where
  u0 : Nat
  hist : Nat
  dtag : Nat
  cnt : Nat
  deriving DecidableEq, Repr

def tinit : TState := ⟨0, 0, 0, 0⟩

/-- New bit of the row being built (row tag `rt`), reading letter `x` in state `q`. -/
def newBit (S1 gpre gper : List Nat) (rt : Nat) (q : TState) (x : Nat) : Bool :=
  let u0' := if q.cnt = 0 then x else q.u0
  decide (gv gpre gper rt ≠ gv gpre gper (rt + q.dtag)) &&
    S1.all fun s => !x.testBit (s - 1) &&
      (if s ≤ q.cnt then !q.hist.testBit (s - 1) else !u0'.testBit (s - q.cnt - 1))

def tstep (S1 gpre gper : List Nat) (rt : Nat) (q : TState) (x : Nat) : TState × Nat :=
  let m := mOf S1
  let u0' := if q.cnt = 0 then x else q.u0
  let b := if newBit S1 gpre gper rt q x then 1 else 0
  (⟨if q.cnt + 1 < m then u0' else 0, (q.hist * 2 + b) % 2 ^ m,
    tg gpre.length gper.length (q.dtag + 1), min (q.cnt + 1) m⟩,
   (b + 2 * (x % 2 ^ (m - 1))) % 2 ^ m)

/-! ### Correctness -/

/-- Hist word: bit `j` is the new-row bit at `d-1-j` (0 if negative). -/
def histW (S1 gpre gper : List Nat) (n d : Nat) : Nat :=
  stackSum (fun j => decide (j < d) && PG S1 gpre gper n (n + (d - 1 - j))) (mOf S1)

/-- The state of the run before reading position `d`. -/
def sd (S1 gpre gper : List Nat) (n d : Nat) : TState :=
  ⟨if 0 < d ∧ d < mOf S1 then St S1 gpre gper n 1 else 0, histW S1 gpre gper n d,
    tg gpre.length gper.length d, min d (mOf S1)⟩

theorem foldl_max_ge (l : List Nat) (a : Nat) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => exact Nat.le_refl _
  | cons x t ih => exact Nat.le_trans (Nat.le_max_left a x) (ih _)

theorem le_mOf (S1 : List Nat) (s : Nat) (hs : s ∈ S1) : s ≤ mOf S1 := by
  have key : ∀ (l : List Nat) (a : Nat), s ∈ l → s ≤ l.foldl max a := by
    intro l
    induction l with
    | nil => intro a h; simp at h
    | cons x t ih =>
      intro a h
      rw [List.foldl_cons]
      rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge t _)
      · exact ih _ h
  exact key S1 0 hs

theorem L1 (S1 gpre gper : List Nat) (n d s : Nat) (h0 : 0 < s) (hm : s ≤ mOf S1) :
    ((!(St S1 gpre gper n (d + 1)).testBit (s - 1)) = true) ↔
      (s ≤ n → PG S1 gpre gper (n - s) (n + d) = false) := by
  rw [testBit_St, bitR_nat]
  have e1 : n - 1 - (s - 1) = n - s := by omega
  by_cases h : s ≤ n
  · have h' : s - 1 < n := by omega
    have e2 : n - s + (d + 1 + (s - 1)) = n + d := by omega
    have hh : s - 1 < mOf S1 := by omega
    rw [if_pos h', e1, show d + 1 + (s - 1) = d + s by omega, show n - s + (d + s) = n + d by omega]
    simp [hh, h]
  · have h' : ¬ (s - 1 < n) := by omega
    simp [h', h]

theorem L2a (S1 gpre gper : List Nat) (n d s : Nat) (h0 : 0 < s) (hm : s ≤ mOf S1) (hd : s ≤ d) :
    ((!(histW S1 gpre gper n d).testBit (s - 1)) = true) ↔
      (s ≤ n + d → PG S1 gpre gper n (n + d - s) = false) := by
  rw [histW, testBit_stackSum]
  have hh : s - 1 < mOf S1 := by omega
  have e : n + (d - 1 - (s - 1)) = n + d - s := by omega
  simp [hh, show s - 1 < d by omega, e, show s ≤ n + d by omega]

theorem L2b (S1 gpre gper : List Nat) (n d s : Nat) (h0 : 0 < s) (hm : s ≤ mOf S1) (hd : d < s) :
    ((!(St S1 gpre gper n 1).testBit (s - d - 1)) = true) ↔
      (s ≤ n + d → PG S1 gpre gper n (n + d - s) = false) := by
  rw [testBit_St, bitR_nat]
  have hh : s - d - 1 < mOf S1 := by omega
  by_cases h : s ≤ n + d
  · have h' : s - d - 1 < n := by omega
    rw [if_pos h', show n - 1 - (s - d - 1) = n + d - s by omega,
      show n + d - s + (1 + (s - d - 1)) = n by omega, PG_symm]
    simp [hh, h]
  · have h' : ¬ (s - d - 1 < n) := by omega
    simp [h', h]

theorem nb_eq (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (n d : Nat) :
    newBit S1 gpre gper (tg gpre.length gper.length n) (sd S1 gpre gper n d)
      (St S1 gpre gper n (d + 1)) = PG S1 gpre gper n (n + d) := by
  rw [Bool.eq_iff_iff, PG_eq S1 gpre gper hS]
  unfold newBit
  simp only [sd, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  have hg : gv gpre gper (tg gpre.length gper.length n + tg gpre.length gper.length d)
      = gv gpre gper (n + d) := by
    rw [← gv_tg gpre gper (tg gpre.length gper.length n + tg gpre.length gper.length d), tg_add,
      gv_tg]
  simp only [hg, gv_tg, decide_eq_true_eq]
  refine and_congr Iff.rfl (forall_congr' fun s => forall_congr' fun hs => ?_)
  have h0 := hS s hs
  have hm := le_mOf S1 s hs
  refine and_congr (L1 S1 gpre gper n d s h0 hm) ?_
  by_cases hd : s ≤ d
  · have : s ≤ min d (mOf S1) := by omega
    simp only [this, ↓reduceIte]
    exact (L2a S1 gpre gper n d s h0 hm hd).trans (by simp)
  · have : ¬ s ≤ min d (mOf S1) := by omega
    simp only [this, ↓reduceIte]
    have hmin : min d (mOf S1) = d := by omega
    have hu : (if d = 0 then St S1 gpre gper n (d + 1)
        else if 0 < d ∧ d < mOf S1 then St S1 gpre gper n 1 else 0) = St S1 gpre gper n 1 := by
      by_cases hd0 : d = 0
      · subst hd0; simp
      · simp [hd0, show d < mOf S1 by omega, Nat.pos_of_ne_zero hd0]
    simp only [hmin, hu]
    exact L2b S1 gpre gper n d s h0 hm (by omega)

theorem tg_add_right (N p a b : Nat) : tg N p (tg N p a + b) = tg N p (a + b) := by
  unfold tg
  by_cases ha : a < N
  · simp [ha]
  · have h1 : ¬ (N + (a - N) % p + b < N) := by omega
    have h2 : ¬ (a + b < N) := by omega
    simp only [ha, h1, h2, ite_false]
    have : N + (a - N) % p + b - N = (a - N) % p + b := by omega
    rw [this, Nat.mod_add_mod]
    congr 2; omega

theorem hist_step (S1 gpre gper : List Nat) (n d : Nat) :
    ((histW S1 gpre gper n d) * 2 + (if PG S1 gpre gper n (n + d) = true then 1 else 0)) % 2 ^ mOf S1 =
      histW S1 gpre gper n (d + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, show histW S1 gpre gper n d * 2 + (if PG S1 gpre gper n (n + d) = true then 1 else 0)
    = (if PG S1 gpre gper n (n + d) = true then 1 else 0) + 2 * histW S1 gpre gper n d by omega,
    testBit_cons]
  cases i with
  | zero => simp only [histW, testBit_stackSum]; simp
  | succ i =>
    simp only [histW, testBit_stackSum]
    have e : d + 1 - 1 - (i + 1) = d - 1 - i := by omega
    by_cases h1 : i + 1 < mOf S1
    · have : i < mOf S1 := by omega
      by_cases h2 : i < d <;> simp [h1, this, h2, e, show d - (i + 1) = d - 1 - i by omega,
        show i + 1 < d + 1 ↔ i < d by omega]
    · simp [h1]

theorem tstep_sd (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (n d : Nat) :
    tstep S1 gpre gper (tg gpre.length gper.length n) (sd S1 gpre gper n d) (St S1 gpre gper n (d + 1)) =
      (sd S1 gpre gper n (d + 1), St S1 gpre gper (n + 1) d) := by
  have hb := nb_eq S1 gpre gper hS n d
  unfold tstep
  rw [hb]
  refine Prod.ext ?_ ?_
  · dsimp only
    simp only [sd, TState.mk.injEq]
    refine ⟨?_, hist_step S1 gpre gper n d, tg_add_right _ _ _ _, by omega⟩
    by_cases h : d + 1 < mOf S1
    · have e : min d (mOf S1) = d := by omega
      have e2 : min d (mOf S1) + 1 < mOf S1 := by omega
      by_cases hd : d = 0
      · subst hd; simp [h]
      · simp [e, h, hd, Nat.pos_of_ne_zero hd, show d < mOf S1 by omega]
    · have e2 : ¬ (min d (mOf S1) + 1 < mOf S1) := by omega
      simp [e2, h]
  · dsimp only
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, testBit_cons, testBit_St]
    cases i with
    | zero => rw [bitR_nat]; simp
    | succ i =>
      dsimp only
      rw [Nat.testBit_mod_two_pow, testBit_St, bitR_nat, bitR_nat]
      have e1 : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
      have e2 : d + (i + 1) = d + 1 + i := by omega
      have e3 : (i + 1 < n + 1) ↔ i < n := by omega
      by_cases h1 : i + 1 < mOf S1
      · have : i < mOf S1 := by omega
        have h3 : i < mOf S1 - 1 := by omega
        simp [h1, this, h3, e1, e2, e3, show n - (i + 1) = n - 1 - i by omega]
      · have h3 : ¬ i < mOf S1 - 1 := by omega
        simp [h1, h3]

theorem sd_zero (S1 gpre gper : List Nat) (n : Nat) : sd S1 gpre gper n 0 = tinit := by
  have h : histW S1 gpre gper n 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp [histW, testBit_stackSum]
  have h2 : tg gpre.length gper.length 0 = 0 := by
    unfold tg
    by_cases h : 0 < gpre.length
    · simp [h]
    · have : gpre.length = 0 := by omega
      simp [this]
  simp [sd, tinit, h, h2]

theorem stateAt_eq (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (n d : Nat) :
    stateAt (tstep S1 gpre gper (rtag gpre gper n)) tinit (fun x => St S1 gpre gper n (x + 1)) d =
      sd S1 gpre gper n d := by
  induction d with
  | zero => exact (sd_zero S1 gpre gper n).symm
  | succ d ih =>
    rw [stateAt, ih]
    exact congrArg Prod.fst (tstep_sd S1 gpre gper hS n d)

/-- Main theorem: the transducer run on the tail of `St n` produces `St (n+1)`. -/
theorem St_succ (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (n d : Nat) :
    St S1 gpre gper (n + 1) d =
      outAt (tstep S1 gpre gper (rtag gpre gper n)) tinit (fun x => St S1 gpre gper n (x + 1)) d := by
  unfold outAt
  rw [stateAt_eq S1 gpre gper hS]
  exact (congrArg Prod.snd (tstep_sd S1 gpre gper hS n d)).symm

/-- Extraction of a cell from the stack (needs `S1 ≠ []`, i.e. `0 < m`). -/
theorem R_of_St (S1 gpre gper : List Nat) (hm : 0 < mOf S1) (a d : Nat) :
    R S1 gpre gper a d = decide (St S1 gpre gper (a + 1) d % 2 = 1) := by
  rw [← Nat.testBit_zero, testBit_St, bitR_nat]
  simp [R, hm]

/-! ### Sanity check (finite prefix, kernel evaluation) -/

/-- Output letters of the transducer over a finite input word. -/
def runList (S1 gpre gper : List Nat) (rt : Nat) : TState → List Nat → List Nat
  | _, [] => []
  | q, x :: xs => (tstep S1 gpre gper rt q x).2 :: runList S1 gpre gper rt (tstep S1 gpre gper rt q x).1 xs

/-- Stack after `n` rows as a list of `K` letters, by iterating the transducer. -/
def stackList (S1 gpre gper : List Nat) : Nat → Nat → List Nat
  | 0, K => List.replicate K 0
  | n + 1, K => runList S1 gpre gper (rtag gpre gper n) tinit ((stackList S1 gpre gper n (K + 1)).drop 1)

-- the transducer's row bits agree with `PG` on a few rows
example : (List.range 4).all (fun n => (List.range 5).all fun d =>
    (((stackList [1, 2, 5, 6] [] [0, 1, 2, 3, 4] (n + 1) 5).getD d 0) % 2 == 1) ==
      PG [1, 2, 5, 6] [] [0, 1, 2, 3, 4] n (n + d)) = true := by
  decide +kernel

end Family
