import FamilyCheck
/-!
Kernel-fast versions of the row step.  `tstepF` is `tstep` with the `S1`-loop replaced by three
bit masks and with raw `Nat.*` operations; `tstepF_eq` proves it equal to `tstep`.  `rowStepF` also
uses a Bool equality on `TState` for the fixed-point tests; `rowStepF_eq` proves it equal to `rowStep`.
-/
namespace Family

/-! ### Masks -/

def maskOf (S1 : List Nat) : Nat := S1.foldl (fun a s => a ||| 1 <<< (s - 1)) 0

theorem testBit_foldl_mask (l : List Nat) : ∀ (acc i : Nat),
    (l.foldl (fun a s => a ||| 1 <<< (s - 1)) acc).testBit i =
      (acc.testBit i || decide (∃ s ∈ l, s - 1 = i)) := by
  induction l with
  | nil => intro acc i; simp
  | cons s l ih =>
    intro acc i
    rw [List.foldl_cons, ih]
    simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, List.mem_cons]
    by_cases h : s - 1 = i <;> simp [h] <;> grind

theorem maskOf_testBit (S1 : List Nat) (i : Nat) :
    (maskOf S1).testBit i = true ↔ ∃ s ∈ S1, s - 1 = i := by
  unfold maskOf; rw [testBit_foldl_mask]; simp

theorem and_zero_iff (x y : Nat) : x &&& y = 0 ↔ ∀ i, ¬ (x.testBit i = true ∧ y.testBit i = true) := by
  constructor
  · intro h i hi
    have := congrArg (fun z => z.testBit i) h
    simp [hi.1, hi.2] at this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := h i
    simp only [Nat.testBit_and, Nat.zero_testBit]
    cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all

theorem mask_x (S1 : List Nat) (x : Nat) :
    x &&& maskOf S1 = 0 ↔ ∀ s ∈ S1, x.testBit (s - 1) = false := by
  rw [and_zero_iff]
  constructor
  · intro h s hs
    rw [Bool.eq_false_iff]; intro hx
    exact h (s - 1) ⟨by simpa using hx, (maskOf_testBit S1 _).2 ⟨s, hs, rfl⟩⟩
  · intro h i ⟨h1, h2⟩
    obtain ⟨s, hs, rfl⟩ := (maskOf_testBit S1 _).1 h2
    rw [h s hs] at h1; cases h1

theorem mask_hist (S1 : List Nat) (hS : ∀ s ∈ S1, 0 < s) (hist c : Nat) :
    hist &&& (maskOf S1 &&& (2 ^ c - 1)) = 0 ↔ ∀ s ∈ S1, s ≤ c → hist.testBit (s - 1) = false := by
  rw [and_zero_iff]
  constructor
  · intro h s hs hsc
    rw [Bool.eq_false_iff]; intro hx
    refine h (s - 1) ⟨by simpa using hx, ?_⟩
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    have := (maskOf_testBit S1 (s - 1)).2 ⟨s, hs, rfl⟩
    have h0 := hS s hs
    simp [this]; omega
  · intro h i ⟨h1, h2⟩
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨s, hs, rfl⟩ := (maskOf_testBit S1 _).1 h2.1
    have h0 := hS s hs
    rw [h s hs (by omega)] at h1; cases h1

theorem mask_u0 (S1 : List Nat) (hS : ∀ s ∈ S1, 0 < s) (u c : Nat) :
    u &&& (maskOf S1 >>> c) = 0 ↔ ∀ s ∈ S1, c < s → u.testBit (s - c - 1) = false := by
  rw [and_zero_iff]
  constructor
  · intro h s hs hsc
    rw [Bool.eq_false_iff]; intro hx
    refine h (s - c - 1) ⟨by simpa using hx, ?_⟩
    rw [Nat.testBit_shiftRight]
    have := (maskOf_testBit S1 (c + (s - c - 1))).2 ⟨s, hs, by omega⟩
    exact this
  · intro h i ⟨h1, h2⟩
    rw [Nat.testBit_shiftRight] at h2
    obtain ⟨s, hs, hsi⟩ := (maskOf_testBit S1 _).1 h2
    have h0 := hS s hs
    have := h s hs (by omega)
    rw [show s - c - 1 = i by omega] at this
    rw [this] at h1; cases h1

/-! ### Test table -/

def tmOf (gpre gper : List Nat) (rt : Nat) : Nat :=
  (List.range (gpre.length + gper.length)).foldl
    (fun a d => if gv gpre gper rt ≠ gv gpre gper (rt + d) then a ||| 1 <<< d else a) 0

theorem testBit_foldl_tm (c : Nat → Prop) [DecidablePred c] (l : List Nat) : ∀ (acc i : Nat),
    (l.foldl (fun a d => if c d then a ||| 1 <<< d else a) acc).testBit i =
      (acc.testBit i || decide (i ∈ l ∧ c i)) := by
  induction l with
  | nil => intro acc i; simp
  | cons d l ih =>
    intro acc i
    rw [List.foldl_cons, ih]
    by_cases hc : c d
    · simp only [hc, ↓reduceIte, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, List.mem_cons]
      by_cases h : d = i <;> simp [h] <;> grind
    · simp only [hc, ↓reduceIte, List.mem_cons]
      by_cases h : d = i <;> simp [h] <;> grind

theorem tmOf_testBit (gpre gper : List Nat) (rt i : Nat) :
    (tmOf gpre gper rt).testBit i = true ↔
      (i < gpre.length + gper.length ∧ gv gpre gper rt ≠ gv gpre gper (rt + i)) := by
  unfold tmOf
  rw [testBit_foldl_tm (fun d => gv gpre gper rt ≠ gv gpre gper (rt + d))]
  simp

theorem tg_lt (N p s : Nat) (hp : 0 < p) : tg N p s < N + p := by
  unfold tg
  by_cases h : s < N
  · simp [h]; omega
  · simp only [h, ↓reduceIte]
    have := Nat.mod_lt (s - N) hp
    omega

theorem tg_tg (N p s : Nat) : tg N p (tg N p s) = tg N p s := by
  have h := tg_add_right N p s 0
  simpa [tg_add_right] using h

/-! ### The fast step -/

/-- `tstep` with masks (`mask = maskOf S1`, `tm = tmOf gpre gper rt`, `m = mOf S1`) and raw ops. -/
def tstepF (N p m mask tm : Nat) (q : TState) (x : Nat) : TState × Nat :=
  let u0' := cond (Nat.beq q.cnt 0) x q.u0
  let t := Nat.mod (Nat.shiftRight tm (tg N p q.dtag)) 2
  let a := Nat.add (Nat.add (Nat.land x mask)
    (Nat.land q.hist (Nat.land mask (Nat.sub (Nat.pow 2 q.cnt) 1))))
    (Nat.land u0' (Nat.shiftRight mask q.cnt))
  let b := cond (Nat.beq a 0) t 0
  (⟨cond (Nat.blt (Nat.add q.cnt 1) m) u0' 0,
    Nat.mod (Nat.add (Nat.mul q.hist 2) b) (Nat.pow 2 m),
    tg N p (Nat.add q.dtag 1), cond (Nat.blt q.cnt m) (Nat.add q.cnt 1) m⟩,
   Nat.mod (Nat.add b (Nat.mul 2 (Nat.mod x (Nat.pow 2 (Nat.sub m 1))))) (Nat.pow 2 m))

theorem newBit_iff (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (hp : 0 < gper.length)
    (rt : Nat) (q : TState) (x : Nat) :
    newBit S1 gpre gper rt q x = true ↔
      ((x &&& maskOf S1) + (q.hist &&& (maskOf S1 &&& (2 ^ q.cnt - 1))) +
        ((if q.cnt = 0 then x else q.u0) &&& (maskOf S1 >>> q.cnt)) = 0 ∧
      (tmOf gpre gper rt).testBit (tg gpre.length gper.length q.dtag) = true) := by
  have hg : gv gpre gper (rt + tg gpre.length gper.length q.dtag) = gv gpre gper (rt + q.dtag) := by
    have e : tg gpre.length gper.length (rt + tg gpre.length gper.length q.dtag) =
        tg gpre.length gper.length (rt + q.dtag) := by
      rw [Nat.add_comm rt, Nat.add_comm rt, tg_add_right]
    rw [← gv_tg gpre gper (rt + tg gpre.length gper.length q.dtag), e, gv_tg]
  rw [tmOf_testBit, hg, Nat.add_eq_zero_iff, Nat.add_eq_zero_iff, mask_x, mask_hist S1 hS,
    mask_u0 S1 hS]
  unfold newBit
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, tg_lt _ _ _ hp, true_and,
    Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨⟨fun s hs => (h2 s hs).1, fun s hs hsc => ?_⟩, fun s hs hsc => ?_⟩, h1⟩
    · have := (h2 s hs).2
      simp only [hsc, ↓reduceIte, Bool.not_eq_true'] at this
      exact this
    · have := (h2 s hs).2
      simp only [show ¬ s ≤ q.cnt by omega, ↓reduceIte, Bool.not_eq_true'] at this
      exact this
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h4, fun s hs => ⟨h1 s hs, ?_⟩⟩
    by_cases hsc : s ≤ q.cnt
    · simp only [hsc, ↓reduceIte, Bool.not_eq_true']; exact h2 s hs hsc
    · simp only [hsc, ↓reduceIte, Bool.not_eq_true']; exact h3 s hs (by omega)

/-- Notation form of `tstepF` (definitionally equal). -/
def tstepN (N p m mask tm : Nat) (q : TState) (x : Nat) : TState × Nat :=
  let u0' := if q.cnt = 0 then x else q.u0
  let b := if (x &&& mask) + (q.hist &&& (mask &&& (2 ^ q.cnt - 1))) + (u0' &&& (mask >>> q.cnt)) = 0
    then (tm >>> tg N p q.dtag) % 2 else 0
  (⟨if q.cnt + 1 < m then u0' else 0, (q.hist * 2 + b) % 2 ^ m, tg N p (q.dtag + 1),
    min (q.cnt + 1) m⟩, (b + 2 * (x % 2 ^ (m - 1))) % 2 ^ m)

theorem tstepF_N (N p m mask tm : Nat) : tstepF N p m mask tm = tstepN N p m mask tm := by
  funext q x
  unfold tstepF tstepN
  have hm : (cond (Nat.blt q.cnt m) (q.cnt + 1) m) = min (q.cnt + 1) m := by
    simp only [cond_eq_if, Nat.blt_eq]
    by_cases h : q.cnt < m <;> simp [h] <;> omega
  simp only [cond_eq_if, Nat.beq_eq, Nat.blt_eq, hm]
  rfl

theorem tstepF_eq (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (hp : 0 < gper.length)
    (rt : Nat) :
    tstepF gpre.length gper.length (mOf S1) (maskOf S1) (tmOf gpre gper rt) =
      tstep S1 gpre gper rt := by
  funext q x
  have hb : cond (Nat.beq ((x &&& maskOf S1) + (q.hist &&& (maskOf S1 &&& (2 ^ q.cnt - 1))) +
        ((if q.cnt = 0 then x else q.u0) &&& (maskOf S1 >>> q.cnt))) 0)
      ((tmOf gpre gper rt >>> tg gpre.length gper.length q.dtag) % 2) 0 =
      (if newBit S1 gpre gper rt q x then 1 else 0) := by
    have key := newBit_iff S1 gpre gper hS hp rt q x
    have hT : ((tmOf gpre gper rt >>> tg gpre.length gper.length q.dtag) % 2 = 1) ↔
        (tmOf gpre gper rt).testBit (tg gpre.length gper.length q.dtag) = true := by
      have := Nat.testBit_zero (tmOf gpre gper rt >>> tg gpre.length gper.length q.dtag)
      rw [Nat.testBit_shiftRight, Nat.add_zero] at this
      rw [this]; exact decide_eq_true_iff.symm
    have hlt := Nat.mod_lt (tmOf gpre gper rt >>> tg gpre.length gper.length q.dtag) (show 0 < 2 by omega)
    by_cases hP : newBit S1 gpre gper rt q x = true
    · obtain ⟨ha, ht⟩ := key.1 hP
      rw [if_pos hP, ha]
      simp [hT.2 ht]
    · rw [if_neg hP]
      by_cases ha : ((x &&& maskOf S1) + (q.hist &&& (maskOf S1 &&& (2 ^ q.cnt - 1))) +
          ((if q.cnt = 0 then x else q.u0) &&& (maskOf S1 >>> q.cnt))) = 0
      · have : ¬ (tmOf gpre gper rt).testBit (tg gpre.length gper.length q.dtag) = true :=
          fun h => hP (key.2 ⟨ha, h⟩)
        rw [ha]
        have : (tmOf gpre gper rt >>> tg gpre.length gper.length q.dtag) % 2 ≠ 1 := fun h => this (hT.1 h)
        simp; omega
      · have : Nat.beq ((x &&& maskOf S1) + (q.hist &&& (maskOf S1 &&& (2 ^ q.cnt - 1))) +
          ((if q.cnt = 0 then x else q.u0) &&& (maskOf S1 >>> q.cnt))) 0 = false :=
          Bool.eq_false_iff.2 (fun h => ha (Nat.eq_of_beq_eq_true h))
        rw [this]; rfl
  rw [tstepF_N]
  unfold tstepN tstep
  simp only [cond_eq_if, Nat.beq_eq] at hb
  simp only [hb]

/-! ### Fast state equality and the fast row step -/

def stEqB (a b : TState) : Bool :=
  Nat.beq a.u0 b.u0 && Nat.beq a.hist b.hist && Nat.beq a.dtag b.dtag && Nat.beq a.cnt b.cnt

theorem stEqB_eq : ∀ {a b : TState}, stEqB a b = true → a = b := by
  intro a b h
  obtain ⟨a1, a2, a3, a4⟩ := a
  obtain ⟨b1, b2, b3, b4⟩ := b
  simp only [stEqB, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  subst h1 h2 h3 h4; rfl

/-- `DecidableEq TState` through `stEqB`; equal to the derived instance (subsingleton). -/
def decFast : DecidableEq TState := fun a b =>
  if h : stEqB a b = true then isTrue (stEqB_eq h)
  else isFalse (fun e => h (by subst e; simp [stEqB]))

theorem decFast_eq : decFast = (inferInstance : DecidableEq TState) := by
  funext a b; exact Subsingleton.elim _ _

/-- Fast `rowStep`: same recipe with `tstepF`, `decFast` and the table data computed once. -/
def rowStepF (S1 gpre gper : List Nat) (r : Nat) (s : Shape) (n : List Nat) (mv : List Move) :
    Option (Shape × List Nat) :=
  if s.x0 = [] then none else
  match @sstep TState (tstepF gpre.length gper.length (mOf S1) (maskOf S1)
      (tmOf gpre gper (rtag gpre gper r))) decFast tinit { s with x0 := s.x0.tail } with
  | none => none
  | some (s', u) =>
    if pwB u n then
      match applyMove s' (.tshrink (shrinkC gper.length s'.z)) with
      | none => none
      | some (s'', _) => applyMoves s'' (nsub n u) mv
    else none

theorem rowStepF_eq (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (hp : 0 < gper.length)
    (r : Nat) (s : Shape) (n : List Nat) (mv : List Move) :
    rowStepF S1 gpre gper r s n mv = rowStep S1 gpre gper r s n mv := by
  unfold rowStepF rowStep
  rw [tstepF_eq S1 gpre gper hS hp, decFast_eq]
  rfl

/-! ### Bool equality of lists and shapes -/

def listEqB : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && listEqB as bs
  | _, _ => false

theorem listEqB_iff : ∀ (a b : List Nat), listEqB a b = true ↔ a = b := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [listEqB]
  | cons x xs ih =>
    intro b
    cases b with
    | nil => simp [listEqB]
    | cons y ys => simp [listEqB, Nat.beq_eq, ih]

def blocksEqB : Blocks → Blocks → Bool
  | [], [] => true
  | (y, x) :: bs, (y', x') :: bs' => listEqB y y' && listEqB x x' && blocksEqB bs bs'
  | _, _ => false

theorem blocksEqB_iff : ∀ (a b : Blocks), blocksEqB a b = true ↔ a = b := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [blocksEqB]
  | cons p ps ih =>
    intro b
    obtain ⟨y, x⟩ := p
    cases b with
    | nil => simp [blocksEqB]
    | cons q qs =>
      obtain ⟨y', x'⟩ := q
      simp [blocksEqB, listEqB_iff, ih]

def shapeEqB (a b : Shape) : Bool :=
  listEqB a.x0 b.x0 && blocksEqB a.blocks b.blocks && listEqB a.z b.z

theorem shapeEqB_iff (a b : Shape) : shapeEqB a b = true ↔ a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp [shapeEqB, listEqB_iff, blocksEqB_iff, and_assoc]

/-! ### Fast segments -/

def runRowsF (S1 gpre gper : List Nat) : Nat → Shape → List Nat → List (List Move) →
    Option (Shape × List Nat)
  | _, s, n, [] => some (s, n)
  | r, s, n, mv :: mvs =>
    match rowStepF S1 gpre gper r s n mv with
    | none => none
    | some (s', n') => runRowsF S1 gpre gper (r + 1) s' n' mvs

theorem runRowsF_eq (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (hp : 0 < gper.length) :
    ∀ (mvs : List (List Move)) (r : Nat) (s : Shape) (n : List Nat),
      runRowsF S1 gpre gper r s n mvs = runRows S1 gpre gper r s n mvs := by
  intro mvs
  induction mvs with
  | nil => intro r s n; rfl
  | cons mv mvs ih =>
    intro r s n
    simp only [runRowsF, runRows, rowStepF_eq S1 gpre gper hS hp]
    cases rowStep S1 gpre gper r s n mv with
    | none => rfl
    | some t => exact ih _ _ _

def runSegsF (S1 gpre gper : List Nat) : Nat → Shape → List Nat → List Seg →
    Option (Nat × Shape × List Nat)
  | r, s, n, [] => some (r, s, n)
  | r, s, n, g :: gs =>
    match runRowsF S1 gpre gper r s n g.rows with
    | none => none
    | some (s', n') =>
      if shapeEqB s' g.shape && listEqB n' g.cnt then
        runSegsF S1 gpre gper (r + g.rows.length) g.shape g.cnt gs
      else none

theorem runSegsF_eq (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (hp : 0 < gper.length) :
    ∀ (gs : List Seg) (r : Nat) (s : Shape) (n : List Nat),
      runSegsF S1 gpre gper r s n gs = runSegs S1 gpre gper r s n gs := by
  intro gs
  induction gs with
  | nil => intro r s n; rfl
  | cons g gs ih =>
    intro r s n
    simp only [runSegsF, runSegs, runRowsF_eq S1 gpre gper hS hp]
    cases runRows S1 gpre gper r s n g.rows with
    | none => rfl
    | some t =>
      obtain ⟨s', n'⟩ := t
      by_cases hc : s' = g.shape ∧ n' = g.cnt
      · have : (shapeEqB s' g.shape && listEqB n' g.cnt) = true := by
          simp [shapeEqB_iff, listEqB_iff, hc.1, hc.2]
        dsimp only
        rw [if_pos this, if_pos hc]
        exact ih _ _ _
      · have : ¬ (shapeEqB s' g.shape && listEqB n' g.cnt) = true := by
          simpa [shapeEqB_iff, listEqB_iff] using hc
        dsimp only
        rw [if_neg this, if_neg hc]

/-- Fast initial-run check: `checkInitial` with `runSegsF`. -/
def checkInitialF (S1 gpre gper : List Nat) (start : List Move) (gs : List Seg) :
    Option (Nat × Shape × List Nat) :=
  match applyMoves (sigma0 gper.length) [] start with
  | none => none
  | some (s, n) => runSegsF S1 gpre gper 0 s n gs

theorem checkInitialF_sound (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s)
    (hp : 0 < gper.length) {start : List Move} {gs : List Seg} {r : Nat} {s : Shape}
    {n : List Nat} (h : checkInitialF S1 gpre gper start gs = some (r, s, n)) :
    ∀ x, decode s n x = St S1 gpre gper r x := by
  apply checkInitial_sound S1 gpre gper hS (start := start) (gs := gs)
  unfold checkInitialF at h
  unfold checkInitial
  cases h1 : applyMoves (sigma0 gper.length) [] start with
  | none => simp [h1] at h
  | some t =>
    obtain ⟨s0, n0⟩ := t
    simp only [h1] at h ⊢
    rw [← runSegsF_eq S1 gpre gper hS hp]
    exact h

/-! ### One segment as a stand-alone Bool check -/

/-- Rows `r, r+1, ...` from the literal state `(s, n)` must end exactly in `(s1, n1)`. -/
def segCheckF (S1 gpre gper : List Nat) (r : Nat) (s : Shape) (n : List Nat)
    (rows : List (List Move)) (s1 : Shape) (n1 : List Nat) : Bool :=
  match runRowsF S1 gpre gper r s n rows with
  | none => false
  | some (s', n') => shapeEqB s' s1 && listEqB n' n1

theorem segCheckF_sound (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (hp : 0 < gper.length)
    {r : Nat} {s s1 : Shape} {n n1 : List Nat} {rows : List (List Move)}
    (h : segCheckF S1 gpre gper r s n rows s1 n1 = true)
    (hd : ∀ x, decode s n x = St S1 gpre gper r x) :
    ∀ x, decode s1 n1 x = St S1 gpre gper (r + rows.length) x := by
  unfold segCheckF at h
  cases h1 : runRowsF S1 gpre gper r s n rows with
  | none => simp [h1] at h
  | some t =>
    obtain ⟨s', n'⟩ := t
    simp only [h1, Bool.and_eq_true, shapeEqB_iff, listEqB_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [runRowsF_eq S1 gpre gper hS hp] at h1
    exact runRows_sound S1 gpre gper hS rows r h1 hd

/-- Chaining step: the checked segment starts at a literal equal to the previous end literal. -/
theorem seg_next (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (hp : 0 < gper.length)
    {r r1 : Nat} {s sp s1 : Shape} {n np n1 : List Nat} {rows : List (List Move)}
    (h : segCheckF S1 gpre gper r s n rows s1 n1 = true) (hr : r + rows.length = r1)
    (hs : (shapeEqB sp s && listEqB np n) = true)
    (hd : ∀ x, decode sp np x = St S1 gpre gper r x) :
    ∀ x, decode s1 n1 x = St S1 gpre gper r1 x := by
  simp only [Bool.and_eq_true, shapeEqB_iff, listEqB_iff] at hs
  obtain ⟨rfl, rfl⟩ := hs
  subst hr
  exact segCheckF_sound S1 gpre gper hS hp h hd

theorem start_sound (S1 gpre gper : List Nat) {start : List Move} {s : Shape} {n : List Nat}
    (h : applyMoves (sigma0 gper.length) [] start = some (s, n)) :
    ∀ x, decode s n x = St S1 gpre gper 0 x := by
  intro x
  rw [← applyMoves_sound start h x, sigma0_decode, St_zero]

end Family
