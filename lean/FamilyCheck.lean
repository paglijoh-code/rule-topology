import FamilyStack
import FamilyBlock
/-!
Bool checker for the concrete part of a wall certificate (the initial run) and the symbolic
row step.  `rowStep` = drop the first letter, `sstep`, shrink `z`, then the certificate's moves.
-/
namespace Family

/-- `u ≤ n` pointwise, same length (Bool form of `Pw`). -/
def pwB : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => decide (a ≤ b) && pwB as bs
  | _, _ => false

theorem pwB_Pw : ∀ {u n : List Nat}, pwB u n = true → Pw u n := by
  intro u
  induction u with
  | nil => intro n h; cases n <;> simp_all [pwB, Pw]
  | cons a as ih =>
    intro n h
    cases n with
    | nil => simp [pwB] at h
    | cons b bs =>
      simp only [pwB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, ih h.2⟩

/-- Apply a list of moves in order, threading the counters. -/
def applyMoves : Shape → List Nat → List Move → Option (Shape × List Nat)
  | s, n, [] => some (s, n)
  | s, n, m :: ms =>
    match applyMove s m with
    | none => none
    | some (s', e) =>
      match e.apply n with
      | none => none
      | some n' => applyMoves s' n' ms

theorem applyMoves_sound : ∀ (ms : List Move) {s s' : Shape} {n n' : List Nat},
    applyMoves s n ms = some (s', n') → ∀ d, decode s n d = decode s' n' d := by
  intro ms
  induction ms with
  | nil => intro s s' n n' h d; simp only [applyMoves, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | cons m ms ih =>
    intro s s' n n' h d
    simp only [applyMoves] at h
    cases h1 : applyMove s m with
    | none => simp [h1] at h
    | some t =>
      obtain ⟨s1, e⟩ := t
      cases h2 : e.apply n with
      | none => simp [h1, h2] at h
      | some n1 =>
        simp only [h1, h2] at h
        rw [← ih h d, applyMove_sound h1 h2]

/-- Least `c` (from the top) so that `z = w^c` with `|w|` a multiple of `p`. -/
def shrinkC (p : Nat) (z : List Nat) : Nat :=
  (((List.range z.length).map fun i => z.length - i).find? fun c =>
    z.length % c == 0 && (z.length / c) % p == 0 && rep (z.take (z.length / c)) c == z).getD 1

/-- One row of the run on a shape: row index `r`, shape of `St r`, counters `n`. -/
def rowStep (S1 gpre gper : List Nat) (r : Nat) (s : Shape) (n : List Nat) (mv : List Move) :
    Option (Shape × List Nat) :=
  if s.x0 = [] then none else
  match sstep (tstep S1 gpre gper (rtag gpre gper r)) tinit { s with x0 := s.x0.tail } with
  | none => none
  | some (s', u) =>
    if pwB u n then
      match applyMove s' (.tshrink (shrinkC gper.length s'.z)) with
      | none => none
      | some (s'', _) => applyMoves s'' (nsub n u) mv
    else none

/-- Rows `r0, r0+1, ...` with their move lists. -/
def runRows (S1 gpre gper : List Nat) : Nat → Shape → List Nat → List (List Move) →
    Option (Shape × List Nat)
  | _, s, n, [] => some (s, n)
  | r, s, n, mv :: mvs =>
    match rowStep S1 gpre gper r s n mv with
    | none => none
    | some (s', n') => runRows S1 gpre gper (r + 1) s' n' mvs

/-- Σ_0 : no letters yet, `z = 0^p`. -/
def sigma0 (p : Nat) : Shape := ⟨[], [], List.replicate p 0⟩

theorem decode_tail (a : Nat) (t : List Nat) (bs : Blocks) (z n : List Nat) (x : Nat) :
    decode ⟨a :: t, bs, z⟩ n (x + 1) = decode ⟨t, bs, z⟩ n x := rfl

theorem applyTail_id {s s' : Shape} {m : Move} {e : CEdit} (h : applyTail s m = some (s', e)) :
    e = .id := by
  unfold applyTail at h
  by_cases hz : s.z = []
  · simp [hz] at h
  · simp only [hz, ↓reduceIte] at h
    cases hf : tailF s m with
    | none => simp [hf] at h
    | some t =>
      obtain ⟨f, z'⟩ := t
      cases hl : lastEdit f s.x0 s.blocks with
      | none => simp [hf, hl] at h
      | some r4 => simp only [hf, hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm

/-- Soundness of one row. -/
theorem rowStep_sound (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) {r : Nat} {s s' : Shape}
    {n n' : List Nat} {mv : List Move} (h : rowStep S1 gpre gper r s n mv = some (s', n'))
    (hd : ∀ x, decode s n x = St S1 gpre gper r x) :
    ∀ x, decode s' n' x = St S1 gpre gper (r + 1) x := by
  unfold rowStep at h
  by_cases h0 : s.x0 = []
  · simp [h0] at h
  · simp only [h0, ↓reduceIte] at h
    cases h1 : sstep (tstep S1 gpre gper (rtag gpre gper r)) tinit { s with x0 := s.x0.tail } with
    | none => rw [h1] at h; simp at h
    | some t =>
      obtain ⟨s1, u⟩ := t
      rw [h1] at h
      dsimp only at h
      by_cases hp : pwB u n = true
      · simp only [hp, ↓reduceIte] at h
        cases h2 : applyMove s1 (.tshrink (shrinkC gper.length s1.z)) with
        | none => simp [h2] at h
        | some t2 =>
          obtain ⟨s2, e⟩ := t2
          simp only [h2] at h
          have he : e = .id := applyTail_id (by simpa only [applyMove] using h2)
          subst he
          intro x
          obtain ⟨a, t, ht⟩ : ∃ a t, s.x0 = a :: t := by
            cases hx : s.x0 with
            | nil => exact absurd hx h0
            | cons a t => exact ⟨a, t, rfl⟩
          have e1 : (fun x => St S1 gpre gper r (x + 1)) = decode { s with x0 := s.x0.tail } n := by
            funext y
            rw [← hd (y + 1)]
            obtain ⟨x0, bs, z⟩ := s
            simp only at ht ⊢
            subst ht
            exact (decode_tail a t _ _ _ y).symm
          rw [← applyMoves_sound mv h x, ← applyMove_sound h2 (n := nsub n u) rfl,
            ← sstep_sound _ h1 (pwB_Pw hp) x, St_succ S1 gpre gper hS r x, e1]
      · simp [hp] at h

/-- Soundness of a run of rows. -/
theorem runRows_sound (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) :
    ∀ (mvs : List (List Move)) (r : Nat) {s s' : Shape} {n n' : List Nat},
      runRows S1 gpre gper r s n mvs = some (s', n') →
      (∀ x, decode s n x = St S1 gpre gper r x) →
      ∀ x, decode s' n' x = St S1 gpre gper (r + mvs.length) x := by
  intro mvs
  induction mvs with
  | nil =>
    intro r s s' n n' h hd
    simp only [runRows, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using hd
  | cons mv mvs ih =>
    intro r s s' n n' h hd
    simp only [runRows] at h
    cases h1 : rowStep S1 gpre gper r s n mv with
    | none => simp [h1] at h
    | some t =>
      obtain ⟨s1, n1⟩ := t
      simp only [h1] at h
      have := ih (r + 1) h (rowStep_sound S1 gpre gper hS h1 hd)
      intro x
      rw [this x, List.length_cons]
      congr 1; omega

/-- A checkpoint segment: the rows to run, and the literal shape/counters expected at its end. -/
structure Seg where
  rows : List (List Move)
  shape : Shape
  cnt : List Nat
  deriving Repr

/-- Run segment after segment; every segment must end in its literal checkpoint (this also cuts the
kernel's term sharing between segments, which is what keeps memory bounded). -/
def runSegs (S1 gpre gper : List Nat) : Nat → Shape → List Nat → List Seg →
    Option (Nat × Shape × List Nat)
  | r, s, n, [] => some (r, s, n)
  | r, s, n, g :: gs =>
    match runRows S1 gpre gper r s n g.rows with
    | none => none
    | some (s', n') =>
      if s' = g.shape ∧ n' = g.cnt then runSegs S1 gpre gper (r + g.rows.length) g.shape g.cnt gs
      else none

theorem runSegs_sound (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) :
    ∀ (gs : List Seg) (r : Nat) {s s' : Shape} {n n' : List Nat} {r' : Nat},
      runSegs S1 gpre gper r s n gs = some (r', s', n') →
      (∀ x, decode s n x = St S1 gpre gper r x) → ∀ x, decode s' n' x = St S1 gpre gper r' x := by
  intro gs
  induction gs with
  | nil =>
    intro r s s' n n' r' h hd
    simp only [runSegs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact hd
  | cons g gs ih =>
    intro r s s' n n' r' h hd
    simp only [runSegs] at h
    cases h1 : runRows S1 gpre gper r s n g.rows with
    | none => simp [h1] at h
    | some t =>
      obtain ⟨s1, n1⟩ := t
      simp only [h1] at h
      by_cases hc : s1 = g.shape ∧ n1 = g.cnt
      · simp only [hc, and_self, ↓reduceIte] at h
        obtain ⟨rfl, rfl⟩ := hc
        exact ih _ h (runRows_sound S1 gpre gper hS g.rows r h1 hd)
      · simp [hc] at h

/-- Initial run: `start` moves on `Σ_0`, then the segments. Returns the row count, shape and
counters reached. -/
def checkInitial (S1 gpre gper : List Nat) (start : List Move) (gs : List Seg) :
    Option (Nat × Shape × List Nat) :=
  match applyMoves (sigma0 gper.length) [] start with
  | none => none
  | some (s, n) => runSegs S1 gpre gper 0 s n gs

theorem sigma0_decode (p x : Nat) : decode (sigma0 p) [] x = 0 := by
  simp only [decode, fin, finAux, sigma0, List.nil_append, cat, per]
  by_cases h : x % p < p
  · simp [h]
  · simp [h]

theorem checkInitial_sound (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) {start : List Move}
    {gs : List Seg} {r : Nat} {s : Shape} {n : List Nat}
    (h : checkInitial S1 gpre gper start gs = some (r, s, n)) :
    ∀ x, decode s n x = St S1 gpre gper r x := by
  unfold checkInitial at h
  cases h1 : applyMoves (sigma0 gper.length) [] start with
  | none => simp [h1] at h
  | some t =>
    obtain ⟨s0, n0⟩ := t
    simp only [h1] at h
    refine runSegs_sound S1 gpre gper hS gs 0 h ?_
    intro x
    rw [← applyMoves_sound start h1 x, sigma0_decode, St_zero]

end Family
