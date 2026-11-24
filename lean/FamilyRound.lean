import FamilyStack
import FamilyBlock
/-!
Symbolic row step with affine counters.

A counter is `a*j + e*t + b` (`A3`): `j` is the class index, `t` the iteration inside a cycle (`e = 0`
outside cycles).  `symRow` is `rowStep` of `FamilyCheck` run on such counters: every guard
(`counter - unroll >= 0`, move guards) is checked at both ends of the iteration range, which is enough
because a guard is linear in `t`.  `symRow_sound` re-proves the one-row soundness directly from
`sstep_sound`, `applyMove_sound` and `St_succ`.  The row tag enters only through `tstep`.
-/
namespace Family

/-! ### Affine counters -/

structure A3 where
  a : Int
  e : Int
  b : Int
  deriving DecidableEq, Repr

def A3.ev (x : A3) (j t : Nat) : Int := x.a * j + x.e * t + x.b

/-- Context: class start `j0` and the iteration count `ca*j + cb` of the current phase
(`0 <= t < count`); a single row has `ca = 0, cb = 1`. -/
structure Cx where
  j0 : Nat
  ca : Int
  cb : Int
  deriving Repr

def Cx.dom (cx : Cx) (j t : Nat) : Prop := cx.j0 ≤ j ∧ (t : Int) < cx.ca * j + cx.cb

/-- `a*j + b >= 0` for all `j >= j0`. -/
def posA (j0 : Nat) (a b : Int) : Bool := decide (0 ≤ a) && decide (0 ≤ a * j0 + b)

theorem posA_ev {j0 : Nat} {a b : Int} (h : posA j0 a b = true) {j : Nat} (hj : j0 ≤ j) :
    0 ≤ a * j + b := by
  simp only [posA, Bool.and_eq_true, decide_eq_true_eq] at h
  have : a * (j0 : Int) ≤ a * j := Int.mul_le_mul_of_nonneg_left (by omega) h.1
  omega

/-- `x >= 0` on the whole domain: both ends of the `t` range. -/
def nn (cx : Cx) (x : A3) : Bool :=
  posA cx.j0 x.a x.b && posA cx.j0 (x.a + x.e * cx.ca) (x.b + x.e * (cx.cb - 1))

/-- lower bound of an `nn` counter over the domain: the smaller of its two end values at `j0` -/
def lbOf (cx : Cx) (x : A3) : Int :=
  min (x.a * cx.j0 + x.b) ((x.a + x.e * cx.ca) * cx.j0 + (x.b + x.e * (cx.cb - 1)))

theorem nn_min {cx : Cx} {x : A3} (h : nn cx x = true) {j t : Nat} (hd : cx.dom j t) :
    lbOf cx x ≤ x.ev j t := by
  simp only [nn, Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  have a0 := posA_ev h0 hd.1
  have a1 := posA_ev h1 hd.1
  have g0 : x.a * (cx.j0 : Int) ≤ x.a * j :=
    Int.mul_le_mul_of_nonneg_left (by have := hd.1; omega) (by simp only [posA, Bool.and_eq_true, decide_eq_true_eq] at h0; exact h0.1)
  have g1 : (x.a + x.e * cx.ca) * (cx.j0 : Int) ≤ (x.a + x.e * cx.ca) * j :=
    Int.mul_le_mul_of_nonneg_left (by have := hd.1; omega) (by simp only [posA, Bool.and_eq_true, decide_eq_true_eq] at h1; exact h1.1)
  obtain ⟨-, ht⟩ := hd
  unfold A3.ev lbOf
  have ht0 : (0 : Int) ≤ t := Int.natCast_nonneg t
  by_cases he : 0 ≤ x.e
  · have := Int.mul_nonneg he ht0
    omega
  · have he' : 0 ≤ -x.e := by omega
    have := Int.mul_nonneg he' (show 0 ≤ cx.ca * j + cx.cb - 1 - t by omega)
    have e1 : (x.a + x.e * cx.ca) * j + (x.b + x.e * (cx.cb - 1)) =
        x.a * j + x.b + x.e * (cx.ca * j + cx.cb - 1) := by grind
    have e2 : -x.e * (cx.ca * j + cx.cb - 1 - t) = -(x.e * (cx.ca * j + cx.cb - 1)) + x.e * t := by
      grind
    omega

theorem nn_ev {cx : Cx} {x : A3} (h : nn cx x = true) {j t : Nat} (hd : cx.dom j t) :
    0 ≤ x.ev j t := by
  have := nn_min h hd
  simp only [nn, Bool.and_eq_true, posA, decide_eq_true_eq] at h
  unfold lbOf at this
  omega

def isZ (x : A3) : Bool := x.a == 0 && x.e == 0 && x.b == 0

theorem isZ_ev {x : A3} (h : isZ x = true) (j t : Nat) : x.ev j t = 0 := by
  simp only [isZ, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp [A3.ev, h1, h2, h3]

/-- numeric counters at `(j, t)` -/
def evC (cn : List A3) (j t : Nat) : List Nat := cn.map fun x => (x.ev j t).toNat

/-- all counters are `>= 0` at `(j, t)` -/
def Pos (cn : List A3) (j t : Nat) : Prop := ∀ x ∈ cn, 0 ≤ x.ev j t

theorem Pos_nil (j t : Nat) : Pos [] j t := by intro x hx; simp at hx

theorem Pos_cons {x : A3} {xs : List A3} {j t : Nat} (h1 : 0 ≤ x.ev j t) (h2 : Pos xs j t) :
    Pos (x :: xs) j t := by
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact h1
  · exact h2 y hy

theorem Pos_tail {x : A3} {xs : List A3} {j t : Nat} (h : Pos (x :: xs) j t) : Pos xs j t :=
  fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem Pos_head {x : A3} {xs : List A3} {j t : Nat} (h : Pos (x :: xs) j t) : 0 ≤ x.ev j t :=
  h x (List.mem_cons_self ..)

/-! ### Symbolic counter edits (mirror of `CEdit.apply`) -/

def symAdj (cx : Cx) (d : Int) : Nat → List A3 → Option (List A3)
  | 0, x :: xs => let y := { x with b := x.b + d }; if nn cx y then some (y :: xs) else none
  | i + 1, x :: xs => (symAdj cx d i xs).map (x :: ·)
  | _, [] => none

def symDel (v : Nat) : Nat → List A3 → Option (List A3)
  | 0, x :: xs => if isZ { x with b := x.b - v } then some xs else none
  | i + 1, x :: xs => (symDel v i xs).map (x :: ·)
  | _, [] => none

def symIns (c : Nat) : Nat → List A3 → Option (List A3)
  | 0, xs => some (⟨0, 0, c⟩ :: xs)
  | i + 1, x :: xs => (symIns c i xs).map (x :: ·)
  | _, [] => none

def symEdit (cx : Cx) : CEdit → List A3 → Option (List A3)
  | .id, n => some n
  | .adj i d, n => symAdj cx d i n
  | .del i v, n => symDel v i n
  | .ins i c, n => symIns c i n

theorem symAdj_sound (cx : Cx) (d : Int) : ∀ (i : Nat) {cn cn' : List A3},
    symAdj cx d i cn = some cn' → ∀ {j t : Nat}, cx.dom j t → Pos cn j t →
    adjAt d i (evC cn j t) = some (evC cn' j t) ∧ Pos cn' j t := by
  intro i
  induction i with
  | zero =>
    intro cn cn' h j t hd hp
    cases cn with
    | nil => simp [symAdj] at h
    | cons x xs =>
      simp only [symAdj] at h
      by_cases hn : nn cx { x with b := x.b + d } = true
      · simp only [hn, ↓reduceIte, Option.some.injEq] at h
        subst h
        have h1 := nn_ev hn hd
        have h0 := Pos_head hp
        have e : ({ x with b := x.b + d } : A3).ev j t = x.ev j t + d := by simp [A3.ev]; omega
        rw [e] at h1
        refine ⟨?_, Pos_cons (by rw [e]; exact h1) (Pos_tail hp)⟩
        simp only [evC, List.map_cons, adjAt]
        have : 0 ≤ ((x.ev j t).toNat : Int) + d := by omega
        simp only [this, ↓reduceIte, Option.some.injEq, List.cons.injEq, and_true]
        omega
      · simp [hn] at h
  | succ i ih =>
    intro cn cn' h j t hd hp
    cases cn with
    | nil => simp [symAdj] at h
    | cons x xs =>
      simp only [symAdj] at h
      cases hr : symAdj cx d i xs with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := ih hr hd (Pos_tail hp)
        refine ⟨?_, Pos_cons (Pos_head hp) h2⟩
        simp only [evC, List.map_cons, adjAt]
        have : adjAt d i (List.map (fun x => (x.ev j t).toNat) xs) = some (evC r j t) := h1
        rw [this]; rfl

theorem symDel_sound (v : Nat) : ∀ (i : Nat) {cn cn' : List A3},
    symDel v i cn = some cn' → ∀ {j t : Nat}, Pos cn j t →
    delAt v i (evC cn j t) = some (evC cn' j t) ∧ Pos cn' j t := by
  intro i
  induction i with
  | zero =>
    intro cn cn' h j t hp
    cases cn with
    | nil => simp [symDel] at h
    | cons x xs =>
      simp only [symDel] at h
      by_cases hz : isZ { x with b := x.b - v } = true
      · simp only [hz, ↓reduceIte, Option.some.injEq] at h
        subst h
        have := isZ_ev hz j t
        have e : ({ x with b := x.b - v } : A3).ev j t = x.ev j t - v := by simp [A3.ev]; omega
        rw [e] at this
        refine ⟨?_, Pos_tail hp⟩
        simp only [evC, List.map_cons, delAt]
        have : (x.ev j t).toNat = v := by omega
        simp [this]
      · simp [hz] at h
  | succ i ih =>
    intro cn cn' h j t hp
    cases cn with
    | nil => simp [symDel] at h
    | cons x xs =>
      simp only [symDel] at h
      cases hr : symDel v i xs with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := ih hr (Pos_tail hp)
        refine ⟨?_, Pos_cons (Pos_head hp) h2⟩
        simp only [evC, List.map_cons, delAt]
        have : delAt v i (List.map (fun x => (x.ev j t).toNat) xs) = some (evC r j t) := h1
        rw [this]; rfl

theorem symIns_sound (c : Nat) : ∀ (i : Nat) {cn cn' : List A3},
    symIns c i cn = some cn' → ∀ {j t : Nat}, Pos cn j t →
    insAt c i (evC cn j t) = some (evC cn' j t) ∧ Pos cn' j t := by
  intro i
  induction i with
  | zero =>
    intro cn cn' h j t hp
    simp only [symIns, Option.some.injEq] at h
    subst h
    refine ⟨?_, Pos_cons (by simp [A3.ev]) hp⟩
    simp [evC, insAt, A3.ev]
  | succ i ih =>
    intro cn cn' h j t hp
    cases cn with
    | nil => simp [symIns] at h
    | cons x xs =>
      simp only [symIns] at h
      cases hr : symIns c i xs with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := ih hr (Pos_tail hp)
        refine ⟨?_, Pos_cons (Pos_head hp) h2⟩
        simp only [evC, List.map_cons, insAt]
        have : insAt c i (List.map (fun x => (x.ev j t).toNat) xs) = some (evC r j t) := h1
        rw [this]; rfl

theorem symEdit_sound (cx : Cx) {e : CEdit} {cn cn' : List A3} (h : symEdit cx e cn = some cn')
    {j t : Nat} (hd : cx.dom j t) (hp : Pos cn j t) :
    e.apply (evC cn j t) = some (evC cn' j t) ∧ Pos cn' j t := by
  cases e with
  | id =>
    simp only [symEdit, Option.some.injEq] at h
    subst h; exact ⟨rfl, hp⟩
  | adj i d => exact symAdj_sound cx d i h hd hp
  | del i v => exact symDel_sound v i h hp
  | ins i c => exact symIns_sound c i h hp

/-! ### Symbolic moves and one row -/

/-- `applyMoves` on symbolic counters. -/
def symMoves (cx : Cx) : Shape → List A3 → List Move → Option (Shape × List A3)
  | s, n, [] => some (s, n)
  | s, n, m :: ms =>
    match applyMove s m with
    | none => none
    | some (s', e) =>
      match symEdit cx e n with
      | none => none
      | some n' => symMoves cx s' n' ms

theorem symMoves_sound (cx : Cx) : ∀ (ms : List Move) {s s' : Shape} {n n' : List A3},
    symMoves cx s n ms = some (s', n') → ∀ {j t : Nat}, cx.dom j t → Pos n j t →
    (∀ d, decode s (evC n j t) d = decode s' (evC n' j t) d) ∧ Pos n' j t := by
  intro ms
  induction ms with
  | nil =>
    intro s s' n n' h j t hd hp
    simp only [symMoves, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ => rfl, hp⟩
  | cons m ms ih =>
    intro s s' n n' h j t hd hp
    simp only [symMoves] at h
    cases h1 : applyMove s m with
    | none => simp [h1] at h
    | some r =>
      obtain ⟨s1, e⟩ := r
      cases h2 : symEdit cx e n with
      | none => simp [h1, h2] at h
      | some n1 =>
        simp only [h1, h2] at h
        obtain ⟨he, hp1⟩ := symEdit_sound cx h2 hd hp
        obtain ⟨hd2, hp2⟩ := ih h hd hp1
        refine ⟨fun d => ?_, hp2⟩
        rw [← hd2 d, applyMove_sound h1 he]

/-- Least `c` (from the top) so that `z = w^c` with `|w|` a multiple of `p`. -/
def rShrinkC (p : Nat) (z : List Nat) : Nat :=
  (((List.range z.length).map fun i => z.length - i).find? fun c =>
    z.length % c == 0 && (z.length / c) % p == 0 && rep (z.take (z.length / c)) c == z).getD 1

/-- `sstep`'s `nsub n u` on symbolic counters; every result must be `>= 0` (this is `Pw u n`). -/
def symSub (cx : Cx) : List A3 → List Nat → Option (List A3)
  | [], [] => some []
  | x :: xs, u :: us =>
    let y : A3 := { x with b := x.b - u }
    if nn cx y then (symSub cx xs us).map (y :: ·) else none
  | _, _ => none

theorem symSub_sound (cx : Cx) : ∀ {cn : List A3} {u : List Nat} {cn' : List A3},
    symSub cx cn u = some cn' → ∀ {j t : Nat}, cx.dom j t → Pos cn j t →
    Pw u (evC cn j t) ∧ evC cn' j t = nsub (evC cn j t) u ∧ Pos cn' j t := by
  intro cn
  induction cn with
  | nil =>
    intro u cn' h j t hd hp
    cases u with
    | nil =>
      simp only [symSub, Option.some.injEq] at h
      subst h
      exact ⟨by simp [evC, Pw], by simp [evC, nsub], Pos_nil j t⟩
    | cons => simp [symSub] at h
  | cons x xs ih =>
    intro u cn' h j t hd hp
    cases u with
    | nil => simp [symSub] at h
    | cons k us =>
      simp only [symSub] at h
      by_cases hn : nn cx { x with b := x.b - k } = true
      · cases hr : symSub cx xs us with
        | none => simp [hn, hr] at h
        | some r =>
          simp only [hn, ↓reduceIte, hr, Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨h1, h2, h3⟩ := ih hr hd (Pos_tail hp)
          have hv := nn_ev hn hd
          have e : ({ x with b := x.b - k } : A3).ev j t = x.ev j t - k := by simp [A3.ev]; omega
          rw [e] at hv
          refine ⟨?_, ?_, Pos_cons (by rw [e]; exact hv) h3⟩
          · simp only [evC, List.map_cons, Pw]
            exact ⟨by omega, h1⟩
          · simp only [evC, List.map_cons, nsub, List.zipWith_cons_cons] at h2 ⊢
            rw [h2]
            simp only [List.cons.injEq, and_true]
            omega
      · simp [hn] at h

/-- One row: `rowStep` with symbolic counters and the representative tag `rt` (a tag value). -/
def symRow (S1 gpre gper : List Nat) (cx : Cx) (rt : Nat) (s : Shape) (n : List A3)
    (mv : List Move) : Option (Shape × List A3) :=
  if s.x0 = [] then none else
  match sstep (tstep S1 gpre gper rt) tinit { s with x0 := s.x0.tail } with
  | none => none
  | some (s', u) =>
    match symSub cx n u with
    | none => none
    | some n' =>
      match applyMove s' (.tshrink (rShrinkC gper.length s'.z)) with
      | none => none
      | some (s'', _) => symMoves cx s'' n' mv

theorem applyTail_id' {s s' : Shape} {m : Move} {e : CEdit} (h : applyTail s m = some (s', e)) :
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

theorem decode_tail' (a : Nat) (t : List Nat) (bs : Blocks) (z n : List Nat) (x : Nat) :
    decode ⟨a :: t, bs, z⟩ n (x + 1) = decode ⟨t, bs, z⟩ n x := rfl

/-- Soundness of one symbolic row: row `r` is computed by `tstep rt` (`htag`). -/
theorem symRow_sound (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) {cx : Cx} {rt : Nat}
    {s s' : Shape} {n n' : List A3} {mv : List Move}
    (h : symRow S1 gpre gper cx rt s n mv = some (s', n')) {r j t : Nat} (hd : cx.dom j t)
    (hp : Pos n j t)
    (htag : tstep S1 gpre gper (rtag gpre gper r) = tstep S1 gpre gper rt)
    (hdec : ∀ x, decode s (evC n j t) x = St S1 gpre gper r x) :
    (∀ x, decode s' (evC n' j t) x = St S1 gpre gper (r + 1) x) ∧ Pos n' j t := by
  unfold symRow at h
  by_cases h0 : s.x0 = []
  · simp [h0] at h
  · simp only [h0, ↓reduceIte] at h
    cases h1 : sstep (tstep S1 gpre gper rt) tinit { s with x0 := s.x0.tail } with
    | none => rw [h1] at h; simp at h
    | some t1 =>
      obtain ⟨s1, u⟩ := t1
      rw [h1] at h
      dsimp only at h
      cases h3 : symSub cx n u with
      | none => simp [h3] at h
      | some n1 =>
        simp only [h3] at h
        obtain ⟨hpw, hsub, hp1⟩ := symSub_sound cx h3 hd hp
        cases h2 : applyMove s1 (.tshrink (rShrinkC gper.length s1.z)) with
        | none => simp [h2] at h
        | some t2 =>
          obtain ⟨s2, e⟩ := t2
          simp only [h2] at h
          have he : e = .id := applyTail_id' (by simpa only [applyMove] using h2)
          subst he
          obtain ⟨hmv, hp2⟩ := symMoves_sound cx mv h hd hp1
          refine ⟨fun x => ?_, hp2⟩
          obtain ⟨a, t', ht⟩ : ∃ a t', s.x0 = a :: t' := by
            cases hx : s.x0 with
            | nil => exact absurd hx h0
            | cons a t' => exact ⟨a, t', rfl⟩
          have e1 : (fun x => St S1 gpre gper r (x + 1)) =
              decode { s with x0 := s.x0.tail } (evC n j t) := by
            funext y
            rw [← hdec (y + 1)]
            obtain ⟨x0, bs, z⟩ := s
            simp only at ht ⊢
            subst ht
            exact (decode_tail' a t' _ _ _ y).symm
          rw [← hmv x, ← applyMove_sound h2 (n := evC n1 j t) rfl, hsub,
            ← sstep_sound _ h1 hpw x, St_succ S1 gpre gper hS r x, htag, e1]

/-! ### Row tags: `tstep` sees the row tag only through the test function -/

def testv (gpre gper : List Nat) (x d : Nat) : Bool := decide (gv gpre gper x ≠ gv gpre gper (x + d))

/-- the test tables of rows `x` and `rt` agree on all tags `< N + p` -/
def eqTags (gpre gper : List Nat) (x rt : Nat) : Bool :=
  (List.range (gpre.length + gper.length)).all fun dt => testv gpre gper x dt == testv gpre gper rt dt

theorem gv_add_tg (gpre gper : List Nat) (x d : Nat) :
    gv gpre gper (x + tg gpre.length gper.length d) = gv gpre gper (x + d) := by
  rw [Nat.add_comm x, ← gv_tg gpre gper (tg gpre.length gper.length d + x), tg_add_right,
    gv_tg, Nat.add_comm d]

theorem gv_rtag_add (gpre gper : List Nat) (x d : Nat) :
    gv gpre gper (rtag gpre gper x + d) = gv gpre gper (x + d) := by
  unfold rtag
  rw [← gv_tg gpre gper (tg gpre.length gper.length x + d), tg_add_right, gv_tg]

theorem tg_lt (N p d : Nat) (hp : 0 < p) : tg N p d < N + p := by
  unfold tg
  by_cases h : d < N
  · simp [h]; omega
  · simp only [h, ↓reduceIte]
    have := Nat.mod_lt (d - N) hp
    omega

theorem testv_tg (gpre gper : List Nat) (x d : Nat) :
    testv gpre gper x d = testv gpre gper x (tg gpre.length gper.length d) := by
  unfold testv; rw [gv_add_tg]

theorem eqTags_all {gpre gper : List Nat} (hp : 0 < gper.length) {x rt : Nat}
    (h : eqTags gpre gper x rt = true) (d : Nat) : testv gpre gper x d = testv gpre gper rt d := by
  unfold eqTags at h
  rw [List.all_eq_true] at h
  have := h (tg gpre.length gper.length d) (List.mem_range.2 (tg_lt _ _ _ hp))
  rw [beq_iff_eq] at this
  rw [testv_tg gpre gper x d, testv_tg gpre gper rt d, this]

theorem tstep_congr (S1 gpre gper : List Nat) {rt1 rt2 : Nat}
    (h : newBit S1 gpre gper rt1 = newBit S1 gpre gper rt2) :
    tstep S1 gpre gper rt1 = tstep S1 gpre gper rt2 := by
  funext q x
  unfold tstep
  rw [h]

theorem tstep_eqTags (S1 gpre gper : List Nat) (hp : 0 < gper.length) {x rt : Nat}
    (h : eqTags gpre gper x rt = true) :
    tstep S1 gpre gper (rtag gpre gper x) = tstep S1 gpre gper rt := by
  apply tstep_congr
  funext q y
  unfold newBit
  have := eqTags_all hp h q.dtag
  unfold testv at this
  rw [gv_rtag_add, rtag, gv_tg]
  simp only [this]

theorem nat_mod_eq_of_dvd {a b p : Nat} (h : (p : Int) ∣ (a : Int) - b) : a % p = b % p := by
  have : ((a : Int) % p) = ((b : Int) % p) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd h)
  exact_mod_cast this

theorem gv_cong (gpre gper : List Nat) {x x' : Nat} (hx : gpre.length ≤ x) (hx' : gpre.length ≤ x')
    (h : (gper.length : Int) ∣ (x : Int) - x') : gv gpre gper x = gv gpre gper x' := by
  unfold gv
  have h1 : ¬ x < gpre.length := by omega
  have h2 : ¬ x' < gpre.length := by omega
  simp only [h1, h2, ↓reduceIte]
  have hm : (x - gpre.length) % gper.length = (x' - gpre.length) % gper.length := by
    apply nat_mod_eq_of_dvd
    have : ((x - gpre.length : Nat) : Int) - ((x' - gpre.length : Nat) : Int) = (x : Int) - x' := by omega
    rw [this]; exact h
  rw [hm]

theorem testv_cong (gpre gper : List Nat) {x x' : Nat} (hx : gpre.length ≤ x) (hx' : gpre.length ≤ x')
    (h : (gper.length : Int) ∣ (x : Int) - x') (d : Nat) :
    testv gpre gper x d = testv gpre gper x' d := by
  unfold testv
  rw [gv_cong gpre gper hx hx' h, gv_cong gpre gper (x := x + d) (x' := x' + d) (by omega) (by omega)
    (by rw [show ((x + d : Nat) : Int) - ((x' + d : Nat) : Int) = (x : Int) - x' by omega]; exact h)]

theorem eqTags_cong (gpre gper : List Nat) {x x' : Nat} (hx : gpre.length ≤ x)
    (hx' : gpre.length ≤ x') (h : (gper.length : Int) ∣ (x : Int) - x') (rt : Nat) :
    eqTags gpre gper x rt = eqTags gpre gper x' rt := by
  unfold eqTags
  congr 1
  funext dt
  rw [testv_cong gpre gper hx hx' h]

/-! ### The round-start sequence `t_k` -/

/-- `t (k+1) = t k + alpha * k + beta` -/
def tseq (t0 α β : Nat) : Nat → Nat
  | 0 => t0
  | k + 1 => tseq t0 α β k + α * k + β

theorem tseq_closed (t0 α β : Nat) (k : Nat) :
    2 * (tseq t0 α β k : Int) = 2 * t0 + 2 * β * k + α * k * (k - 1) := by
  induction k with
  | zero => simp [tseq]
  | succ k ih => simp only [tseq]; push_cast; grind

theorem tseq_mono (t0 α β : Nat) {k k' : Nat} (h : k ≤ k') : tseq t0 α β k ≤ tseq t0 α β k' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have := ih (by omega)
    rw [← Nat.add_assoc]
    simp only [tseq]; omega

theorem tseq_per (t0 α β p : Nat) (k : Nat) :
    (p : Int) ∣ (tseq t0 α β (k + 2 * p) : Int) - tseq t0 α β k := by
  have h1 := tseq_closed t0 α β (k + 2 * p)
  have h2 := tseq_closed t0 α β k
  refine ⟨2 * β + α * (2 * k + 2 * p - 1), ?_⟩
  push_cast at h1
  have : 2 * ((tseq t0 α β (k + 2 * p) : Int) - tseq t0 α β k) =
      2 * (p * (2 * β + α * (2 * k + 2 * p - 1))) := by grind
  omega

theorem tseq_per_mul (t0 α β p : Nat) (k m : Nat) :
    (p : Int) ∣ (tseq t0 α β (k + 2 * p * m) : Int) - tseq t0 α β k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := tseq_per t0 α β p (k + 2 * p * m)
    have e : k + 2 * p * (m + 1) = k + 2 * p * m + 2 * p := by rw [Nat.mul_add]; omega
    rw [e]
    have := Int.dvd_add h ih
    have e2 : ((tseq t0 α β (k + 2 * p * m + 2 * p) : Int) - tseq t0 α β (k + 2 * p * m)) +
        ((tseq t0 α β (k + 2 * p * m) : Int) - tseq t0 α β k) =
        (tseq t0 α β (k + 2 * p * m + 2 * p) : Int) - tseq t0 α β k := by omega
    rwa [e2] at this

end Family
