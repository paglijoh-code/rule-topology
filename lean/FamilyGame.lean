/-
M6 game with an explicit periodic Grundy function `g` (lists `gpre`, `gper`), see `docs/certificate-format.md`.
`PG S1 gpre gper a b = true` iff (a,b) is a P-position: `gv a ≠ gv b` and no S1-move reaches a
P-position.  `outcome_eq_PG` bridges to `LeadA.outcome` when `g` is the Sprague-Grundy function of
Sub(S2).
-/
import LeadASound
namespace Family

/-- `g x = gpre[x]` for `x < N`, else `gper[(x - N) % p]` (default 0). -/
def gv (gpre gper : List Nat) (x : Nat) : Nat :=
  if x < gpre.length then gpre.getD x 0 else gper.getD ((x - gpre.length) % gper.length) 0

/-- P-positions, by well-founded recursion on `a + b` (the `0 < s` guard only serves termination). -/
def PG (S1 gpre gper : List Nat) (a b : Nat) : Bool :=
  decide (gv gpre gper a ≠ gv gpre gper b) &&
  S1.all fun s =>
    (if _h : 0 < s ∧ s ≤ a then !PG S1 gpre gper (a - s) b else true) &&
    (if _h : 0 < s ∧ s ≤ b then !PG S1 gpre gper a (b - s) else true)
termination_by a + b
decreasing_by all_goals omega

theorem PG_eq (S1 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s) (a b : Nat) :
    PG S1 gpre gper a b = true ↔ gv gpre gper a ≠ gv gpre gper b ∧
      ∀ s ∈ S1, (s ≤ a → PG S1 gpre gper (a - s) b = false) ∧
        (s ≤ b → PG S1 gpre gper a (b - s) = false) := by
  rw [PG]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine and_congr Iff.rfl (forall_congr' fun s => forall_congr' fun hs => ?_)
  have h0 := hS s hs
  constructor
  · intro h
    refine ⟨fun h1 => ?_, fun h1 => ?_⟩
    · have := h.1; rw [dif_pos ⟨h0, h1⟩] at this; simpa using this
    · have := h.2; rw [dif_pos ⟨h0, h1⟩] at this; simpa using this
  · intro h
    refine ⟨?_, ?_⟩
    · split
      · next h1 => simp [h.1 h1.2]
      · rfl
    · split
      · next h1 => simp [h.2 h1.2]
      · rfl

theorem PG_symm (S1 gpre gper : List Nat) (a b : Nat) :
    PG S1 gpre gper a b = PG S1 gpre gper b a := by
  induction h : a + b using Nat.strongRecOn generalizing a b with
  | _ n ih =>
    conv => rhs; rw [PG]
    rw [PG]
    have e : decide (gv gpre gper a ≠ gv gpre gper b) = decide (gv gpre gper b ≠ gv gpre gper a) := by
      simp [eq_comm]
    rw [e]
    congr 1
    refine List.all_congr rfl ?_
    intro s
    have i1 : 0 < s ∧ s ≤ a → PG S1 gpre gper (a - s) b = PG S1 gpre gper b (a - s) := fun hh =>
      ih (a - s + b) (by omega) (a - s) b rfl
    have i2 : 0 < s ∧ s ≤ b → PG S1 gpre gper a (b - s) = PG S1 gpre gper (b - s) a := fun hh =>
      ih (a + (b - s)) (by omega) a (b - s) rfl
    by_cases h1 : 0 < s ∧ s ≤ a <;> by_cases h2 : 0 < s ∧ s ≤ b
    · simp only [dif_pos h1, dif_pos h2, i1 h1, i2 h2]; exact Bool.and_comm _ _
    · simp only [dif_pos h1, dif_neg h2, i1 h1]; simp
    · simp only [dif_neg h1, dif_pos h2, i2 h2]; simp
    · simp only [dif_neg h1, dif_neg h2]

/-- Bridge: if `g` is the Grundy function of Sub(S2), `PG` is `LeadA.outcome`. -/
theorem outcome_eq_PG (S1 S2 gpre gper : List Nat) (hS : ∀ s ∈ S1, 0 < s)
    (hg : ∀ x, LeadA.sgFn S2 x = gv gpre gper x) (a b : Nat) :
    LeadA.outcome S1 S2 a b = PG S1 gpre gper a b := by
  induction h : a + b using Nat.strongRecOn generalizing a b with
  | _ n ih =>
    rw [Bool.eq_iff_iff, LeadA.outcome_eq, PG_eq S1 gpre gper hS, hg, hg]
    have i1 : ∀ s, 0 < s → s ≤ a → LeadA.outcome S1 S2 (a - s) b = PG S1 gpre gper (a - s) b :=
      fun s h0 hh => ih (a - s + b) (by omega) (a - s) b rfl
    have i2 : ∀ s, 0 < s → s ≤ b → LeadA.outcome S1 S2 a (b - s) = PG S1 gpre gper a (b - s) :=
      fun s h0 hh => ih (a + (b - s)) (by omega) a (b - s) rfl
    constructor
    · rintro ⟨hne, h1, h2⟩
      exact ⟨hne, fun s hs => ⟨fun hh => by rw [← i1 s (hS s hs) hh]; exact h1 s hs (hS s hs) hh,
        fun hh => by rw [← i2 s (hS s hs) hh]; exact h2 s hs (hS s hs) hh⟩⟩
    · rintro ⟨hne, h⟩
      exact ⟨hne, fun s hs h0 hh => by rw [i1 s h0 hh]; exact (h s hs).1 hh,
        fun s hs h0 hh => by rw [i2 s h0 hh]; exact (h s hs).2 hh⟩

/-- The checker's `gval` over `sgList` is `gv` of the split lists. -/
theorem gv_take_drop (gl : List Nat) (gpre gper : Nat) (hl : gl.length = gpre + gper) (hp : 0 < gper)
    (x : Nat) : gv (gl.take gpre) (gl.drop gpre) x = LeadA.gval gl gpre gper x := by
  have h1 : (gl.take gpre).length = gpre := by simp [hl]
  have h2 : (gl.drop gpre).length = gper := by simp [hl]
  unfold gv LeadA.gval
  rw [h1, h2]
  by_cases hx : x < gpre
  · have : x < gpre + gper := by omega
    simp [hx, this, List.getD_eq_getElem?_getD]
  · have hm : (x - gpre) % gper < gper := Nat.mod_lt _ hp
    simp only [hx, ite_false, List.getD_eq_getElem?_getD, List.getElem?_drop]
    by_cases hy : x < gpre + gper
    · have : (x - gpre) % gper = x - gpre := Nat.mod_eq_of_lt (by omega)
      simp only [hy, ite_true, this]; congr 2; omega
    · simp only [hy, ite_false]

/-- From `LeadA.gOk`: `gv` over the split `sgList` lists is the Grundy function of Sub(S2). -/
theorem sgFn_eq_gv (S2 : List Nat) (gpre gper : Nat) (h : LeadA.gOk S2 gpre gper = true) (x : Nat) :
    LeadA.sgFn S2 x =
      gv ((LeadA.sgList S2 (gpre + gper)).take gpre) ((LeadA.sgList S2 (gpre + gper)).drop gpre) x := by
  obtain ⟨hper, hpos, -⟩ := LeadA.gOk_sound S2 gpre gper h
  rw [gv_take_drop _ gpre gper (by rw [LeadA.sgList_eq S2 hpos]; simp) hper, LeadA.gval_eq S2 gpre gper h]

end Family
