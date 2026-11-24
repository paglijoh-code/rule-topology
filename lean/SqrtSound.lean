/-
Soundness: the model satisfies M1's game equation, hence (by `Eqn.unique`) equals `outcome`.
`outcome_eq : outcome [1,2,5,6] [1,2,3,4] a b = model a b` for all a, b.
-/
import SqrtSmall
import LeadASound
namespace LeadA

theorem mex_eq (l : List Nat) (c : Nat) (h1 : c ∉ l) (h2 : ∀ m < c, m ∈ l) : mex l = c := by
  have := mex_spec l
  by_cases h : mex l < c
  · exact absurd (h2 _ h) this.2
  · by_cases h' : c < mex l
    · exact absurd (this.1 c h') h1
    · omega

theorem sgFn_1234 : ∀ x, sgFn [1, 2, 3, 4] x = x % 5 := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    have hin : ∀ m, m ∈ (([1, 2, 3, 4] : List Nat).filterMap fun s =>
        if h : 0 < s ∧ s ≤ x then some (sgFn [1, 2, 3, 4] (x - s)) else none) ↔
        ∃ s, 1 ≤ s ∧ s ≤ 4 ∧ s ≤ x ∧ (x - s) % 5 = m := by
      intro m
      rw [mem_moves]
      constructor
      · rintro ⟨s, hs, h0, h1, h2⟩
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
        refine ⟨s, by omega, by omega, h1, ?_⟩
        rw [← h2, ih (x - s) (by omega)]
      · rintro ⟨s, h0, h1, h2, h3⟩
        refine ⟨s, ?_, by omega, h2, ?_⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
        · rw [ih (x - s) (by omega), h3]
    rw [sgFn_eq]
    apply mex_eq
    · rw [hin]
      rintro ⟨s, h0, h1, h2, h3⟩
      omega
    · intro m hm
      rw [hin]
      exact ⟨x % 5 - m, by omega, by omega, by omega, by omega⟩

end LeadA

namespace SqrtM
open LeadA

theorem rhs_iff (M : Nat → Nat → Bool) (a d : Nat) : RhsN M a d = true ↔
    d % 5 ≠ 0 ∧ ∀ s, s ∈ [1, 2, 5, 6] → Ucell M a d s = false ∧ Wcell M a d s = false := by
  unfold RhsN
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, List.mem_cons,
    List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, and_assoc]

theorem round_exists : ∀ n, ∃ k, tk k ≤ 13 + n ∧ 13 + n < tk (k + 1) := by
  intro n
  induction n with
  | zero => exact ⟨0, by decide, by decide⟩
  | succ n ih =>
    obtain ⟨k, h1, h2⟩ := ih
    by_cases h : 13 + (n + 1) < tk (k + 1)
    · exact ⟨k, by omega, h⟩
    · have := tk_succ (k + 1)
      have := tk_13 (k + 1)
      have : 14 ≤ gap (k + 1) := by unfold gap; omega
      exact ⟨k + 1, by omega, by omega⟩

theorem model_eq_chk (a d : Nat) : chk a d = true := by
  by_cases ha : a < 181
  · exact small a ha d
  · obtain ⟨k, h1, h2⟩ := round_exists (a - 13)
    rw [show 13 + (a - 13) = a by omega] at h1 h2
    have hk : 3 ≤ k := by
      by_cases hk : 3 ≤ k
      · exact hk
      · have := tk_mono (k + 1) 3 (by omega)
        have e3 : tk 3 = 181 := rfl
        omega
    have hs := tk_succ k
    have := big k (a - tk k) d hk (by omega)
    rw [show tk k + (a - tk k) = a by omega] at this
    exact this

theorem model_eq (a d : Nat) : Mrow a d = RhsN Mrow a d := beq_iff_eq.1 (model_eq_chk a d)

def Q (a b : Nat) : Prop := model a b = true

theorem model_symm (a b : Nat) : model a b = model b a := by
  unfold model
  by_cases h1 : a ≤ b
  · by_cases h2 : b ≤ a
    · have : a = b := by omega
      subst this; rfl
    · rw [if_pos h1, if_neg h2]
  · have h2 : b ≤ a := by omega
    rw [if_neg h1, if_pos h2]

theorem model_le (a b : Nat) (h : a ≤ b) : model a b = Mrow a (b - a) := by
  unfold model; rw [if_pos h]

theorem Q_eq_le (a b : Nat) (hab : a ≤ b) :
    Q a b ↔ ¬ IsP1 [1, 2, 3, 4] a b ∧ (∀ s ∈ [1, 2, 5, 6], 0 < s → s ≤ a → ¬ Q (a - s) b) ∧
      (∀ s ∈ [1, 2, 5, 6], 0 < s → s ≤ b → ¬ Q a (b - s)) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  have hP : IsP1 [1, 2, 3, 4] a (a + d) ↔ d % 5 = 0 := by
    rw [IsP1_iff_sg _ (a + (a + d)) a (a + d) rfl, sgFn_1234, sgFn_1234]
    omega
  have hU : ∀ s, s ≤ a → (Q (a - s) (a + d) ↔ Mrow (a - s) (d + s) = true) := by
    intro s hs
    unfold Q
    rw [model_le _ _ (by omega), show a + d - (a - s) = d + s by omega]
  have hW : ∀ s, s ≤ a + d → (Q a (a + d - s) ↔
      (if s ≤ d then Mrow a (d - s) else Mrow (a + d - s) (s - d)) = true) := by
    intro s hs
    unfold Q
    by_cases hsd : s ≤ d
    · rw [model_le _ _ (by omega), show a + d - s - a = d - s by omega, if_pos hsd]
    · rw [model_symm, model_le _ _ (by omega), show a - (a + d - s) = s - d by omega, if_neg hsd]
  have hQ : Q a (a + d) ↔ Mrow a d = true := by
    unfold Q; rw [model_le _ _ (by omega), show a + d - a = d by omega]
  rw [hQ, model_eq a d, rhs_iff, hP]
  constructor
  · rintro ⟨h0, hs⟩
    refine ⟨h0, ?_, ?_⟩
    · intro s hs' _ hsa hq
      have := (hs s hs').1
      unfold Ucell at this
      rw [(hU s hsa).1 hq] at this
      simp [hsa] at this
    · intro s hs' _ hsb hq
      have := (hs s hs').2
      unfold Wcell at this
      rw [(hW s hsb).1 hq] at this
      simp [hsb] at this
  · rintro ⟨h0, hA, hB⟩
    refine ⟨h0, fun s hs' => ⟨?_, ?_⟩⟩
    · unfold Ucell
      by_cases hsa : s ≤ a
      · have := hA s hs' (by simp at hs'; omega) hsa
        have h2 : Mrow (a - s) (d + s) = false := by
          have := (not_congr (hU s hsa)).1 this
          simpa using this
        simp [hsa, h2]
      · simp [hsa]
    · unfold Wcell
      by_cases hsb : s ≤ a + d
      · have := hB s hs' (by simp at hs'; omega) hsb
        have h2 : (if s ≤ d then Mrow a (d - s) else Mrow (a + d - s) (s - d)) = false := by
          have := (not_congr (hW s hsb)).1 this
          simpa using this
        simp [hsb, h2]
      · simp [hsb]

theorem Q_symm (a b : Nat) : Q a b ↔ Q b a := by unfold Q; rw [model_symm]

theorem Q_eqn : Eqn [1, 2, 5, 6] (IsP1 [1, 2, 3, 4]) Q := by
  intro a b
  by_cases hab : a ≤ b
  · exact Q_eq_le a b hab
  · have h := Q_eq_le b a (by omega)
    rw [Q_symm a b, h, IsP1_symm [1, 2, 3, 4] b a]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun s hs h0 hsa hq => h3 s hs h0 hsa ((Q_symm _ _).1 hq),
        fun s hs h0 hsb hq => h2 s hs h0 hsb ((Q_symm _ _).1 hq)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun s hs h0 hsb hq => h3 s hs h0 hsb ((Q_symm _ _).1 hq),
        fun s hs h0 hsa hq => h2 s hs h0 hsa ((Q_symm _ _).1 hq)⟩

/-- the outcome of M1's game for S1 = [1,2,5,6], S2 = [1,2,3,4] is the explicit model -/
theorem outcome_eq : ∀ a b, outcome [1, 2, 5, 6] [1, 2, 3, 4] a b = model a b := by
  intro a b
  have h := Eqn.unique (IsP0_eqn [1, 2, 5, 6] [1, 2, 3, 4]) Q_eqn a b
  have h2 := outcome_iff [1, 2, 5, 6] [1, 2, 3, 4] a b
  unfold Q at h
  cases h3 : outcome [1, 2, 5, 6] [1, 2, 3, 4] a b <;> cases h4 : model a b
  · rfl
  · have := h.2 h4; rw [← h2] at this; simp [h3] at this
  · have := h.1 (h2.1 h3); simp [h4] at this
  · rfl

end SqrtM
