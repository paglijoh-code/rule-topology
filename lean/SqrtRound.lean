/-
Round structure of the model: `roundOf`, and the cells of `Mrow` read in the coordinates of
`Lrow` / `Rrow` (e = d - w_k).
-/
import SqrtGlue
namespace SqrtM

theorem tk_succ (k : Nat) : tk (k + 1) = tk k + gap k := by
  unfold tk gap
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

theorem tk_mono (k k' : Nat) (h : k ≤ k') : tk k ≤ tk k' := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => rw [← Nat.add_assoc, tk_succ]; have := ih (by omega); omega

theorem tk_ge (k : Nat) : k ≤ tk k := by unfold tk; omega
theorem tk_13 (k : Nat) : 13 ≤ tk k := by unfold tk; omega

theorem roundAux_spec (a k' : Nat) (h1 : tk k' ≤ a) (h2 : a < tk (k' + 1)) :
    ∀ f k, k ≤ k' → k' - k ≤ f → roundAux a f k = k' := by
  intro f
  induction f with
  | zero =>
    intro k hk hf
    have : k = k' := by omega
    subst this; simp [roundAux]
  | succ f ih =>
    intro k hk hf
    unfold roundAux
    by_cases h : tk (k + 1) ≤ a
    · have : k + 1 ≤ k' := by
        by_cases hc : k + 1 ≤ k'
        · exact hc
        · have : k = k' := by omega
          subst this; omega
      rw [if_pos h]; exact ih (k + 1) this (by omega)
    · rw [if_neg h]
      by_cases hc : k + 1 ≤ k'
      · have := tk_mono _ _ hc
        omega
      · omega

theorem roundOf_eq (a k : Nat) (h1 : tk k ≤ a) (h2 : a < tk (k + 1)) : roundOf a = k := by
  have := tk_ge k
  exact roundAux_spec a k h1 h2 a 0 (by omega) (by omega)

theorem Mrow_round (k r d : Nat) (hr : r < gap k) : Mrow (tk k + r) d = Mk k r (d : Int) := by
  have h13 := tk_13 k
  have hs := tk_succ k
  unfold Mrow
  rw [if_neg (by omega), roundOf_eq _ k (by omega) (by omega)]
  congr 1
  omega

theorem cellL (k r a d : Nat) (ha : a = tk k + r) (hr : r < 12 * k + 32) :
    Mrow a d = Lrow r ((d : Int) - wk k) := by
  subst ha
  have : r < gap k := by unfold gap; omega
  rw [Mrow_round k r d this]
  unfold Mk
  rw [if_pos hr]

theorem cellR (k r a d : Nat) (ha : a = tk k + r) (hr : 12 * k + 32 ≤ r) (hr2 : r < gap k) :
    Mrow a d = Rrow (gap k - r) ((d : Int) - wk k) := by
  subst ha
  rw [Mrow_round k r d hr2]
  unfold Mk
  rw [if_neg (by omega)]

/-- the last six rows of round m, seen from round m + 1 (wall 10 cells to the right) -/
theorem cellPrev (m s a d : Nat) (ha : a + s = tk (m + 1)) (h1 : 1 ≤ s) (h6 : s ≤ 6) :
    Mrow a d = Rrow s ((d : Int) - wk (m + 1) + 10) := by
  have hs := tk_succ m
  have hg : gap m - s + 12 * m + 0 ≥ 0 := by omega
  have e : a = tk m + (gap m - s) := by unfold gap at *; omega
  rw [cellR m (gap m - s) a d e (by unfold gap; omega) (by unfold gap; omega)]
  have : gap m - (gap m - s) = s := by unfold gap; omega
  rw [this]
  congr 1
  unfold wk
  push_cast
  omega

end SqrtM
