/-
The jump rows: the first six rows r = 0..5 of round k read the last six rows (s = 1..6 rows to go)
of round k - 1, whose wall is 10 cells to the left.  In the coordinate e = d - w_k the previous
round's cell is `Rrow s (e + 10)`.  The "jump table" `Jt i e` (i = r + 6) glues both:
rows i >= 6 are `Lrow (i - 6)`, rows i < 6 are `Rrow (6 - i) (e + 10)`.
`J_ok`: the equation holds for i in [6, 11] and every e.
-/
import SqrtR
namespace SqrtM

def Jt (i : Nat) (e : Int) : Bool := if 6 ≤ i then Lrow (i - 6) e else Rrow (6 - i) (e + 10)

theorem EqF_shift1 (f : Nat → Int → Bool) (r : Nat) (hr : 6 ≤ r) (e : Int) :
    EqF (fun r e => f (r + 1) e) r e = EqF f (r + 1) e := by
  unfold EqF
  dsimp only
  have h1 : r - 1 + 1 = r + 1 - 1 := by omega
  have h2 : r - 2 + 1 = r + 1 - 2 := by omega
  have h5 : r - 5 + 1 = r + 1 - 5 := by omega
  have h6 : r - 6 + 1 = r + 1 - 6 := by omega
  rw [h1, h2, h5, h6]

/-- left of e = -41 every jump row is the pure alpha medium (shifted by one row) -/
theorem Jt_left (i : Nat) (hi : i ≤ 11) (e : Int) (he : e ≤ -35) : Jt i e = fa (i + 1) e := by
  unfold Jt fa
  by_cases h6 : 6 ≤ i
  · rw [if_pos h6]
    unfold Lrow p1L
    rw [if_pos (by omega)]
    apply alpha_congr
    omega
  · rw [if_neg h6]
    by_cases h1 : 6 - i = 1
    · unfold Rrow
      rw [if_pos h1, if_pos (by omega)]
      unfold gamma
      apply alpha_congr
      omega
    · unfold Rrow p1R
      rw [if_neg h1, if_pos (by omega)]
      unfold gamma
      apply alpha_congr
      omega

/-- right of e = 30 every jump row is the tail table (shifted by one row) -/
theorem Jt_right (i : Nat) (hi : i ≤ 11) (e : Int) (he : 30 ≤ e) : Jt i e = ft (i + 1) e := by
  have hb := pw_bounds ((i - 6) % 7) (by omega)
  unfold Jt ft
  by_cases h6 : 6 ≤ i
  · rw [if_pos h6]
    unfold Lrow p1L
    rw [if_neg (by omega), if_neg (by omega)]
    have : (i - 6) % 7 = (i + 1) % 7 := by omega
    rw [this]
  · rw [if_neg h6]
    have hb2 := pw_bounds (zR (6 - i)) (by unfold zR; omega)
    unfold Rrow p1R
    by_cases h1 : 6 - i = 1
    · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]
      have : zR (6 - i) = (i + 1) % 7 := by unfold zR; omega
      rw [this]
      apply tl_congr; omega
    · rw [if_neg h1, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have : zR (6 - i) = (i + 1) % 7 := by unfold zR; omega
      rw [this]
      apply tl_congr; omega

theorem J_win : ∀ i : Nat, i < 6 → ∀ x : Nat, x < 76 →
    EqF Jt (i + 6) ((x : Int) - 40) = true := by
  decide +kernel

theorem J_ok (i : Nat) (h6 : 6 ≤ i) (h11 : i ≤ 11) (e : Int) : EqF Jt i e = true := by
  have hs : ∀ s : Nat, s ∈ [0, 1, 2, 5, 6] → s ≤ 6 := by
    intro s hs; simp at hs; omega
  by_cases h1 : e ≤ -41
  · rw [EqF_congr Jt (fun r e => fa (r + 1) e) i e
      (fun s hs' => Jt_left _ (by have := hs s hs'; omega) _ (by have := hs s hs'; omega))
      (fun s hs' => Jt_left _ (by have := hs s hs'; omega) _ (by have := hs s hs'; omega))]
    rw [EqF_shift1 fa i h6]
    exact fa_ok _ (by omega) e
  by_cases h2 : 36 ≤ e
  · rw [EqF_congr Jt (fun r e => ft (r + 1) e) i e
      (fun s hs' => Jt_right _ (by have := hs s hs'; omega) _ (by have := hs s hs'; omega))
      (fun s hs' => Jt_right _ (by have := hs s hs'; omega) _ (by have := hs s hs'; omega))]
    rw [EqF_shift1 ft i h6]
    exact ft_ok _ (by omega) e
  · have := J_win (i - 6) (by omega) (e + 40).toNat (by omega)
    have e' : (((e + 40).toNat : Nat) : Int) - 40 = e := by omega
    rwa [e', show i - 6 + 6 = i by omega] at this

end SqrtM
