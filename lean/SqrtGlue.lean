/-
Glue between the model on global rows (`Mrow a d`, d = b - a) and the virtual tables.
`RhsN M a d` is the game equation of the cell (a, d) of a table M on (row, column) pairs, with
the reflection at the diagonal (a move (a, b - s) with s > d lands on (a + d - s, s - d)).
-/
import SqrtJump
namespace SqrtM

def Ucell (M : Nat → Nat → Bool) (a d s : Nat) : Bool := s ≤ a && M (a - s) (d + s)
def Wcell (M : Nat → Nat → Bool) (a d s : Nat) : Bool :=
  s ≤ a + d && (if s ≤ d then M a (d - s) else M (a + d - s) (s - d))

def RhsN (M : Nat → Nat → Bool) (a d : Nat) : Bool :=
  d % 5 != 0 && !Ucell M a d 1 && !Wcell M a d 1 && !Ucell M a d 2 && !Wcell M a d 2
    && !Ucell M a d 5 && !Wcell M a d 5 && !Ucell M a d 6 && !Wcell M a d 6

theorem rhs_expand (M : Nat → Nat → Bool) (a d : Nat) (ha : 6 ≤ a) (hd : 6 ≤ d) :
    RhsN M a d = (d % 5 != 0 && !M (a-1) (d+1) && !M a (d-1) && !M (a-2) (d+2) && !M a (d-2)
      && !M (a-5) (d+5) && !M a (d-5) && !M (a-6) (d+6) && !M a (d-6)) := by
  have u : ∀ s, s ≤ a → Ucell M a d s = M (a - s) (d + s) := by
    intro s hs; simp [Ucell, hs]
  have w : ∀ s, s ≤ d → Wcell M a d s = M a (d - s) := by
    intro s hs; simp [Wcell, hs, show s ≤ a + d by omega]
  unfold RhsN
  rw [u 1 (by omega), u 2 (by omega), u 5 (by omega), u 6 (by omega),
    w 1 (by omega), w 2 (by omega), w 5 (by omega), w 6 (by omega)]

theorem mod5_bne (d : Nat) (w : Int) (hw : w % 5 = 0) :
    ((((d : Int) - w) % 5 != 0) = (d % 5 != 0)) := by
  by_cases h : d % 5 = 0
  · have : ((d : Int) - w) % 5 = 0 := by omega
    simp [h, this]
  · have : ((d : Int) - w) % 5 ≠ 0 := by omega
    rw [bne_iff_ne.mpr this, bne_iff_ne.mpr h]

/-- transfer to a forward table F (rows r - i) -/
theorem tf_F (F : Nat → Int → Bool) (M : Nat → Nat → Bool) (a r d : Nat) (w : Int)
    (hw : w % 5 = 0) (ha : 6 ≤ a) (hr : 6 ≤ r) (hd : 6 ≤ d)
    (h : ∀ i, i ≤ 6 → ∀ y, d ≤ y + 6 → y ≤ d + 6 → M (a - i) y = F (r - i) ((y : Int) - w)) :
    (M a d == RhsN M a d) = EqF F r ((d : Int) - w) := by
  rw [rhs_expand M a d ha hd]
  have c : ∀ i y, i ≤ 6 → d ≤ y + 6 → y ≤ d + 6 → M (a - i) y = F (r - i) ((y : Int) - w) :=
    fun i y h1 h2 h3 => h i h1 y h2 h3
  have c0 := c 0 d (by omega) (by omega) (by omega)
  have a1 := c 1 (d + 1) (by omega) (by omega) (by omega)
  have a2 := c 2 (d + 2) (by omega) (by omega) (by omega)
  have a5 := c 5 (d + 5) (by omega) (by omega) (by omega)
  have a6 := c 6 (d + 6) (by omega) (by omega) (by omega)
  have b1 := c 0 (d - 1) (by omega) (by omega) (by omega)
  have b2 := c 0 (d - 2) (by omega) (by omega) (by omega)
  have b5 := c 0 (d - 5) (by omega) (by omega) (by omega)
  have b6 := c 0 (d - 6) (by omega) (by omega) (by omega)
  simp only [Nat.sub_zero] at c0 b1 b2 b5 b6
  rw [show ((d + 1 : Nat) : Int) - w = ((d : Int) - w) + 1 by omega] at a1
  rw [show ((d + 2 : Nat) : Int) - w = ((d : Int) - w) + 2 by omega] at a2
  rw [show ((d + 5 : Nat) : Int) - w = ((d : Int) - w) + 5 by omega] at a5
  rw [show ((d + 6 : Nat) : Int) - w = ((d : Int) - w) + 6 by omega] at a6
  rw [show ((d - 1 : Nat) : Int) - w = ((d : Int) - w) - 1 by omega] at b1
  rw [show ((d - 2 : Nat) : Int) - w = ((d : Int) - w) - 2 by omega] at b2
  rw [show ((d - 5 : Nat) : Int) - w = ((d : Int) - w) - 5 by omega] at b5
  rw [show ((d - 6 : Nat) : Int) - w = ((d : Int) - w) - 6 by omega] at b6
  unfold EqF
  rw [a1, a2, a5, a6, b1, b2, b5, b6, c0, mod5_bne d w hw]

/-- transfer to a backward (R phase) table F (rows s + i) -/
theorem tf_R (F : Nat → Int → Bool) (M : Nat → Nat → Bool) (a s d : Nat) (w : Int)
    (hw : w % 5 = 0) (ha : 6 ≤ a) (hd : 6 ≤ d)
    (h : ∀ i, i ≤ 6 → ∀ y, d ≤ y + 6 → y ≤ d + 6 → M (a - i) y = F (s + i) ((y : Int) - w)) :
    (M a d == RhsN M a d) = EqR F s ((d : Int) - w) := by
  rw [rhs_expand M a d ha hd]
  have c : ∀ i y, i ≤ 6 → d ≤ y + 6 → y ≤ d + 6 → M (a - i) y = F (s + i) ((y : Int) - w) :=
    fun i y h1 h2 h3 => h i h1 y h2 h3
  have c0 := c 0 d (by omega) (by omega) (by omega)
  have a1 := c 1 (d + 1) (by omega) (by omega) (by omega)
  have a2 := c 2 (d + 2) (by omega) (by omega) (by omega)
  have a5 := c 5 (d + 5) (by omega) (by omega) (by omega)
  have a6 := c 6 (d + 6) (by omega) (by omega) (by omega)
  have b1 := c 0 (d - 1) (by omega) (by omega) (by omega)
  have b2 := c 0 (d - 2) (by omega) (by omega) (by omega)
  have b5 := c 0 (d - 5) (by omega) (by omega) (by omega)
  have b6 := c 0 (d - 6) (by omega) (by omega) (by omega)
  simp only [Nat.sub_zero, Nat.add_zero] at c0 b1 b2 b5 b6
  rw [show ((d + 1 : Nat) : Int) - w = ((d : Int) - w) + 1 by omega] at a1
  rw [show ((d + 2 : Nat) : Int) - w = ((d : Int) - w) + 2 by omega] at a2
  rw [show ((d + 5 : Nat) : Int) - w = ((d : Int) - w) + 5 by omega] at a5
  rw [show ((d + 6 : Nat) : Int) - w = ((d : Int) - w) + 6 by omega] at a6
  rw [show ((d - 1 : Nat) : Int) - w = ((d : Int) - w) - 1 by omega] at b1
  rw [show ((d - 2 : Nat) : Int) - w = ((d : Int) - w) - 2 by omega] at b2
  rw [show ((d - 5 : Nat) : Int) - w = ((d : Int) - w) - 5 by omega] at b5
  rw [show ((d - 6 : Nat) : Int) - w = ((d : Int) - w) - 6 by omega] at b6
  unfold EqR
  rw [a1, a2, a5, a6, b1, b2, b5, b6, c0, mod5_bne d w hw]

/-- congruence of the Nat equation under a row shift a <-> j (reads rows a-6..a, columns <= d+6) -/
theorem RhsN_congr (M G : Nat → Nat → Bool) (a j d : Nat) (hj : 6 ≤ j) (hja : j ≤ a)
    (h : ∀ i, i ≤ 6 → ∀ y, y ≤ d + 6 → M (a - i) y = G (j - i) y) : RhsN M a d = RhsN G j d := by
  have u : ∀ s, s ≤ 6 → Ucell M a d s = Ucell G j d s := by
    intro s hs
    have e1 := h s hs (d + s) (by omega)
    simp [Ucell, e1, show s ≤ a by omega, show s ≤ j by omega]
  have w : ∀ s, s ≤ 6 → Wcell M a d s = Wcell G j d s := by
    intro s hs
    by_cases hsd : s ≤ d
    · have e1 := h 0 (by omega) (d - s) (by omega)
      simp only [Nat.sub_zero] at e1
      simp [Wcell, hsd, e1, show s ≤ a + d by omega, show s ≤ j + d by omega]
    · have e1 := h (s - d) (by omega) (s - d) (by omega)
      rw [show a - (s - d) = a + d - s by omega, show j - (s - d) = j + d - s by omega] at e1
      simp [Wcell, hsd, e1, show s ≤ a + d by omega, show s ≤ j + d by omega]
  unfold RhsN
  rw [u 1 (by omega), u 2 (by omega), u 5 (by omega), u 6 (by omega),
    w 1 (by omega), w 2 (by omega), w 5 (by omega), w 6 (by omega)]

end SqrtM
