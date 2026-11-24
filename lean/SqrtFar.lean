/-
M3 far region of the sqrt wall: beyond the wall (columns d >= 75 + 10 K in rows a < tk (K+1)) the table
`row a d` is the doubly periodic pattern `F (a % 7) (d % 10)` (explicit literal table), hence periodic
with periods 7 in the row and 10 in the column.  Witness family: the cell (t_k, t_k + 23 + 10k) is a
P-position and the far pattern (and its mirror) predicts N there.  Statements use only `LeadA.outcome`
via `SqrtM.row`, the table `F` and literals.
-/
import SqrtCor
namespace SqrtM

/-- the far pattern, rows a mod 7, columns d mod 10 (true = P) -/
def Ftab : List (List Bool) :=
  [[false, true, false, false, false, false, false, false, true, false],
   [false, false, false, true, false, false, true, false, false, false],
   [false, true, false, false, false, false, false, false, true, false],
   [false, false, false, true, false, false, true, false, false, false],
   [false, true, false, false, false, false, false, false, true, false],
   [false, false, true, false, false, false, false, false, false, true],
   [false, false, false, false, true, false, false, true, false, false]]

def F (x y : Nat) : Bool := ((Ftab.getD (x % 7) []).getD (y % 10) false)

theorem F_congr {x x' y y' : Nat} (h1 : x % 7 = x' % 7) (h2 : y % 10 = y' % 10) : F x y = F x' y' := by
  unfold F; rw [h1, h2]

theorem tail_F : ∀ z : Nat, z < 7 → ∀ j : Nat, j < 10 → bit (tailM z) j = F (z + 6) (j + 5) := by
  decide +kernel

theorem tl_F (z : Nat) (hz : z < 7) (n a d : Nat) (h1 : (z + 6) % 7 = a % 7)
    (h2 : (n + 5) % 10 = d % 10) : tl z (n : Int) = F a d := by
  unfold tl
  have e : ((n : Int) % 10).toNat = n % 10 := by omega
  rw [e, tail_F z hz (n % 10) (by omega)]
  exact F_congr (by omega) (by omega)

theorem pw_le : ∀ z : Nat, z < 7 → pw z ≤ 26 := by decide +kernel

theorem far_table (K a d : Nat) (ha : 13 ≤ a) (hK : a < 7 * ((K + 1) * (K + 1)) + 35 * (K + 1) + 13)
    (hd : 75 + 10 * K ≤ d) : row a d = F (a % 7) (d % 10) := by
  obtain ⟨k, h1, h2⟩ := round_exists (a - 13)
  rw [show 13 + (a - 13) = a by omega] at h1 h2
  have h1' : tk k ≤ a := h1
  have h2' : a < tk (k + 1) := h2
  have hkK : k ≤ K := by
    refine Classical.byContradiction fun hc => ?_
    have := tk_mono (K + 1) k (by omega)
    have e : tk (K + 1) = 7 * ((K + 1) * (K + 1)) + 35 * (K + 1) + 13 := rfl
    omega
  have hs := tk_succ k
  have hg : gap k = 14 * (k + 3) := rfl
  have htk : tk k = 7 * (k * k) + 35 * k + 13 := rfl
  obtain ⟨r, hr⟩ : ∃ r, a = tk k + r := ⟨a - tk k, by omega⟩
  have hrg : r < gap k := by omega
  have hwk : wk k = 35 + 10 * (k : Int) := rfl
  have he : (d : Int) - wk k = ((d - 35 - 10 * k : Nat) : Int) := by omega
  have hpw : ∀ z : Nat, z < 7 → pw z ≤ 26 := pw_le
  rw [hr, row_eq, Mrow_round k r d hrg]
  unfold Mk
  by_cases hL : r < 12 * k + 32
  · rw [if_pos hL]
    unfold Lrow
    have hp := hpw (r % 7) (by omega)
    unfold p1L
    rw [if_neg (by omega), if_neg (by omega), he]
    exact tl_F _ (by omega) _ _ _ (by omega) (by omega)
  · rw [if_neg hL]
    unfold Rrow
    have hp := hpw (zR (gap k - r)) (by unfold zR; omega)
    unfold p1R
    by_cases hs1 : gap k - r = 1
    · rw [if_pos hs1, if_neg (by omega), if_neg (by omega), he]
      exact tl_F _ (by unfold zR; omega) _ _ _ (by unfold zR; omega) (by omega)
    · rw [if_neg hs1, if_neg (by omega), if_neg (by omega), if_neg (by omega), he]
      exact tl_F _ (by unfold zR; omega) _ _ _ (by unfold zR; omega) (by omega)

/-- doubly periodic far region: period 7 in the row, period 10 in the column -/
theorem far_periodic (K a d : Nat) (ha : 13 ≤ a)
    (hK : a + 7 < 7 * ((K + 1) * (K + 1)) + 35 * (K + 1) + 13) (hd : 75 + 10 * K ≤ d) :
    row (a + 7) d = row a d ∧ row a (d + 10) = row a d := by
  have h0 := far_table K a d ha (by omega) hd
  have h7 := far_table K (a + 7) d (by omega) hK hd
  have h10 := far_table K a (d + 10) ha (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [h7, h0]; exact F_congr (by omega) rfl
  · rw [h10, h0]; exact F_congr rfl (by omega)

theorem witness (k : Nat) (hk : k % 7 = 0) :
    row (7 * (k * k) + 35 * k + 13) (23 + 10 * k) = true ∧
    F ((7 * (k * k) + 35 * k + 13) % 7) ((23 + 10 * k) % 10) = false ∧
    F ((7 * (k * k) + 35 * k + 13 + (23 + 10 * k)) % 7) ((10 - (23 + 10 * k) % 10) % 10) = false := by
  refine ⟨?_, ?_, ?_⟩
  · have hg : 0 < gap k := by unfold gap; omega
    have := Mrow_round k 0 (23 + 10 * k) hg
    rw [Nat.add_zero] at this
    rw [show 7 * (k * k) + 35 * k + 13 = tk k from rfl, row_eq, this]
    unfold Mk
    rw [if_pos (by omega)]
    unfold Lrow p1L
    have hwk : wk k = 35 + 10 * (k : Int) := rfl
    have e : ((23 + 10 * k : Nat) : Int) - wk k = -12 := by omega
    rw [e]
    decide
  · have e1 : (7 * (k * k) + 35 * k + 13) % 7 = 6 := by omega
    have e2 : (23 + 10 * k) % 10 = 3 := by omega
    rw [e1, e2]; decide
  · have e1 : (7 * (k * k) + 35 * k + 13 + (23 + 10 * k)) % 7 = 1 := by omega
    have e2 : (10 - (23 + 10 * k) % 10) % 10 = 7 := by omega
    rw [e1, e2]; decide

/-- the alpha medium in a column (paper Lemma "alpha"): in the L phase, left of the seam p1 -/
theorem alpha_col (k r d : Nat) (hr : r ≤ 6 * k) (hd : d ≤ 5 * k + 25) :
    row (7 * (k * k) + 35 * k + 13 + r) d = alpha ((d : Int) - 35 - 10 * (k : Int) - 5 * (r : Int)) := by
  have hrg : r < gap k := by unfold gap; omega
  rw [show 7 * (k * k) + 35 * k + 13 + r = tk k + r from rfl, row_eq, Mrow_round k r d hrg]
  unfold Mk
  rw [if_pos (by omega)]
  unfold Lrow p1L
  have hwk : wk k = 35 + 10 * (k : Int) := rfl
  rw [if_pos (by omega), hwk]
  congr 1
  omega

#print axioms far_table
#print axioms far_periodic
#print axioms witness
#print axioms alpha_col

end SqrtM
