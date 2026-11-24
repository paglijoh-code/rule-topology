/-
The k-free window table of the left edge.  For round k >= 3, row r = 12 k + j, column d <= 44:
`WT j d` (j = rows after the reflection time 12 k).  `MWT` states that `Mrow` equals it; the
equation of `WT` on the window j in [6, 42] is a finite check.
-/
import SqrtRound
namespace SqrtM

def WT (j d : Nat) : Bool :=
  if j ≤ 31 then
    (if (d : Int) - 35 < p1L j then alpha ((d : Int) - 5 * (j : Int)) else beta ((d : Int) - 5 * (j : Int)))
  else
    (if (d : Int) < 41 - 5 * (42 - (j : Int)) then alpha ((d : Int) - 45 + 5 * (42 - (j : Int)))
     else if (d : Int) < 55 - 5 * (42 - (j : Int)) then
       gword (((d : Int) - 41 + 5 * (42 - (j : Int))).toNat)
     else beta ((d : Int) - 35 + 5 * (42 - (j : Int))))

theorem MWT (k j d : Nat) (hk : 3 ≤ k) (hj : j ≤ 42) (hd : d ≤ 44) :
    Mrow (tk k + (12 * k + j)) d = WT j d := by
  have hg : 12 * k + j < gap k := by unfold gap; omega
  by_cases hj31 : j ≤ 31
  · rw [cellL k (12 * k + j) _ d rfl (by omega)]
    have hb := pw_bounds ((12 * k + j) % 7) (by omega)
    have hp : p1L (12 * k + j) = p1L j - 10 * (k : Int) := by unfold p1L; omega
    unfold Lrow WT
    rw [if_pos hj31, hp]
    unfold wk
    by_cases hc : (d : Int) - 35 < p1L j
    · rw [if_pos (by omega), if_pos hc]; apply alpha_congr; omega
    · rw [if_neg (by omega), if_neg hc, if_pos (by omega)]; apply beta_congr; omega
  · rw [cellR k (12 * k + j) _ d rfl (by omega) hg]
    have hb := pw_bounds (zR (gap k - (12 * k + j))) (by unfold zR; omega)
    have hgap : gap k - (12 * k + j) = 2 * k + 42 - j := by unfold gap; omega
    rw [hgap] at hb ⊢
    unfold Rrow WT p1R wk
    rw [if_neg (by omega), if_neg hj31]
    by_cases h1 : (d : Int) < 41 - 5 * (42 - (j : Int))
    · rw [if_pos h1, if_pos (by omega)]; unfold gamma; apply alpha_congr; omega
    · rw [if_neg h1, if_neg (by omega)]
      by_cases h2 : (d : Int) < 55 - 5 * (42 - (j : Int))
      · rw [if_pos h2, if_pos (by omega)]; congr 1; omega
      · rw [if_neg h2, if_neg (by omega), if_pos (by omega)]; apply beta_congr; omega

theorem WT_win : ∀ i : Nat, i < 37 → ∀ d : Nat, d < 38 →
    (WT (i + 6) d == RhsN WT (i + 6) d) = true := by
  decide +kernel

/-! ### The pure lattice zones -/

def Lam (c : Int) (a d : Nat) : Bool := alpha ((d : Int) - 5 * (a : Int) - c)

theorem Lat_base : ∀ n : Nat, n < 35 → n % 5 = 0 → ∀ d : Nat, d < 6 →
    (Lam (n : Int) 6 d == RhsN (Lam (n : Int)) 6 d) = true := by
  decide +kernel

theorem Lat (c : Int) (hc : c % 5 = 0) (a d : Nat) (ha : 6 ≤ a) (hd : d < 6) :
    (Lam c a d == RhsN (Lam c) a d) = true := by
  have hb := Lat_base ((c + 5 * (a : Int) - 30) % 35).toNat (by omega) (by omega) d hd
  have e1 : Lam c a d = Lam (((c + 5 * (a : Int) - 30) % 35).toNat : Int) 6 d := by
    unfold Lam; apply alpha_congr; omega
  have e2 : RhsN (Lam c) a d = RhsN (Lam (((c + 5 * (a : Int) - 30) % 35).toNat : Int)) 6 d := by
    apply RhsN_congr _ _ a 6 d (by omega) ha
    intro i hi y _
    unfold Lam; apply alpha_congr; omega
  rw [e1, e2]; exact hb

theorem Rrow_gamma (s : Nat) (e : Int) (hs : 1 ≤ s) (h1 : e < 6 - 5 * (s : Int)) (h2 : e < -10) :
    Rrow s e = gamma (e + 5 * (s : Int)) := by
  unfold Rrow p1R
  by_cases h : s = 1
  · subst h; rw [if_pos rfl, if_pos h2]; congr 1
  · rw [if_neg h, if_pos h1]

theorem ZL (k r' d' : Nat) (hk : 3 ≤ k) (hr : r' ≤ 12 * k + 5) (hd : d' ≤ 11) :
    Mrow (tk k + r') d' = Lam (10 * (k : Int) + 5) (tk k + r') d' := by
  rw [cellL k r' _ d' rfl (by omega)]
  unfold Lrow p1L Lam wk
  rw [if_pos (by omega)]
  apply alpha_congr
  unfold tk
  push_cast
  omega

theorem ZP (k s d' : Nat) (hk : 3 ≤ k) (hs1 : 1 ≤ s) (hs6 : s ≤ 6) (hd : d' ≤ 11) :
    Mrow (tk k - s) d' = Lam (10 * (k : Int) + 5) (tk k - s) d' := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h13 := tk_13 (m + 1)
  rw [cellPrev m s (tk (m + 1) - s) d' (by omega) hs1 hs6]
  rw [Rrow_gamma s _ hs1 (by unfold wk; push_cast; omega) (by unfold wk; push_cast; omega)]
  unfold gamma Lam wk
  apply alpha_congr
  have := tk_13 (m + 1)
  unfold tk at *
  push_cast
  omega

theorem ZR (k r' d' : Nat) (hk : 3 ≤ k) (hr : 12 * k + 37 ≤ r') (hr2 : r' < gap k) (hd : d' ≤ 11) :
    Mrow (tk k + r') d' = Lam (10 * (k : Int) + 15) (tk k + r') d' := by
  rw [cellR k r' _ d' rfl (by omega) hr2]
  have hgap : gap k - r' ≥ 1 := by omega
  rw [Rrow_gamma (gap k - r') _ hgap (by unfold wk gap; push_cast; omega)
    (by unfold wk; push_cast; omega)]
  unfold gamma Lam wk
  apply alpha_congr
  unfold tk gap at *
  push_cast
  omega

end SqrtM
