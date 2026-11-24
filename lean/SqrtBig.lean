/-
The model satisfies the game equation in every round k >= 3 (rows a >= t_3 = 181).
Cases (j = r - 12 k, d = column):
 d >= 6: r < 6 jump rows (J_ok); r <= 12k+31 L phase (A_ok); j in [32,37] transition
         (window for d < 38, R table for d >= 38); j >= 38 R phase (R_ok).
 d < 6 (reflection at the diagonal): j <= 5 lattice zone; j in [6,42] window; j >= 43 lattice zone.
-/
import SqrtWin
namespace SqrtM

theorem wk_mod5 (k : Nat) : wk k % 5 = 0 := by unfold wk; omega

/-- on a window row (j in [6,42]) with d < 38 -/
theorem big_window (k r d : Nat) (hk : 3 ≤ k) (hr : r < gap k) (hj1 : 12 * k + 6 ≤ r)
    (hj2 : r ≤ 12 * k + 42) (hd : d < 38) :
    (Mrow (tk k + r) d == RhsN Mrow (tk k + r) d) = true := by
  have h13 := tk_13 k
  have hg : gap k = 14 * (k + 3) := rfl
  obtain ⟨j, rfl⟩ : ∃ j, r = 12 * k + j := ⟨r - 12 * k, by omega⟩
  have e0 := MWT k j d hk (by omega) (by omega)
  rw [RhsN_congr Mrow WT (tk k + (12 * k + j)) j d (by omega) (by omega)
    (fun i hi y hy => by
      rw [show tk k + (12 * k + j) - i = tk k + (12 * k + (j - i)) by omega]
      exact MWT k (j - i) y hk (by omega) (by omega)), e0]
  exact WT_win (j - 6) (by omega) d hd |> fun h => by rwa [show j - 6 + 6 = j by omega] at h

theorem big_zoneL (k r d : Nat) (hk : 3 ≤ k) (hr : r ≤ 12 * k + 5) (hd : d < 6) (hr6 : 6 ≤ r) :
    (Mrow (tk k + r) d == RhsN Mrow (tk k + r) d) = true := by
  have h13 := tk_13 k
  have hg : gap k = 14 * (k + 3) := rfl
  have e0 := ZL k r d hk hr (by omega)
  rw [RhsN_congr Mrow (Lam (10 * (k : Int) + 5)) (tk k + r) (tk k + r) d (by omega) (Nat.le_refl _)
    (fun i hi y hy => by
      by_cases hir : i ≤ r
      · rw [show tk k + r - i = tk k + (r - i) by omega]
        exact ZL k (r - i) y hk (by omega) (by omega)
      · rw [show tk k + r - i = tk k - (i - r) by omega]
        exact ZP k (i - r) y hk (by omega) (by omega) (by omega)), e0]
  exact Lat _ (by omega) _ _ (by omega) hd

theorem big_zoneL0 (k r d : Nat) (hk : 3 ≤ k) (hr : r < 6) (hd : d < 6) :
    (Mrow (tk k + r) d == RhsN Mrow (tk k + r) d) = true := by
  have h13 := tk_13 k
  have hg : gap k = 14 * (k + 3) := rfl
  have e0 := ZL k r d hk (by omega) (by omega)
  rw [RhsN_congr Mrow (Lam (10 * (k : Int) + 5)) (tk k + r) (tk k + r) d (by omega) (Nat.le_refl _)
    (fun i hi y hy => by
      by_cases hir : i ≤ r
      · rw [show tk k + r - i = tk k + (r - i) by omega]
        exact ZL k (r - i) y hk (by omega) (by omega)
      · rw [show tk k + r - i = tk k - (i - r) by omega]
        exact ZP k (i - r) y hk (by omega) (by omega) (by omega)), e0]
  exact Lat _ (by omega) _ _ (by omega) hd

theorem big_zoneR (k r d : Nat) (hk : 3 ≤ k) (hr : 12 * k + 43 ≤ r) (hr2 : r < gap k) (hd : d < 6) :
    (Mrow (tk k + r) d == RhsN Mrow (tk k + r) d) = true := by
  have h13 := tk_13 k
  have hg : gap k = 14 * (k + 3) := rfl
  have e0 := ZR k r d hk (by omega) hr2 (by omega)
  rw [RhsN_congr Mrow (Lam (10 * (k : Int) + 15)) (tk k + r) (tk k + r) d (by omega) (Nat.le_refl _)
    (fun i hi y hy => by
      rw [show tk k + r - i = tk k + (r - i) by omega]
      exact ZR k (r - i) y hk (by omega) (by omega) (by omega)), e0]
  exact Lat _ (by omega) _ _ (by omega) hd

theorem big_jump (k r d : Nat) (hk : 3 ≤ k) (hr : r < 6) (hd : 6 ≤ d) :
    (Mrow (tk k + r) d == RhsN Mrow (tk k + r) d) = true := by
  have h13 := tk_13 k
  have hg : gap k = 14 * (k + 3) := rfl
  rw [tf_F Jt Mrow (tk k + r) (r + 6) d (wk k) (wk_mod5 k) (by omega) (by omega) hd
    (fun i hi y _ _ => by
      by_cases hir : i ≤ r
      · rw [cellL k (r - i) (tk k + r - i) y (by omega) (by omega)]
        unfold Jt
        rw [if_pos (by omega), show r + 6 - i - 6 = r - i by omega]
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        rw [cellPrev m (i - r) (tk (m + 1) + r - i) y (by omega) (by omega) (by omega)]
        unfold Jt
        rw [if_neg (by omega), show 6 - (r + 6 - i) = i - r by omega])]
  exact J_ok (r + 6) (by omega) (by omega) _

theorem big_L (k r d : Nat) (hk : 3 ≤ k) (hr : 6 ≤ r) (hr2 : r ≤ 12 * k + 31) (hd : 6 ≤ d) :
    (Mrow (tk k + r) d == RhsN Mrow (tk k + r) d) = true := by
  have h13 := tk_13 k
  have hg : gap k = 14 * (k + 3) := rfl
  rw [tf_F Lrow Mrow (tk k + r) r d (wk k) (wk_mod5 k) (by omega) hr hd
    (fun i hi y _ _ => by
      rw [cellL k (r - i) (tk k + r - i) y (by omega) (by omega)])]
  exact A_ok r hr _

theorem LR_eq (k r' y : Nat) (hk : 3 ≤ k) (h1 : 12 * k + 26 ≤ r') (h2 : r' ≤ 12 * k + 31)
    (hy : 32 ≤ y) :
    Lrow r' ((y : Int) - wk k) = Rrow (gap k - r') ((y : Int) - wk k) := by
  have hb := pw_bounds (r' % 7) (by omega)
  have hgap : gap k - r' = 14 * (k + 3) - r' := by unfold gap; omega
  rw [hgap]
  have hb2 := pw_bounds (zR (14 * (k + 3) - r')) (by unfold zR; omega)
  have hz : zR (14 * (k + 3) - r') = r' % 7 := by unfold zR; omega
  unfold Lrow Rrow p1L p1R wk
  have c1 : ¬ (((y : Int) - (35 + 10 * (k : Int))) < -9 + 5 * ((r' % 6 : Nat) : Int) - 5 * ((r' / 6 : Nat) : Int)) := by omega
  have c2 : ¬ (14 * (k + 3) - r' = 1) := by omega
  have c3 : ¬ (((y : Int) - (35 + 10 * (k : Int))) < 6 - 5 * ((14 * (k + 3) - r' : Nat) : Int)) := by omega
  have c4 : ¬ (((y : Int) - (35 + 10 * (k : Int))) < 6 - 5 * ((14 * (k + 3) - r' : Nat) : Int) + 14) := by omega
  rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, hz]
  by_cases h : ((y : Int) - (35 + 10 * (k : Int))) < pw (r' % 7)
  · rw [if_pos h, if_pos h]; apply beta_congr; omega
  · rw [if_neg h, if_neg h]

theorem big_trans (k r d : Nat) (hk : 3 ≤ k) (hr : 12 * k + 32 ≤ r) (hr2 : r ≤ 12 * k + 37)
    (hd : 38 ≤ d) :
    (Mrow (tk k + r) d == RhsN Mrow (tk k + r) d) = true := by
  have h13 := tk_13 k
  have hg : gap k = 14 * (k + 3) := rfl
  rw [tf_R Rrow Mrow (tk k + r) (gap k - r) d (wk k) (wk_mod5 k) (by omega) (by omega)
    (fun i hi y hy1 _ => by
      by_cases hc : 12 * k + 32 ≤ r - i
      · rw [cellR k (r - i) (tk k + r - i) y (by omega) hc (by unfold gap; omega)]
        congr 1; unfold gap; omega
      · rw [cellL k (r - i) (tk k + r - i) y (by omega) (by omega)]
        rw [LR_eq k (r - i) y hk (by omega) (by omega) (by omega)]
        congr 1; unfold gap; omega)]
  exact R_ok _ (by unfold gap; omega) _

theorem big_R (k r d : Nat) (hk : 3 ≤ k) (hr : 12 * k + 38 ≤ r) (hr2 : r < gap k) (hd : 6 ≤ d) :
    (Mrow (tk k + r) d == RhsN Mrow (tk k + r) d) = true := by
  have h13 := tk_13 k
  have hg : gap k = 14 * (k + 3) := rfl
  rw [tf_R Rrow Mrow (tk k + r) (gap k - r) d (wk k) (wk_mod5 k) (by omega) hd
    (fun i hi y _ _ => by
      rw [cellR k (r - i) (tk k + r - i) y (by omega) (by omega) (by unfold gap; omega)]
      congr 1; unfold gap; omega)]
  exact R_ok _ (by unfold gap; omega) _

theorem big (k r d : Nat) (hk : 3 ≤ k) (hr : r < gap k) :
    (Mrow (tk k + r) d == RhsN Mrow (tk k + r) d) = true := by
  by_cases hd : 6 ≤ d
  · by_cases h1 : r < 6
    · exact big_jump k r d hk h1 hd
    by_cases h2 : r ≤ 12 * k + 31
    · exact big_L k r d hk (by omega) h2 hd
    by_cases h3 : r ≤ 12 * k + 37
    · by_cases h4 : d < 38
      · exact big_window k r d hk hr (by omega) (by omega) h4
      · exact big_trans k r d hk (by omega) h3 (by omega)
    · exact big_R k r d hk (by omega) hr hd
  · by_cases h1 : r < 6
    · exact big_zoneL0 k r d hk h1 (by omega)
    by_cases h2 : r ≤ 12 * k + 5
    · exact big_zoneL k r d hk h2 (by omega) (by omega)
    by_cases h3 : r ≤ 12 * k + 42
    · exact big_window k r d hk hr (by omega) h3 (by omega)
    · exact big_zoneR k r d hk (by omega) hr (by omega)

end SqrtM
