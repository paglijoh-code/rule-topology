/-
Item (B): the R-phase virtual table `Rrow s e` (s = rows to go until the next jump, s >= 1, all
columns e in Z) satisfies the game equation `EqR`, for every s >= 1 and every e.
Pieces: left of the glider region `Rrow = fRA` (EqRA_all); right of e = 40 and, for s >= 7, on the
wall region `Rrow` is the wall/tail table read backwards (EqR_mirror); the corner s <= 6,
e in [-16, 45] is a finite window.
-/
import SqrtVirt
namespace SqrtM

theorem Rrow_fRA (s : Nat) (e : Int) (h : (2 ≤ s ∧ e ≤ 0) ∨ (s = 1 ∧ e < -10)) :
    Rrow s e = fRA s e := by
  have hb := pw_bounds (zR s) (by unfold zR; omega)
  unfold Rrow fRA RA p1R
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : s ≠ 1 := by omega
    simp only [this, if_false]
    repeat' split
    all_goals first | omega | (congr 1; omega) | (congr 1 <;> omega) | rfl
  · subst h1
    simp only [if_true]
    repeat' split
    all_goals first | omega | (congr 1; omega) | rfl

theorem Rrow_wall (s : Nat) (e : Int) (hs : 7 ≤ s) (he : -11 ≤ e) :
    Rrow s e = Wall (zR s) e := by
  have hb := pw_bounds (zR s) (by unfold zR; omega)
  unfold Rrow Wall p1R
  have : s ≠ 1 := by omega
  simp only [this, if_false]
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases h : e < pw (zR s)
  · rw [if_pos h, if_pos h]
    apply beta_congr; unfold zR; omega
  · rw [if_neg h, if_neg h]

theorem Rrow_tail (s N : Nat) (e : Int) (hs : 1 ≤ s) (hN : N % 7 = 0) (hsN : s ≤ N)
    (he : 40 ≤ e ∨ (2 ≤ s ∧ 26 ≤ e)) : Rrow s e = ft (N - s) e := by
  have hb := pw_bounds (zR s) (by unfold zR; omega)
  unfold Rrow ft p1R
  have hz : (N - s) % 7 = zR s := by unfold zR; omega
  rw [hz]
  by_cases h1 : s = 1
  · subst h1
    simp only [if_true]
    rw [if_neg (by omega), if_neg (by omega)]
  · simp only [h1, if_false]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem EqR_fRA (s : Nat) (e : Int) : EqR fRA s e = EqRA (e - p1R s) := by
  unfold EqR EqRA Eq9 fRA
  have v1 : RA (e + 1 - p1R (s + 1)) = RA (e - p1R s + 6) := by congr 1; unfold p1R; omega
  have v2 : RA (e + 2 - p1R (s + 2)) = RA (e - p1R s + 12) := by congr 1; unfold p1R; omega
  have v5 : RA (e + 5 - p1R (s + 5)) = RA (e - p1R s + 30) := by congr 1; unfold p1R; omega
  have v6 : RA (e + 6 - p1R (s + 6)) = RA (e - p1R s + 36) := by congr 1; unfold p1R; omega
  have w1 : RA (e - 1 - p1R s) = RA (e - p1R s - 1) := by congr 1; omega
  have w2 : RA (e - 2 - p1R s) = RA (e - p1R s - 2) := by congr 1; omega
  have w5 : RA (e - 5 - p1R s) = RA (e - p1R s - 5) := by congr 1; omega
  have w6 : RA (e - 6 - p1R s) = RA (e - p1R s - 6) := by congr 1; omega
  have m : (e - p1R s + 1) % 5 = e % 5 := by unfold p1R; omega
  rw [v1, v2, v5, v6, w1, w2, w5, w6, m]

theorem R_win : ∀ s : Nat, s < 6 → ∀ i : Nat, i < 62 →
    EqR Rrow (s + 1) ((i : Int) - 16) = true := by
  decide +kernel

theorem R_ok (s : Nat) (hs : 1 ≤ s) (e : Int) : EqR Rrow s e = true := by
  have hsn : ∀ t : Nat, t ∈ [0, 1, 2, 5, 6] → t ≤ 6 := by
    intro t ht; simp at ht; omega
  by_cases h1 : 46 ≤ e
  · rw [EqR_mirror Rrow ft s (7 * (s + 7)) e (by omega)
      (fun t ht => by
        have := hsn t ht
        rw [Rrow_tail (s + t) (7 * (s + 7)) (e + t) (by omega) (by omega) (by omega) (Or.inl (by omega)),
          Nat.sub_sub])
      (fun t ht => by
        have := hsn t ht
        rw [Rrow_tail s (7 * (s + 7)) (e - t) (by omega) (by omega) (by omega) (Or.inl (by omega))])]
    exact ft_ok _ (by omega) e
  by_cases h4 : e ≤ -6 ∧ 2 ≤ s ∨ e ≤ -17
  · rw [EqR_congr Rrow fRA s e
      (fun t ht => by
        have := hsn t ht
        apply Rrow_fRA
        rcases h4 with ⟨h4, h4'⟩ | h4
        · left; omega
        · by_cases hs1 : s + t = 1
          · right; omega
          · left; omega)
      (fun t ht => by
        have := hsn t ht
        apply Rrow_fRA
        rcases h4 with ⟨h4, h4'⟩ | h4
        · left; omega
        · by_cases hs1 : s = 1
          · right; omega
          · left; omega)]
    rw [EqR_fRA]
    exact EqRA_all _
  by_cases h7 : 7 ≤ s
  · by_cases h2 : 32 ≤ e
    · rw [EqR_mirror Rrow ft s (7 * (s + 7)) e (by omega)
        (fun t ht => by
          have := hsn t ht
          rw [Rrow_tail (s + t) (7 * (s + 7)) (e + t) (by omega) (by omega) (by omega)
            (Or.inr ⟨by omega, by omega⟩), Nat.sub_sub])
        (fun t ht => by
          have := hsn t ht
          rw [Rrow_tail s (7 * (s + 7)) (e - t) (by omega) (by omega) (by omega)
            (Or.inr ⟨by omega, by omega⟩)])]
      exact ft_ok _ (by omega) e
    by_cases h3 : -5 ≤ e
    · rw [EqR_mirror Rrow wf s (7 * (s + 7)) e (by omega)
        (fun t ht => by
          have := hsn t ht
          rw [Rrow_wall _ _ (by omega) (by omega)]
          unfold wf
          congr 1; unfold zR; omega)
        (fun t ht => by
          have := hsn t ht
          rw [Rrow_wall _ _ (by omega) (by omega)]
          unfold wf
          congr 1; unfold zR; omega)]
      exact wf_ok _ (by omega) e h3 (by omega)
    · exfalso; omega
  · have h8 : s < 7 := by omega
    have := R_win (s - 1) (by omega) (e + 16).toNat (by omega)
    have e' : (((e + 16).toNat : Nat) : Int) - 16 = e := by omega
    rwa [e', show s - 1 + 1 = s by omega] at this

end SqrtM
