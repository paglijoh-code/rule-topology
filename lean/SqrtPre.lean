/-
Tail onsets of the model rows, in the column e = d - w_k (k-free).  `EPre F c` : the 10-periodic tail of
the row F starts exactly at e = c.  `cc z` is the onset of the generic row of phase z = r mod 7;
`cR s` that of the last rows of an R phase.
-/
import SqrtSound
namespace SqrtM

def EPre (F : Int → Bool) (c : Int) : Prop :=
  (∀ e : Int, c ≤ e → F (e + 10) = F e) ∧ F (c - 1 + 10) ≠ F (c - 1)

/-- onset for the generic row of phase z -/
def cc (z : Nat) : Int := ([0, -20, -15, -10, -5, 0, -5].getD z 0 : Int)
/-- onset of the R-phase row with s rows to go, s <= 8 -/
def cR (s : Nat) : Int := ([0, -5, 10, 5, 0, -5, -10, 0, -5].getD s 0 : Int)

/-- the wall medium of phase z (left of the seam beta, right of it the tail) -/
def Lb (z : Nat) (e : Int) : Bool := if e < pw z then beta (e - 5 * (z : Int)) else tl z e

theorem EPre_congr (F G : Int → Bool) (c : Int) (h : ∀ e : Int, c - 1 ≤ e → F e = G e)
    (hG : EPre G c) : EPre F c := by
  obtain ⟨h1, h2⟩ := hG
  refine ⟨fun e he => ?_, ?_⟩
  · rw [h e (by omega), h (e + 10) (by omega)]; exact h1 e he
  · rw [h (c - 1) (by omega), h (c - 1 + 10) (by omega)]; exact h2

theorem EPre_win (F : Int → Bool) (c : Int) (z : Nat) (hc : -20 ≤ c)
    (htail : ∀ e : Int, 40 ≤ e → F e = tl z e)
    (hw : ∀ x : Nat, x < 60 → F (c + x + 10) = F (c + x))
    (hn : F (c - 1 + 10) ≠ F (c - 1)) : EPre F c := by
  refine ⟨fun e he => ?_, hn⟩
  by_cases h : e < c + 60
  · have := hw (e - c).toNat (by omega)
    have e' : c + (((e - c).toNat : Nat) : Int) = e := by omega
    rwa [e'] at this
  · rw [htail e (by omega), htail (e + 10) (by omega)]
    apply tl_congr; omega

theorem Lrow_tail26 (r : Nat) (e : Int) (he : 26 ≤ e) : Lrow r e = tl (r % 7) e := by
  unfold Lrow p1L
  rw [if_neg (by omega), if_neg (by have := pw_bounds (r % 7) (by omega); omega)]

theorem Rrow_tail40 (s : Nat) (hs : 1 ≤ s) (e : Int) (he : 40 ≤ e) : Rrow s e = tl (zR s) e := by
  have hb := pw_bounds (zR s) (by unfold zR; omega)
  unfold Rrow p1R
  by_cases h1 : s = 1
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h1, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem Lb_win : ∀ z : Nat, z < 7 → ∀ x : Nat, x < 60 →
    Lb z (cc z + x + 10) = Lb z (cc z + x) := by decide +kernel
theorem Lb_wit : ∀ z : Nat, z < 7 → Lb z (cc z - 1 + 10) ≠ Lb z (cc z - 1) := by decide +kernel
theorem cc_ge : ∀ z : Nat, z < 7 → -20 ≤ cc z := by decide +kernel

theorem Lb_pre' (z : Nat) (hz : z < 7) : EPre (Lb z) (cc z) := by
  have hb := pw_bounds z hz
  apply EPre_win _ _ z (cc_ge z hz)
  · intro e he; unfold Lb; rw [if_neg (by omega)]
  · exact Lb_win z hz
  · exact Lb_wit z hz

theorem L_win : ∀ r : Nat, r < 48 → ∀ x : Nat, x < 60 →
    Lrow r (cc (r % 7) + x + 10) = Lrow r (cc (r % 7) + x) := by decide +kernel
theorem L_wit : ∀ r : Nat, r < 48 →
    Lrow r (cc (r % 7) - 1 + 10) ≠ Lrow r (cc (r % 7) - 1) := by decide +kernel

theorem Lrow_pre (r : Nat) : EPre (Lrow r) (cc (r % 7)) := by
  have hz : r % 7 < 7 := by omega
  by_cases h : r < 48
  · apply EPre_win _ _ (r % 7) (cc_ge _ hz)
    · intro e he; exact Lrow_tail26 r e (by omega)
    · exact L_win r h
    · exact L_wit r h
  · apply EPre_congr _ (Lb (r % 7)) _ _ (Lb_pre' _ hz)
    intro e he
    have := cc_ge _ hz
    unfold Lrow Lb p1L
    rw [if_neg (by omega)]
    split
    · apply beta_congr; omega
    · rfl

theorem Rwin9 : ∀ s : Nat, s < 9 → 1 ≤ s → ∀ x : Nat, x < 60 →
    Rrow s (cR s + x + 10) = Rrow s (cR s + x) := by decide +kernel
theorem Rwit9 : ∀ s : Nat, s < 9 → 1 ≤ s →
    Rrow s (cR s - 1 + 10) ≠ Rrow s (cR s - 1) := by decide +kernel
theorem cR_ge : ∀ s : Nat, s < 9 → 1 ≤ s → -20 ≤ cR s := by decide +kernel

theorem Rrow_pre_small (s : Nat) (hs : 1 ≤ s) (h9 : s < 9) : EPre (Rrow s) (cR s) := by
  apply EPre_win _ _ (zR s) (cR_ge s h9 hs)
  · intro e he; exact Rrow_tail40 s hs e he
  · exact Rwin9 s h9 hs
  · exact Rwit9 s h9 hs

theorem Rrow_pre_big (s : Nat) (hs : 9 ≤ s) : EPre (Rrow s) (cc (zR s)) := by
  have hz : zR s < 7 := by unfold zR; omega
  apply EPre_congr _ (Lb (zR s)) _ _ (Lb_pre' _ hz)
  intro e he
  have := cc_ge _ hz
  have hb := pw_bounds (zR s) hz
  unfold Rrow Lb p1R
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  split
  · apply beta_congr; unfold zR; omega
  · rfl

end SqrtM
