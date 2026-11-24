/-
Rows a < t_3 = 181 (the early rows and rounds 0, 1, 2): the equation is checked directly on
d < 111 by kernel evaluation; beyond d = 95 every such row is 10-periodic, which transports the
equation from d - 10 to d.
-/
import SqrtBig
namespace SqrtM

def chk (a d : Nat) : Bool := Mrow a d == RhsN Mrow a d
def chkRows (a0 n D : Nat) : Bool :=
  (List.range n).all fun i => (List.range D).all fun d => chk (a0 + i) d

theorem chkRows_spec (a0 n D : Nat) (h : chkRows a0 n D = true) :
    ∀ a, a0 ≤ a → a < a0 + n → ∀ d, d < D → chk a d = true := by
  intro a h1 h2 d hd
  unfold chkRows at h
  rw [List.all_eq_true] at h
  have := h (a - a0) (List.mem_range.2 (by omega))
  rw [List.all_eq_true] at this
  have := this d (List.mem_range.2 hd)
  rwa [show a0 + (a - a0) = a by omega] at this

theorem small1 : chkRows 0 40 111 = true := by decide +kernel
theorem small2 : chkRows 40 40 111 = true := by decide +kernel
theorem small3 : chkRows 80 50 111 = true := by decide +kernel
theorem small4 : chkRows 130 51 111 = true := by decide +kernel

theorem Rrow_tail' (s : Nat) (e : Int) (hs : 1 ≤ s) (he : 40 ≤ e) : Rrow s e = tl (zR s) e := by
  rw [Rrow_tail s (7 * (s + 7)) e hs (by omega) (by omega) (Or.inl he)]
  unfold ft; congr 1; unfold zR; omega

theorem Lrow_tail' (r : Nat) (e : Int) (he : 26 ≤ e) : Lrow r e = tl (r % 7) e := by
  rw [Lrow_tail r e he]; rfl

theorem Mrow_per (a : Nat) (ha : a < 181) (y : Nat) (hy : 95 ≤ y) : Mrow a (y + 10) = Mrow a y := by
  by_cases h13 : a < 13
  · unfold Mrow
    rw [if_pos h13, if_pos h13]
    unfold early
    rw [if_neg (by omega)]
    by_cases hy' : y < 45
    · omega
    · rw [if_neg hy']; congr 1; omega
  · have h13' : 13 ≤ a := by omega
    have hs := tk_succ 0
    have hs1 := tk_succ 1
    have hs2 := tk_succ 2
    have e0 : tk 0 = 13 := rfl
    have e1 : tk 1 = 55 := rfl
    have e2 : tk 2 = 111 := rfl
    have e3 : tk 3 = 181 := rfl
    have g0 : gap 0 = 42 := rfl
    have g1 : gap 1 = 56 := rfl
    have g2 : gap 2 = 70 := rfl
    obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k ≤ 2 ∧ r < gap k ∧ a = tk k + r := by
      by_cases c1 : a < 55
      · exact ⟨0, a - 13, by omega, by omega, by omega⟩
      by_cases c2 : a < 111
      · exact ⟨1, a - 55, by omega, by omega, by omega⟩
      · exact ⟨2, a - 111, by omega, by omega, by omega⟩
    rw [Mrow_round k r _ hr, Mrow_round k r _ hr]
    unfold Mk
    have hk3 : wk k = 35 + 10 * (k : Int) := rfl
    have hgk : gap k = 14 * (k + 3) := rfl
    by_cases hL : r < 12 * k + 32
    · rw [if_pos hL, if_pos hL, Lrow_tail' _ _ (by omega), Lrow_tail' _ _ (by omega)]
      apply tl_congr; omega
    · rw [if_neg hL, if_neg hL, Rrow_tail' _ _ (by unfold gap; omega) (by omega),
        Rrow_tail' _ _ (by unfold gap; omega) (by omega)]
      apply tl_congr; omega

theorem RhsN_per (M : Nat → Nat → Bool) (a d : Nat) (hd : 16 ≤ d)
    (h : ∀ x y, x ≤ a → d ≤ y + 6 → y ≤ d + 6 → M x y = M x (y - 10)) :
    RhsN M a d = RhsN M a (d - 10) := by
  have u : ∀ s, s ≤ 6 → Ucell M a d s = Ucell M a (d - 10) s := by
    intro s hs
    unfold Ucell
    rw [h (a - s) (d + s) (by omega) (by omega) (by omega), show d + s - 10 = d - 10 + s by omega]
  have w : ∀ s, s ≤ 6 → Wcell M a d s = Wcell M a (d - 10) s := by
    intro s hs
    unfold Wcell
    rw [if_pos (by omega), if_pos (by omega), h a (d - s) (by omega) (by omega) (by omega),
      show d - s - 10 = d - 10 - s by omega]
    simp [show s ≤ a + d by omega, show s ≤ a + (d - 10) by omega]
  unfold RhsN
  rw [u 1 (by omega), u 2 (by omega), u 5 (by omega), u 6 (by omega),
    w 1 (by omega), w 2 (by omega), w 5 (by omega), w 6 (by omega),
    show (d - 10) % 5 = d % 5 by omega]

theorem small (a : Nat) (ha : a < 181) : ∀ d, chk a d = true := by
  have base : ∀ d, d < 111 → chk a d = true := by
    intro d hd
    by_cases h1 : a < 40
    · exact chkRows_spec 0 40 111 small1 a (by omega) (by omega) d hd
    by_cases h2 : a < 80
    · exact chkRows_spec 40 40 111 small2 a (by omega) (by omega) d hd
    by_cases h3 : a < 130
    · exact chkRows_spec 80 50 111 small3 a (by omega) (by omega) d hd
    · exact chkRows_spec 130 51 111 small4 a (by omega) (by omega) d hd
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    by_cases hd : d < 111
    · exact base d hd
    · have ih' := ih (d - 10) (by omega)
      unfold chk at ih' ⊢
      have e := RhsN_per Mrow a d (by omega) (fun x y hx h1 h2 => by
        have hx' : x < 181 := by omega
        rw [← Mrow_per x hx' (y - 10) (by omega), show y - 10 + 10 = y by omega])
      rw [e]
      have m : Mrow a d = Mrow a (d - 10) := by
        rw [← Mrow_per a ha (d - 10) (by omega), show d - 10 + 10 = d by omega]
      rw [m]; exact ih'

end SqrtM
