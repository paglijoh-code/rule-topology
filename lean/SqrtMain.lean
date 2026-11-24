/-
Main result: the sqrt a wall law for S1 = [1,2,5,6], S2 = [1,2,3,4], stated
about `outcome` of the game of LeadADefs only.

`row a d` is the outcome of the position (a, a + d) (true = P).  `IsPre a p` : the row a has a tail of
period 10 starting exactly at column p (p is the least such column).  The law: with
t_k = 7k^2 + 35k + 13, w_k = 35 + 10k, gap_k = 14(k + 3), for every k and 0 <= r < gap_k the row
a = t_k + r satisfies
* pre(t_k) = w_k (r = 0): the wall jumps exactly at t_k;
* w_k - 20 <= pre(a) <= w_k for r <= gap_k - 4;
* the last three rows before the next jump have pre = w_k + 5, w_k + 10, w_k - 5.
-/
import SqrtPre
namespace SqrtM

/-- outcome (true = P) of the position (a, a + d) of the game [1,2,5,6] / [1,2,3,4] -/
def row (a d : Nat) : Bool := LeadA.outcome [1, 2, 5, 6] [1, 2, 3, 4] a (a + d)

/-- the row a is eventually 10-periodic from column p on, and p is least with this property -/
def IsPre (a p : Nat) : Prop :=
  (∀ d, p ≤ d → row a (d + 10) = row a d) ∧
  ∀ q, q < p → ∃ d, q ≤ d ∧ row a (d + 10) ≠ row a d

theorem row_eq (a d : Nat) : row a d = Mrow a d := by
  unfold row
  rw [outcome_eq]
  unfold model
  rw [if_pos (by omega), show a + d - a = d by omega]

theorem Mk_L (k r : Nat) (h : r < 12 * k + 32) (e : Int) : Mk k r (e + wk k) = Lrow r e := by
  unfold Mk; rw [if_pos h]; congr 1; omega

theorem Mk_R (k r : Nat) (h : ¬ r < 12 * k + 32) (e : Int) :
    Mk k r (e + wk k) = Rrow (gap k - r) e := by
  unfold Mk; rw [if_neg h]; congr 1; omega

theorem isPre_of_EPre (k r : Nat) (hr : r < gap k) (c : Int) (hc : -20 ≤ c) (p : Nat)
    (hp : (p : Int) = 35 + 10 * (k : Int) + c) (h : EPre (fun e => Mk k r (e + wk k)) c) :
    IsPre (tk k + r) p := by
  have hw : wk k = 35 + 10 * (k : Int) := rfl
  have hrow : ∀ d : Nat, row (tk k + r) d = (fun e => Mk k r (e + wk k)) ((d : Int) - wk k) := by
    intro d
    rw [row_eq, Mrow_round k r d hr]
    dsimp only
    congr 1; omega
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun d hd => ?_, fun q hq => ?_⟩
  · rw [hrow, hrow]
    have := h1 ((d : Int) - wk k) (by omega)
    rw [← this]
    congr 1; push_cast; omega
  · refine ⟨p - 1, by omega, ?_⟩
    rw [hrow, hrow]
    intro heq
    apply h2
    have e1 : ((p - 1 + 10 : Nat) : Int) - wk k = c - 1 + 10 := by omega
    have e2 : ((p - 1 : Nat) : Int) - wk k = c - 1 := by omega
    rw [e1, e2] at heq
    exact heq

theorem sqrt_wall (k r a : Nat) (hr : r < 14 * (k + 3)) (ha : a = 7 * (k * k) + 35 * k + 13 + r) :
    (r = 0 → IsPre a (35 + 10 * k)) ∧
    (r + 4 ≤ 14 * (k + 3) → ∃ p, IsPre a p ∧ 35 + 10 * k ≤ p + 20 ∧ p ≤ 35 + 10 * k) ∧
    (r + 3 = 14 * (k + 3) → IsPre a (35 + 10 * k + 5)) ∧
    (r + 2 = 14 * (k + 3) → IsPre a (35 + 10 * k + 10)) ∧
    (r + 1 = 14 * (k + 3) → IsPre a (35 + 10 * k - 5)) := by
  have hg : gap k = 14 * (k + 3) := rfl
  have hr' : r < gap k := by omega
  have ha' : a = tk k + r := by rw [ha]; rfl
  subst ha'
  by_cases hL : r < 12 * k + 32
  · have hF : EPre (fun e => Mk k r (e + wk k)) (cc (r % 7)) := by
      apply EPre_congr _ (Lrow r) _ _ (Lrow_pre r)
      intro e _; exact Mk_L k r hL e
    have hc := cc_ge (r % 7) (by omega)
    have hc2 : cc (r % 7) ≤ 0 := by
      have : ∀ z : Nat, z < 7 → cc z ≤ 0 := by decide +kernel
      exact this _ (by omega)
    have hz : r = 0 → cc (r % 7) = 0 := by intro h; subst h; rfl
    refine ⟨fun h0 => ?_, fun _ => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exact isPre_of_EPre k r hr' _ hc (35 + 10 * k) (by rw [hz h0]; simp) hF
    · refine ⟨(35 + 10 * (k : Int) + cc (r % 7)).toNat, isPre_of_EPre k r hr' _ hc _ (by omega) hF, ?_, ?_⟩ <;> omega
    all_goals omega
  · have hF : ∀ c, EPre (Rrow (gap k - r)) c → EPre (fun e => Mk k r (e + wk k)) c := by
      intro c h
      apply EPre_congr _ (Rrow (gap k - r)) _ _ h
      intro e _; exact Mk_R k r hL e
    have hs9 : 9 ≤ gap k - r ∨ gap k - r < 9 := by omega
    refine ⟨fun h0 => by omega, fun h4 => ?_, fun h3 => ?_, fun h2 => ?_, fun h1 => ?_⟩
    · rcases hs9 with h9 | h9
      · have hz : zR (gap k - r) < 7 := by unfold zR; omega
        have hc := cc_ge _ hz
        have hc2 : ∀ z : Nat, z < 7 → cc z ≤ 0 := by decide +kernel
        have := hc2 _ hz
        exact ⟨(35 + 10 * (k : Int) + cc (zR (gap k - r))).toNat,
          isPre_of_EPre k r hr' _ hc _ (by omega) (hF _ (Rrow_pre_big _ h9)), by omega, by omega⟩
      · have hcR := cR_ge (gap k - r) h9 (by omega)
        have hc2 : ∀ s : Nat, s < 9 → 4 ≤ s → cR s ≤ 0 := by decide +kernel
        have := hc2 _ h9 (by omega)
        exact ⟨(35 + 10 * (k : Int) + cR (gap k - r)).toNat,
          isPre_of_EPre k r hr' _ hcR _ (by omega) (hF _ (Rrow_pre_small _ (by omega) h9)),
          by omega, by omega⟩
    · have hs : gap k - r = 3 := by omega
      have := Rrow_pre_small 3 (by omega) (by omega)
      rw [← hs] at this
      exact isPre_of_EPre k r hr' _ (by rw [hs]; decide) _ (by rw [hs]; simp [cR] <;> omega) (hF _ this)
    · have hs : gap k - r = 2 := by omega
      have := Rrow_pre_small 2 (by omega) (by omega)
      rw [← hs] at this
      exact isPre_of_EPre k r hr' _ (by rw [hs]; decide) _ (by rw [hs]; simp [cR] <;> omega) (hF _ this)
    · have hs : gap k - r = 1 := by omega
      have := Rrow_pre_small 1 (by omega) (by omega)
      rw [← hs] at this
      exact isPre_of_EPre k r hr' _ (by rw [hs]; decide) _ (by rw [hs]; simp [cR] <;> omega) (hF _ this)

#print axioms sqrt_wall
#print axioms outcome_eq

end SqrtM
