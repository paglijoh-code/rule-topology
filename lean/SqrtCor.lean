/-
M3 corollaries of the sqrt a wall law (`SqrtM.sqrt_wall`):
(1) all-rows form for a >= 13, and uniqueness of the pre-period start;
(2) the wall is not within bounded distance of any line of slope n/m >= 0;
(3) two-sided square-root bounds: 100 a <= 7 p^2 + 280 p and 7 p^2 <= 100 a + 280 p + 275;
(4) transport to S2 = [1,2,3,4,6]: sgFn is x % 5 there too, so the game is the same.
Statements use only `LeadA.outcome`, `SqrtM.row`, `SqrtM.IsPre` and literals.
-/
import SqrtMain
namespace SqrtM
open LeadA

theorem pre_unique {a p p' : Nat} (h : IsPre a p) (h' : IsPre a p') : p = p' := by
  refine Classical.byContradiction fun hne => ?_
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · obtain ⟨d, hd, hd2⟩ := h'.2 p hl
    exact hd2 (h.1 d hd)
  · obtain ⟨d, hd, hd2⟩ := h.2 p' hl
    exact hd2 (h'.1 d hd)

theorem tk_succ' (k : Nat) : 7 * ((k + 1) * (k + 1)) + 35 * (k + 1) + 13 =
    7 * (k * k) + 35 * k + 13 + 14 * (k + 3) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

theorem sqrt_wall_all : ∀ a, 13 ≤ a → ∃ k p, 7*(k*k)+35*k+13 ≤ a ∧
    a < 7*((k+1)*(k+1))+35*(k+1)+13 ∧ IsPre a p ∧ 35 + 10*k ≤ p + 20 ∧ p ≤ 35 + 10*k + 10 := by
  intro a ha
  obtain ⟨k, h1, h2⟩ := round_exists (a - 13)
  rw [show 13 + (a - 13) = a by omega] at h1 h2
  have h1' : 7 * (k * k) + 35 * k + 13 ≤ a := h1
  have h2' : a < 7 * ((k + 1) * (k + 1)) + 35 * (k + 1) + 13 := h2
  have e2 := tk_succ' k
  obtain ⟨r, hr⟩ : ∃ r, a = 7 * (k * k) + 35 * k + 13 + r := ⟨a - (7 * (k * k) + 35 * k + 13), by omega⟩
  have hrl : r < 14 * (k + 3) := by omega
  obtain ⟨_, c2, c3, c4, c5⟩ := sqrt_wall k r a hrl hr
  refine ⟨k, ?_⟩
  by_cases hA : r + 4 ≤ 14 * (k + 3)
  · obtain ⟨p, hp, hp1, hp2⟩ := c2 hA
    exact ⟨p, h1', by omega, hp, hp1, by omega⟩
  by_cases hB : r + 3 = 14 * (k + 3)
  · exact ⟨_, h1', by omega, c3 hB, by omega, by omega⟩
  by_cases hC : r + 2 = 14 * (k + 3)
  · exact ⟨_, h1', by omega, c4 hC, by omega, by omega⟩
  · exact ⟨_, h1', by omega, c5 (by omega), by omega, by omega⟩

/-- the wall is at bounded distance from no line of slope n/m, n, m naturals, 0 < m -/
theorem wall_not_linear : ¬ ∃ n m C N : Nat, 0 < m ∧
    ∀ a, N ≤ a → ∀ p, IsPre a p → m * p ≤ n * a + C ∧ n * a ≤ m * p + C := by
  rintro ⟨n, m, C, N, hm, H⟩
  obtain ⟨k, hk⟩ : ∃ k, k = 2 * m + C + N + 10 := ⟨_, rfl⟩
  have hpre : IsPre (7 * (k * k) + 35 * k + 13) (35 + 10 * k) :=
    (sqrt_wall k 0 _ (by omega) (by omega)).1 rfl
  have hkk : k ≤ k * k := Nat.le_mul_self k
  have hN : N ≤ 7 * (k * k) + 35 * k + 13 := by omega
  obtain ⟨h1, h2⟩ := H _ hN _ hpre
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : 1 * (35 + 10 * k) ≤ m * (35 + 10 * k) := Nat.mul_le_mul_right _ hm
    omega
  · have hT : (7 * (k * k) + 35 * k + 13) ≤ n * (7 * (k * k) + 35 * k + 13) := by
      have := Nat.mul_le_mul_right (7 * (k * k) + 35 * k + 13) hn
      omega
    have hsq : k * (2 * m + C + 10) ≤ k * k := Nat.mul_le_mul_left _ (by omega)
    have e1 : m * (35 + 10 * k) = 35 * m + 10 * (m * k) := by
      grind
    have e2 : k * (2 * m + C + 10) = 2 * (m * k) + C * k + 10 * k := by
      grind
    have : C ≤ C * k := Nat.le_mul_of_pos_right _ (by omega)
    omega

#print axioms pre_unique
#print axioms sqrt_wall_all
#print axioms wall_not_linear

/-- two-sided square-root bounds on the wall -/
theorem sqrt_bounds {a p : Nat} (ha : 13 ≤ a) (hp : IsPre a p) :
    100 * a ≤ 7 * (p * p) + 280 * p ∧ 7 * (p * p) ≤ 100 * a + 280 * p + 275 := by
  obtain ⟨k, p', h1, h2, hp', l1, l2⟩ := sqrt_wall_all a ha
  have := pre_unique hp hp'
  subst this
  have e2 := tk_succ' k
  constructor
  · have hs : (15 + 10 * k) * (15 + 10 * k) ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
    have e : (15 + 10 * k) * (15 + 10 * k) = 225 + 300 * k + 100 * (k * k) := by
      grind
    omega
  · by_cases h45 : 45 ≤ p
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + 45 := ⟨p - 45, by omega⟩
      have hs : q * q ≤ (10 * k) * (10 * k) := Nat.mul_le_mul (by omega) (by omega)
      have e : (10 * k) * (10 * k) = 100 * (k * k) := by
        grind
      have e2 : (q + 45) * (q + 45) = q * q + 90 * q + 2025 := by
        grind
      omega
    · have : p * p ≤ 45 * p := Nat.mul_le_mul_right _ (by omega)
      omega

#print axioms sqrt_bounds

/-! ### Transport to S2 = [1,2,3,4,6] -/

end SqrtM

namespace LeadA

theorem sgFn_12346 : ∀ x, sgFn [1, 2, 3, 4, 6] x = x % 5 := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    have hin : ∀ m, m ∈ (([1, 2, 3, 4, 6] : List Nat).filterMap fun s =>
        if h : 0 < s ∧ s ≤ x then some (sgFn [1, 2, 3, 4, 6] (x - s)) else none) ↔
        ∃ s, 1 ≤ s ∧ s ≤ 4 ∧ s ≤ x ∧ (x - s) % 5 = m := by
      intro m
      rw [mem_moves]
      constructor
      · rintro ⟨s, hs, h0, h1, h2⟩
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
        rw [ih (x - s) (by omega)] at h2
        by_cases h6 : s = 6
        · exact ⟨1, by omega, by omega, by omega, by omega⟩
        · exact ⟨s, by omega, by omega, h1, h2⟩
      · rintro ⟨s, h0, h1, h2, h3⟩
        refine ⟨s, ?_, by omega, h2, ?_⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
        · rw [ih (x - s) (by omega), h3]
    rw [sgFn_eq]
    apply mex_eq
    · rw [hin]
      rintro ⟨s, h0, h1, h2, h3⟩
      omega
    · intro m hm
      rw [hin]
      exact ⟨x % 5 - m, by omega, by omega, by omega, by omega⟩

theorem IsP1_6_iff (a b : Nat) : IsP1 [1, 2, 3, 4, 6] a b ↔ IsP1 [1, 2, 3, 4] a b := by
  rw [IsP1_iff_sg _ (a + b) a b rfl, IsP1_iff_sg _ (a + b) a b rfl, sgFn_12346, sgFn_12346,
    sgFn_1234, sgFn_1234]

theorem outcome_eq6 : ∀ a b, outcome [1, 2, 5, 6] [1, 2, 3, 4, 6] a b =
    outcome [1, 2, 5, 6] [1, 2, 3, 4] a b := by
  intro a b
  have hW : IsP1 [1, 2, 3, 4, 6] = IsP1 [1, 2, 3, 4] := by
    funext x y; exact propext (IsP1_6_iff x y)
  have h : Eqn [1, 2, 5, 6] (IsP1 [1, 2, 3, 4]) (IsP0 [1, 2, 5, 6] [1, 2, 3, 4, 6]) := by
    have := IsP0_eqn [1, 2, 5, 6] [1, 2, 3, 4, 6]
    rwa [hW] at this
  have hu := Eqn.unique h (IsP0_eqn [1, 2, 5, 6] [1, 2, 3, 4]) a b
  rw [Bool.eq_iff_iff, outcome_iff, outcome_iff]
  exact hu

end LeadA

namespace SqrtM
open LeadA

/-- the row of the game [1,2,5,6] / [1,2,3,4,6] -/
def row6 (a d : Nat) : Bool := LeadA.outcome [1, 2, 5, 6] [1, 2, 3, 4, 6] a (a + d)

def IsPre6 (a p : Nat) : Prop :=
  (∀ d, p ≤ d → row6 a (d + 10) = row6 a d) ∧
  ∀ q, q < p → ∃ d, q ≤ d ∧ row6 a (d + 10) ≠ row6 a d

theorem row6_eq (a d : Nat) : row6 a d = row a d := by
  unfold row6 row; exact outcome_eq6 _ _

theorem IsPre6_iff (a p : Nat) : IsPre6 a p ↔ IsPre a p := by
  unfold IsPre6 IsPre; simp only [row6_eq]

theorem sqrt_wall6 (k r a : Nat) (hr : r < 14 * (k + 3)) (ha : a = 7 * (k * k) + 35 * k + 13 + r) :
    (r = 0 → IsPre6 a (35 + 10 * k)) ∧
    (r + 4 ≤ 14 * (k + 3) → ∃ p, IsPre6 a p ∧ 35 + 10 * k ≤ p + 20 ∧ p ≤ 35 + 10 * k) ∧
    (r + 3 = 14 * (k + 3) → IsPre6 a (35 + 10 * k + 5)) ∧
    (r + 2 = 14 * (k + 3) → IsPre6 a (35 + 10 * k + 10)) ∧
    (r + 1 = 14 * (k + 3) → IsPre6 a (35 + 10 * k - 5)) := by
  simp only [IsPre6_iff]
  exact sqrt_wall k r a hr ha

theorem sqrt_wall_all6 : ∀ a, 13 ≤ a → ∃ k p, 7*(k*k)+35*k+13 ≤ a ∧
    a < 7*((k+1)*(k+1))+35*(k+1)+13 ∧ IsPre6 a p ∧ 35 + 10*k ≤ p + 20 ∧ p ≤ 35 + 10*k + 10 := by
  simp only [IsPre6_iff]
  exact sqrt_wall_all

#print axioms LeadA.sgFn_12346
#print axioms LeadA.outcome_eq6
#print axioms sqrt_wall6
#print axioms sqrt_wall_all6

end SqrtM
