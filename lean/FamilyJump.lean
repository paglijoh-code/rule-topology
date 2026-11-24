/-
Jump laws for a family of rounds (all over `Int`, no Mathlib).

Setup.  Round k starts at row t k and has length gap_k = α k + β, so
  t (k+1) = t k + α k + β,
while the wall position moves by a constant Δ per round,
  w (k+1) = w k + Δ.
Closed forms: `w k = w0 + Δ k`, `2 t k = 2 t0 + 2 β k + α k (k-1)`; the second
difference of t is the constant α; eliminating k gives the exact division-free
identity `t_quad_in_w`, 2Δ² t = 2Δ² t0 + 2βΔ (w-w0) + α (w-w0)(w-w0-Δ).

`wall_sqrt_bounds` is the integer form of "wall position p = sqrt(2Δ² a / α) + O(1)":
for a row a of round k (t k ≤ a < t (k+1)) and a wall position p within c of w k,
  α p² ≤ 2Δ² a + A1 |p| + B1   and   2Δ² a ≤ α p² + A2 |p| + B2,
with A1 B1 A2 B2 explicit (`A1 .. B2` below), |p| written `ab p`.

Link to `SqrtM.sqrt_wall` (SqrtCor/SqrtMain): there the r = 0 rows are
t_k = 7k²+35k+13 and the wall is w_k = 35 + 10k, i.e. α=14, β=42, Δ=10, t0=13, w0=35
(gap_k = 14(k+3)); `wallA_check` verifies the closed form reproduces t_k.  The
constants of `SqrtM.sqrt_bounds` (100 a vs 7 p²) are the case 2Δ²/α = 100/7.
-/
namespace Family

/-- absolute value as an integer -/
def ab (x : Int) : Int := (x.natAbs : Int)

theorem ab_nn (x : Int) : 0 ≤ ab x := by unfold ab; omega
theorem le_ab (x : Int) : x ≤ ab x ∧ -x ≤ ab x := by unfold ab; omega
theorem ab_mul (x y : Int) : ab (x * y) = ab x * ab y := by
  unfold ab; rw [Int.natAbs_mul]; simp

theorem mulb (u v U V : Int) (hu : ab u ≤ U) (hv : ab v ≤ V) :
    -(U * V) ≤ u * v ∧ u * v ≤ U * V := by
  have h1 := le_ab (u * v); rw [ab_mul] at h1
  have h2 := Int.mul_le_mul hu hv (ab_nn v) (by have := ab_nn u; omega)
  omega

section
variable {α β Δ t0 w0 : Int} {t w : Nat → Int}

theorem w_closed (hw0 : w 0 = w0) (hw : ∀ k, w (k + 1) = w k + Δ) (k : Nat) :
    w k = w0 + Δ * k := by
  induction k with
  | zero => simp [hw0]
  | succ k ih => rw [hw k, ih]; push_cast; grind

theorem t_closed (ht0 : t 0 = t0) (ht : ∀ k, t (k + 1) = t k + α * k + β) (k : Nat) :
    2 * t k = 2 * t0 + 2 * β * k + α * k * (k - 1) := by
  induction k with
  | zero => simp [ht0]
  | succ k ih => rw [ht k]; push_cast; grind

theorem t_second_diff (ht : ∀ k, t (k + 1) = t k + α * k + β) (k : Nat) :
    t (k + 2) - 2 * t (k + 1) + t k = α := by
  have h1 := ht (k + 1)
  have h0 := ht k
  push_cast at h1
  grind

theorem t_quad_in_w (ht0 : t 0 = t0) (hw0 : w 0 = w0)
    (ht : ∀ k, t (k + 1) = t k + α * k + β) (hw : ∀ k, w (k + 1) = w k + Δ) (k : Nat) :
    2 * Δ ^ 2 * t k = 2 * Δ ^ 2 * t0 + 2 * β * Δ * (w k - w0)
      + α * (w k - w0) * (w k - w0 - Δ) := by
  have h1 := t_closed ht0 ht k
  have h2 := w_closed hw0 hw k
  rw [h2]
  grind

/-- coefficients of the square-root bounds; S = c + |w0| -/
def A1 (α β Δ w0 c : Int) : Int := ab (2 * β - α) * Δ + 2 * α * (c + ab w0)
def B1 (α β Δ t0 w0 c : Int) : Int :=
  2 * Δ ^ 2 * ab t0 + ab (2 * β - α) * Δ * (c + ab w0) + α * ((c + ab w0) * (c + ab w0))
def A2 (α β Δ w0 c : Int) : Int := A1 α β Δ w0 c + 2 * Δ * α
def B2 (α β Δ t0 w0 c : Int) : Int :=
  B1 α β Δ t0 w0 c + 2 * Δ * α * (c + ab w0) + 2 * Δ ^ 2 * ab β

theorem wall_sqrt_bounds (ht0 : t 0 = t0) (hw0 : w 0 = w0)
    (ht : ∀ k, t (k + 1) = t k + α * k + β) (hw : ∀ k, w (k + 1) = w k + Δ)
    (hα : 0 ≤ α) (hΔ : 0 < Δ) (k : Nat) (a : Int) (ha1 : t k ≤ a) (ha2 : a < t (k + 1))
    (p c : Int) (hp1 : w k - c ≤ p) (hp2 : p ≤ w k + c) (hc : 0 ≤ c) :
    α * p ^ 2 ≤ 2 * Δ ^ 2 * a + A1 α β Δ w0 c * ab p + B1 α β Δ t0 w0 c ∧
    2 * Δ ^ 2 * a ≤ α * p ^ 2 + A2 α β Δ w0 c * ab p + B2 α β Δ t0 w0 c := by
  have hq := t_quad_in_w ht0 hw0 ht hw k
  have hx := w_closed hw0 hw k
  have htk := ht k
  -- s = w k - w0 - p, |s| <= S
  obtain ⟨s, hs⟩ : ∃ s, s = w k - w0 - p := ⟨_, rfl⟩
  have hwk : w k = p + s + w0 := by omega
  obtain ⟨S, hS⟩ : ∃ S, S = c + ab w0 := ⟨_, rfl⟩
  have hw0b := le_ab w0
  have hSs : ab s ≤ S := by unfold ab at *; omega
  have hS0 : 0 ≤ S := by have := ab_nn w0; omega
  have hΔ2 : 0 ≤ Δ ^ 2 := by
    rw [show Δ ^ 2 = Δ * Δ by grind]; exact Int.mul_nonneg (Int.le_of_lt hΔ) (Int.le_of_lt hΔ)
  have hΔ3 : 0 ≤ 2 * Δ ^ 2 := by omega
  -- sandwich on 2 Δ² a
  have h1 : 2 * Δ ^ 2 * t k ≤ 2 * Δ ^ 2 * a := Int.mul_le_mul_of_nonneg_left ha1 hΔ3
  have h2 : 2 * Δ ^ 2 * a ≤ 2 * Δ ^ 2 * (t k + α * k + β) :=
    Int.mul_le_mul_of_nonneg_left (by omega) hΔ3
  -- exact expansions
  have E1 : 2 * Δ ^ 2 * t k - α * p ^ 2 =
      2 * Δ ^ 2 * t0 + ((2 * β - α) * Δ) * p + ((2 * β - α) * Δ) * s
        + 2 * α * (p * s) + α * (s * s) := by
    rw [hwk] at hq; grind
  have E2 : 2 * Δ ^ 2 * (t k + α * k + β) - 2 * Δ ^ 2 * t k =
      2 * Δ * α * p + 2 * Δ * α * s + 2 * Δ ^ 2 * β := by
    have : Δ * (k : Int) = p + s := by omega
    grind
  -- bounds on the pieces
  have b0 := le_ab t0
  have bt0 : -(2 * Δ ^ 2 * ab t0) ≤ 2 * Δ ^ 2 * t0 ∧ 2 * Δ ^ 2 * t0 ≤ 2 * Δ ^ 2 * ab t0 := by
    constructor
    · have := Int.mul_le_mul_of_nonneg_left b0.2 hΔ3; grind
    · exact Int.mul_le_mul_of_nonneg_left b0.1 hΔ3
  have abD : ab ((2 * β - α) * Δ) = ab (2 * β - α) * Δ := by
    rw [ab_mul]; have : ab Δ = Δ := by unfold ab; omega
    rw [this]
  have bp := mulb ((2 * β - α) * Δ) p (ab (2 * β - α) * Δ) (ab p) (by omega) (by omega)
  have bs := mulb ((2 * β - α) * Δ) s (ab (2 * β - α) * Δ) S (by omega) hSs
  have bps := mulb p s (ab p) S (by omega) hSs
  have bss := mulb s s S S hSs hSs
  have a2 : 0 ≤ 2 * α := by omega
  have bps' := Int.mul_le_mul_of_nonneg_left bps.1 a2
  have bps'' := Int.mul_le_mul_of_nonneg_left bps.2 a2
  have bss' := Int.mul_le_mul_of_nonneg_left bss.1 hα
  have bss'' := Int.mul_le_mul_of_nonneg_left bss.2 hα
  have dα : 0 ≤ 2 * Δ * α := by
    exact Int.mul_nonneg (by omega) hα
  have bpp := le_ab p
  have bsS := le_ab s
  have c1 := Int.mul_le_mul_of_nonneg_left bpp.1 dα
  have c1' := Int.mul_le_mul_of_nonneg_left bpp.2 dα
  have c2 := Int.mul_le_mul_of_nonneg_left (show s ≤ S by omega) dα
  have c2' := Int.mul_le_mul_of_nonneg_left (show -s ≤ S by omega) dα
  have bb := le_ab β
  have c3 := Int.mul_le_mul_of_nonneg_left bb.1 hΔ3
  have c3' := Int.mul_le_mul_of_nonneg_left bb.2 hΔ3
  -- unfold the coefficients
  have eA1 : A1 α β Δ w0 c * ab p =
      ab (2 * β - α) * Δ * ab p + 2 * α * S * ab p := by
    unfold A1; rw [← hS]; grind
  have eA2 : A2 α β Δ w0 c * ab p =
      ab (2 * β - α) * Δ * ab p + 2 * α * S * ab p + 2 * Δ * α * ab p := by
    unfold A2; unfold A1; rw [← hS]; grind
  have eB1 : B1 α β Δ t0 w0 c =
      2 * Δ ^ 2 * ab t0 + ab (2 * β - α) * Δ * S + α * (S * S) := by
    unfold B1; rw [← hS]
  have eB2 : B2 α β Δ t0 w0 c =
      2 * Δ ^ 2 * ab t0 + ab (2 * β - α) * Δ * S + α * (S * S)
        + 2 * Δ * α * S + 2 * Δ ^ 2 * ab β := by
    unfold B2 B1; rw [← hS]
  rw [eA1, eB1]
  rw [eA2, eB2]
  constructor <;> grind
end

/-! ### Sanity check: wall A, α=14, β=42, Δ=10, t0=13, w0=35 -/

theorem wallA_check (t : Nat → Int)
    (ht0 : t 0 = 13) (ht : ∀ k, t (k + 1) = t k + 14 * k + 42) (k : Nat) :
    t k = 7 * (k : Int) * k + 35 * k + 13 := by
  have := t_closed ht0 ht k
  grind

theorem wallA_w (w : Nat → Int) (hw0 : w 0 = 35) (hw : ∀ k, w (k + 1) = w k + 10) (k : Nat) :
    w k = 35 + 10 * k := w_closed hw0 hw k

end Family
