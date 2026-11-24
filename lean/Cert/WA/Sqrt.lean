import Cert.WA.Round
import SqrtMain
/-!
Wall A's certified law (`Family.Cert.WA.wall`) is the law of `SqrtM.sqrt_wall`:
same game, same tail period, same round starts t_k = 7k² + 35k + 13 and the same
onsets w_k = 35 + 10k, for every round k ≥ k0 = 33.
-/
namespace Family.Cert.WA

/-- g = Grundy function of Sub({1,2,3,4}), i.e. x mod 5 -/
theorem sg_eq (x : Nat) : LeadA.sgFn [1, 2, 3, 4] x = gv gpre gper x := by
  rw [sgFn_eq_gv [1, 2, 3, 4] 0 5 (by decide) x]
  rfl

/-- `IsPreG` of the certificate's game is `SqrtM.IsPre` -/
theorem isPreG_iff (a q : Nat) : IsPreG cert.S1 cert.gpre cert.gper cert.π a q ↔ SqrtM.IsPre a q := by
  have h : ∀ a b, LeadA.outcome [1, 2, 5, 6] [1, 2, 3, 4] a b = PG [1, 2, 5, 6] gpre gper a b :=
    outcome_eq_PG S1 [1, 2, 3, 4] gpre gper hS sg_eq
  show IsPreG S1 gpre gper 10 a q ↔ SqrtM.IsPre a q
  unfold IsPreG SqrtM.IsPre SqrtM.row
  simp only [h, S1]

theorem tRec_eq (n : Nat) :
    tRec 8791 33 14 42 n = 7 * ((33 + n) * (33 + n)) + 35 * (33 + n) + 13 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tRec, ih]
    rw [show 33 + (n + 1) = (33 + n) + 1 by omega]
    generalize 33 + n = m
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega

/-- round starts and onsets of the certificate equal SqrtM's for k ≥ 33 -/
theorem law_eq (k : Nat) (hk : cert.k0 ≤ k) :
    cert.t k = 7 * (k * k) + 35 * k + 13 ∧ cert.w0 + cert.Δ * k = 35 + 10 * k := by
  refine ⟨?_, rfl⟩
  show tRec 8791 33 14 42 (k - 33) = _
  have hk' : 33 ≤ k := hk
  rw [tRec_eq, show 33 + (k - 33) = k by omega]

/-- `Family.Cert.WA.wall`, restated in SqrtM's terms: for every k ≥ 33, row t_k = 7k²+35k+13 has
onset exactly 35 + 10k, and every row of round k has onset at most 35 + 10k + 20. -/
theorem wall_sqrt (k : Nat) (hk : 33 ≤ k) :
    SqrtM.IsPre (7 * (k * k) + 35 * k + 13) (35 + 10 * k) ∧
    ∀ a, 7 * (k * k) + 35 * k + 13 ≤ a → a < 7 * ((k + 1) * (k + 1)) + 35 * (k + 1) + 13 →
      ∃ q, SqrtM.IsPre a q ∧ q ≤ 35 + 10 * k + 20 := by
  obtain ⟨-, hw⟩ := wall
  obtain ⟨-, -, hpre, hrows⟩ := hw k hk
  obtain ⟨et, ew⟩ := law_eq k hk
  obtain ⟨et1, -⟩ := law_eq (k + 1) (by show 33 ≤ k + 1; omega)
  refine ⟨?_, fun a h1 h2 => ?_⟩
  · rw [← et, ← ew]; exact (isPreG_iff _ _).1 hpre
  · obtain ⟨q, hq, hqle⟩ := hrows a (by rw [et]; exact h1) (by rw [et1]; exact h2)
    exact ⟨q, (isPreG_iff _ _).1 hq, by rw [← ew]; exact hqle⟩

end Family.Cert.WA
