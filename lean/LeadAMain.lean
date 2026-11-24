/-
Milestone 1 outcome: the two-heap outcome of the one-push game Sub([3]) -> Sub([1,4]) is
eventually doubly periodic with A0 = 0, q = 15, T = 8, p = 5, in terms of `outcome`
(the table builder of `LeadADefs`, proved equal to the relational spec `IsP0` in `LeadASpec`).
Proof: the general soundness theorem `checkCert_sound` (`LeadASound`) applied to the
kernel-checked certificate `leada_3_14_ok` (`LeadAProof`).
-/
import LeadASound
import LeadAProof
namespace LeadA

/-- For the pair Sub([3]) -> Sub([1,4]): for every a (A0 = 0), d, the outcome of heaps
(a + 15, a + 15 + d) equals that of (a, a + d); and for every a and d >= 8 the outcome of heaps
(a, a + d + 5) equals that of (a, a + d).  Here `outcome S1 S2 a b = true` means the player to
move loses (P), with one push allowed from Sub(S1) to Sub(S2). -/
theorem leadA_3_14 :
    (∀ a d, outcome [3] [1, 4] (a + 15) (a + 15 + d) = outcome [3] [1, 4] a (a + d)) ∧
    (∀ a d, 8 ≤ d → outcome [3] [1, 4] a (a + d + 5) = outcome [3] [1, 4] a (a + d)) := by
  obtain ⟨-, -, h1, h2⟩ := checkCert_sound [3] [1, 4] cert_3_14 leada_3_14_ok
  exact ⟨fun a d => h1 a (Nat.zero_le _) d, fun a d hd => h2 a (Nat.zero_le _) d hd⟩

/-- Relational form: the same statement for the spec `IsP0` (P-positions of the game). -/
theorem leadA_3_14_spec :
    (∀ a d, IsP0 [3] [1, 4] (a + 15) (a + 15 + d) ↔ IsP0 [3] [1, 4] a (a + d)) ∧
    (∀ a d, 8 ≤ d → (IsP0 [3] [1, 4] a (a + d + 5) ↔ IsP0 [3] [1, 4] a (a + d))) := by
  obtain ⟨h1, h2⟩ := leadA_3_14
  refine ⟨fun a d => ?_, fun a d hd => ?_⟩
  · rw [← outcome_iff, ← outcome_iff, h1]
  · rw [← outcome_iff, ← outcome_iff, h2 a d hd]

#print axioms leadA_3_14
#print axioms leadA_3_14_spec
#print axioms checkCert_sound
#print axioms outcome_iff

end LeadA
