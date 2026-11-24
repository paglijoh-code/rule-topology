/-
Kernel-checked H.A certificate for S1 = [3] -> S2 = [1, 4]: A0 = 0, q = 15, a0 = 3, T = 8, p = 5,
SG period 5.  `decide` (no `native_decide`) evaluates `checkCert` in the kernel.  The meaning
(theorem `leadA_3_14`) is in LeadAMain.lean, via `checkCert_sound`.
-/
import LeadAData
namespace LeadA

set_option maxRecDepth 100000 in
theorem leada_3_14_ok : checkCert [3] [1, 4] cert_3_14 = true := by decide

#print axioms leada_3_14_ok

end LeadA
