/- Negative controls: corrupted certificates must FAIL the same checker (kernel-checked by decide). -/
import LeadAData
namespace LeadA

def mutRow (c : Cert) (i : Nat) (f : Row → Row) : Cert := { c with rows := c.rows.modify i f }

set_option maxRecDepth 100000

-- one preperiod cell of row 3 flipped
theorem mut_flipPre : checkCert [3] [1, 4] (mutRow cert_3_14 3 fun R => { R with pre := R.pre.modify 1 not }) = false := by decide
-- one cycle cell of row 5 flipped
theorem mut_flipCyc : checkCert [3] [1, 4] (mutRow cert_3_14 5 fun R => { R with cyc := R.cyc.modify 0 not }) = false := by decide
-- window repeat claimed with the wrong shift q
theorem mut_badQ : checkCert [3] [1, 4] { cert_3_14 with q := 10 } = false := by decide
-- wrong SG period (not a period of g of Sub({1,4}))
theorem mut_badG : checkCert [3] [1, 4] { cert_3_14 with gper := 4, q := 16 } = false := by decide
-- period bound p too small
theorem mut_badP : checkCert [3] [1, 4] { cert_3_14 with p := 1 } = false := by decide
-- a certificate for a different pair does not certify this one
theorem mut_wrongPair : checkCert [3] [1, 3] cert_3_14 = false := by decide

end LeadA
