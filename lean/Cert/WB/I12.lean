import Cert.WB.Wall
namespace Family.Cert.WB.I12
open Family
def rows : List (List Move) := [
[.tailRot 1, .tailIn],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1, .tailIn]]
def s0 : Shape := ⟨[0, 65, 32, 0, 130, 4, 0, 16, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 8, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 0, 65, 8, 16, 130, 4, 32, 8, 0, 16, 130, 4, 8, 1, 0, 64, 32, 4, 16, 2, 0, 64, 33, 4, 130, 0, 8, 65, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32], [], [4, 130, 16, 8, 65, 32]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[16, 1, 32, 4, 8, 64, 130, 1, 32, 4, 8, 64, 130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 8, 65, 16, 0, 32, 4, 8, 16, 130, 0, 65, 4, 8, 32, 130, 65, 0, 4, 8, 32, 16, 1, 0, 4, 8, 64, 130, 1, 0, 4, 8, 64, 130, 16, 0, 4, 8, 65, 130, 16, 0, 4, 8, 33, 130, 16, 0, 64, 8, 33, 4, 16, 0, 130, 8, 4, 0, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8], [], [4, 32, 16, 130, 65, 8]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 300 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 300 + rows.length = 325 := by decide
end Family.Cert.WB.I12
