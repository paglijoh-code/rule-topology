import Cert.WB.Wall
namespace Family.Cert.WB.I07
open Family
def rows : List (List Move) := [
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
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
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3]]
def s0 : Shape := ⟨[130, 64, 0, 4, 8, 1, 32, 64, 0, 4, 8, 33, 130, 16, 0, 4, 8, 65, 0, 16, 32, 132, 8, 0, 16, 2, 128, 65, 8, 0, 32, 2, 128, 65, 8, 4, 32, 16, 128, 65, 8, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8], [], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[32, 65, 8, 16, 130, 32, 0, 65, 8, 16, 32, 4, 0, 130, 8, 16, 65, 4, 130, 0, 8, 16, 65, 4, 32, 0, 8, 16, 130, 4, 32, 1, 8, 16, 66, 0, 32, 1, 8, 16, 0, 4, 32, 0, 130, 16, 1, 64, 32, 0, 132, 16, 8, 64, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32], [], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 175 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 175 + rows.length = 200 := by decide
end Family.Cert.WB.I07
