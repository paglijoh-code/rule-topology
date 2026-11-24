import Cert.WB.Wall
namespace Family.Cert.WB.I06
open Family
def rows : List (List Move) := [
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
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
[.tailRot 1, .tailIn],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1]]
def s0 : Shape := ⟨[32, 16, 8, 0, 130, 4, 16, 65, 8, 32, 2, 4, 16, 128, 8, 32, 66, 4, 128, 8, 1, 64, 2, 4, 128, 16, 1, 64, 32, 4, 128, 16, 8, 64, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32], [], [4, 130, 16, 8, 65, 32]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[130, 64, 0, 4, 8, 1, 32, 64, 0, 4, 8, 33, 130, 16, 0, 4, 8, 65, 0, 16, 32, 132, 8, 0, 16, 2, 128, 65, 8, 0, 32, 2, 128, 65, 8, 4, 32, 16, 128, 65, 8, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8], [], [4, 32, 16, 130, 65, 8]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 150 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 150 + rows.length = 175 := by decide
end Family.Cert.WB.I06
