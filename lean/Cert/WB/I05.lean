import Cert.WB.Wall
namespace Family.Cert.WB.I05
open Family
def rows : List (List Move) := [
[.tailRot 3],
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
[.tailRot 3]]
def s0 : Shape := ⟨[130, 8, 32, 16, 0, 1, 130, 8, 64, 16, 0, 33, 130, 64, 4, 0, 32, 1, 130, 64, 8, 0, 32, 16, 130, 64, 8, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8], [], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[32, 16, 8, 0, 130, 4, 16, 65, 8, 32, 2, 4, 16, 128, 8, 32, 66, 4, 128, 8, 1, 64, 2, 4, 128, 16, 1, 64, 32, 4, 128, 16, 8, 64, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32], [], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 125 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 125 + rows.length = 150 := by decide
end Family.Cert.WB.I05
