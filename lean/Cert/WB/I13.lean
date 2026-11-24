import Cert.WB.Wall
namespace Family.Cert.WB.I13
open Family
def rows : List (List Move) := [
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
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1, .tailIn],
[.tailRot 3]]
def s0 : Shape := ⟨[16, 1, 32, 4, 8, 64, 130, 1, 32, 4, 8, 64, 130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 8, 65, 16, 0, 32, 4, 8, 16, 130, 0, 65, 4, 8, 32, 130, 65, 0, 4, 8, 32, 16, 1, 0, 4, 8, 64, 130, 1, 0, 4, 8, 64, 130, 16, 0, 4, 8, 65, 130, 16, 0, 4, 8, 33, 130, 16, 0, 64, 8, 33, 4, 16, 0, 130, 8, 4, 0, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8], [], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[32, 65, 8, 16, 130, 32, 0, 65, 8, 16, 32, 4, 0, 130, 8, 16, 65, 4, 130, 0, 8, 16, 65, 32, 130, 0, 8, 16, 65, 4, 130, 0, 8, 16, 65, 4, 32, 0, 8, 16, 130, 4, 32, 65, 8, 16, 130, 4, 32, 65, 8, 16, 130, 32, 0, 65, 8, 16, 32, 4, 0, 130, 8, 16, 65, 4, 130, 0, 8, 16, 65, 32, 0, 0, 8, 16, 66, 4, 0, 1, 128, 16, 66, 8, 32, 1, 132, 16, 8, 0, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32], [], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 325 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 325 + rows.length = 350 := by decide
end Family.Cert.WB.I13
