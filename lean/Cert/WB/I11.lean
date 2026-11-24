import Cert.WB.Wall
namespace Family.Cert.WB.I11
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
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3]]
def s0 : Shape := ⟨[130, 16, 8, 0, 0, 65, 130, 16, 32, 0, 0, 65, 130, 16, 32, 0, 8, 65, 130, 16, 4, 0, 8, 65, 130, 16, 32, 0, 8, 65, 130, 16, 4, 0, 8, 65, 130, 4, 32, 0, 16, 65, 130, 0, 8, 16, 0, 65, 130, 8, 4, 32, 0, 1, 130, 8, 0, 32, 0, 16, 130, 64, 1, 4, 0, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8], [], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[0, 65, 32, 0, 130, 4, 0, 16, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 8, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 0, 65, 8, 16, 130, 4, 32, 8, 0, 16, 130, 4, 8, 1, 0, 64, 32, 4, 16, 2, 0, 64, 33, 4, 130, 0, 8, 65, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32], [], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 275 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 275 + rows.length = 300 := by decide
end Family.Cert.WB.I11
