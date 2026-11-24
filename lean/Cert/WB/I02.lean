import Cert.WB.Wall
namespace Family.Cert.WB.I02
open Family
def rows : List (List Move) := [
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3, .tailIn],
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
[.tailRot 1]]
def s0 : Shape := ⟨[132, 0, 66, 16, 8, 4, 128, 0, 2, 16, 8, 65, 32, 0, 4, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32], [], [4, 130, 16, 8, 65, 32]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[0, 4, 32, 16, 128, 8, 0, 4, 32, 16, 130, 65, 0, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8], [], [4, 32, 16, 130, 65, 8]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 50 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 50 + rows.length = 75 := by decide
end Family.Cert.WB.I02
