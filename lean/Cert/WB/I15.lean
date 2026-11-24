import Cert.WB.Wall
namespace Family.Cert.WB.I15
open Family
def rows : List (List Move) := [
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
[.tailRot 3, .tailIn, .split 0 35 12 2],
[.rot 0 6, .tailRot 1, .fromRight 0],
[.tailRot 3],
[.tailRot 1],
[.rot 0 6, .tailRot 3, .fromLeft 0, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.rot 0 6, .tailRot 1, .fromRight 0, .tailIn],
[.tailRot 3],
[.tailRot 1],
[.rot 0 6, .tailRot 3, .fromLeft 0, .tailIn],
[.tailRot 1],
[.tailRot 3, .fromRight 0, .tailIn]]
def s0 : Shape := ⟨[128, 16, 32, 0, 8, 4, 128, 16, 32, 0, 8, 65, 130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 65, 0, 130, 16, 32, 65, 8, 0, 4, 16, 32, 130, 8, 4, 0, 16, 32, 130, 65, 4, 0, 16, 32, 130, 8, 4, 0, 16, 32, 130, 65, 4, 0, 16, 32, 130, 8, 4, 0, 16, 32, 2, 65, 4, 128, 16, 32, 66, 8, 0, 0, 0, 32, 132, 16, 1, 2, 8, 32, 16, 1, 64, 8, 4, 32, 16, 130, 64, 8, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8], [], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[32, 65, 8, 130, 0, 4, 32, 65, 130, 16, 0, 8, 32, 65, 4, 16, 8, 0, 32, 65, 4, 130, 8], [([0, 32, 65, 4, 16, 8, 0, 32, 65, 4, 130, 8], [0, 32, 65, 4, 16, 8, 0, 32, 65, 4, 130, 8, 0, 32, 65, 132, 16, 0, 0, 0, 65, 8, 32, 2, 4, 16, 65, 32, 2, 128, 16, 8, 65, 32, 4, 128, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32])], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := [3]
theorem ok : segCheckF S1 gpre gper 375 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 375 + rows.length = 400 := by decide
end Family.Cert.WB.I15
