import Cert.WB.Wall
namespace Family.Cert.WB.I31
open Family
def rows : List (List Move) := [
[.rot 0 6, .tailRot 3, .fromLeft 0, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.rot 0 6, .tailRot 1, .fromRight 0, .tailIn],
[.tailRot 3],
[.tailRot 1],
[.rot 0 6, .tailRot 3, .fromLeft 0, .tailIn],
[.tailRot 1],
[.tailRot 3, .fromRight 0, .tailIn],
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
[.tailRot 3, .fromRight 0, .tailIn],
[.rot 0 6, .tailRot 1, .fromRight 0],
[.tailRot 3],
[.tailRot 1],
[.rot 0 6, .tailRot 3, .fromLeft 0, .tailIn]]
def s0 : Shape := ⟨[130, 64, 0, 4, 8, 1, 130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 8, 65, 16, 0, 32, 4, 8, 16, 130, 0, 65, 4, 8, 32, 130, 65, 0, 4, 8, 32, 16, 65, 0, 4, 8, 32, 130, 65, 0, 4, 8, 32, 130, 16, 0, 4, 8, 65, 130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 8, 65, 16, 0, 32, 4, 8, 16, 130, 0, 65, 4, 8, 32, 130, 65, 0, 4, 8, 32, 16, 65, 0, 4, 8, 32, 130, 65], [([0, 4, 8, 32, 16, 65, 0, 4, 8, 32, 130, 65], [0, 4, 8, 32, 16, 65, 0, 4, 8, 32, 130, 1, 0, 4, 8, 64, 0, 16, 32, 132, 8, 0, 16, 2, 128, 65, 8, 0, 32, 2, 128, 65, 8, 4, 32, 16, 128, 65, 8, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := [3]
def s1 : Shape := ⟨[2, 64, 8, 16, 33, 4, 2, 128, 8, 16, 65, 4, 130, 0, 8, 16, 65, 32, 130, 0, 8, 16, 65, 4, 130, 0, 8, 16, 65, 4, 32, 0, 8, 16, 130, 4, 32, 65, 8, 16, 130, 4, 32, 65, 8, 16, 130, 32, 0, 65, 8, 16, 32, 4, 0, 130, 8, 16, 65, 4, 130, 0, 8, 16, 65, 32, 130], [([0, 8, 16, 65, 4, 130, 0, 8, 16, 65, 32, 130], [0, 8, 16, 65, 4, 130, 0, 8, 16, 65, 32, 130, 0, 8, 16, 65, 4, 2, 0, 8, 16, 128, 0, 32, 65, 8, 16, 0, 32, 4, 0, 130, 16, 1, 64, 4, 0, 130, 16, 8, 64, 32, 0, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32])], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := [5]
theorem ok : segCheckF S1 gpre gper 775 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 775 + rows.length = 800 := by decide
end Family.Cert.WB.I31
