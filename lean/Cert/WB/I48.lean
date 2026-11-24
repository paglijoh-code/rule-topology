import Cert.WB.Wall
namespace Family.Cert.WB.I48
open Family
def rows : List (List Move) := [
[.rot 0 1, .tailRot 1, .fromRight 0],
[.rot 0 6, .tailRot 3, .fromRight 0, .fromLeft 0],
[.rot 0 3, .tailRot 1],
[.rot 0 6, .tailRot 3, .fromRight 0, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.rot 0 9, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromRight 0],
[.rot 0 11, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromLeft 0, .tailIn],
[.tailRot 1, .toLeft 0],
[.tailRot 3],
[.rot 0 1, .tailRot 1, .fromRight 0, .tailIn],
[.rot 0 6, .tailRot 3, .fromRight 0, .fromLeft 0],
[.rot 0 3, .tailRot 1],
[.rot 0 6, .tailRot 3, .fromRight 0, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.rot 0 9, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromRight 0, .tailIn],
[.rot 0 11, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromLeft 0],
[.tailRot 1, .toLeft 0, .tailIn],
[.tailRot 3],
[.rot 0 1, .tailRot 1, .fromRight 0]]
def s0 : Shape := ⟨[32, 16, 0, 0, 130, 4, 32, 65, 0, 0, 130, 4, 32, 16, 0, 0, 130, 4, 32, 65], [([0, 0, 130, 4, 32, 16, 0, 0, 130, 4, 32, 65], [0, 0, 130, 4, 32, 16, 0, 0, 130, 4, 32, 65, 0, 0, 130, 4, 32, 65, 0, 16, 130, 4, 32, 8, 0, 16, 130, 4, 32, 65, 0, 16, 130, 4, 32, 8, 0, 16, 130, 4, 8, 65, 0, 32, 130, 4, 16, 65, 32, 0, 130, 4, 16, 8, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 65, 8, 0, 130, 4, 32, 8, 0, 16, 130, 4, 8, 65, 0, 32, 2, 4, 16, 128, 32, 0, 66, 4, 128, 8, 33, 64, 2, 4, 128, 16, 65, 0, 2, 4, 128, 16, 8, 0, 32, 4, 128, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32])], [4, 130, 16, 8, 65, 32]⟩
def n0 : List Nat := [7]
def s1 : Shape := ⟨[32, 1, 0, 4, 8, 64, 130, 1, 0, 4, 8, 64, 32, 1, 0, 4, 8, 64, 130, 1], [([0, 4, 8, 64, 32, 1, 0, 4, 8, 64, 130, 1], [0, 4, 8, 64, 32, 1, 0, 4, 8, 64, 130, 1, 0, 4, 8, 64, 130, 1, 32, 4, 8, 64, 16, 1, 32, 4, 8, 64, 130, 1, 32, 4, 8, 64, 16, 1, 32, 4, 8, 16, 130, 1, 64, 4, 8, 32, 130, 65, 0, 4, 8, 32, 16, 65, 0, 4, 8, 32, 130, 65, 0, 4, 8, 32, 130, 65, 0, 4, 8, 32, 130, 65, 0, 4, 8, 32, 130, 16, 0, 4, 8, 65, 16, 0, 32, 4, 8, 16, 130, 0, 65, 4, 8, 32, 130, 65, 0, 4, 8, 32, 16, 65, 0, 4, 8, 32, 130, 65, 0, 4, 8, 32, 130, 16, 0, 4, 8, 65, 130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 8, 65, 16, 0, 32, 4, 8, 16, 2, 128, 1, 64, 8, 32, 4, 128, 1, 66, 8, 4, 0, 16, 2, 64, 8, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n1 : List Nat := [5]
theorem ok : segCheckF S1 gpre gper 1200 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 1200 + rows.length = 1225 := by decide
end Family.Cert.WB.I48
