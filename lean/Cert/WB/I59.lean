import Cert.WB.Wall
namespace Family.Cert.WB.I59
open Family
def rows : List (List Move) := [
[.tailRot 3],
[.rot 0 1, .tailRot 1, .fromRight 0],
[.rot 0 6, .tailRot 3, .fromRight 0, .fromLeft 0, .tailIn],
[.rot 0 3, .tailRot 1],
[.rot 0 6, .tailRot 3, .fromRight 0],
[.tailRot 1],
[.tailRot 3, .tailIn],
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
[.tailRot 3, .tailIn],
[.rot 0 9, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromRight 0],
[.rot 0 11, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromLeft 0, .tailIn],
[.tailRot 1, .toLeft 0],
[.tailRot 3]]
def s0 : Shape := ⟨[130, 16, 8, 0, 0, 65, 130, 16, 32, 0, 0, 65, 130, 16, 8, 0, 0, 65, 130, 16, 32], [([0, 0, 65, 130, 16, 8, 0, 0, 65, 130, 16, 32], [0, 0, 65, 130, 16, 8, 0, 0, 65, 130, 16, 32, 0, 0, 65, 130, 16, 32, 0, 8, 65, 130, 16, 4, 0, 8, 65, 130, 16, 32, 0, 8, 65, 130, 16, 4, 0, 8, 65, 130, 4, 32, 0, 16, 65, 130, 0, 8, 16, 0, 65, 130, 8, 4, 32, 0, 1, 130, 8, 0, 32, 0, 16, 130, 64, 1, 4, 0, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := [13]
def s1 : Shape := ⟨[32, 16, 0, 0, 130, 4, 32, 65, 0, 0, 130, 4, 32, 16, 0, 0, 130, 4, 32, 65], [([0, 0, 130, 4, 32, 16, 0, 0, 130, 4, 32, 65], [0, 0, 130, 4, 32, 16, 0, 0, 130, 4, 32, 65, 0, 0, 130, 4, 32, 65, 0, 16, 130, 4, 32, 8, 0, 16, 130, 4, 32, 65, 0, 16, 130, 4, 32, 8, 0, 16, 130, 4, 8, 65, 0, 32, 130, 4, 16, 65, 32, 0, 130, 4, 16, 8, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 0, 65, 8, 16, 130, 4, 32, 8, 0, 16, 130, 4, 8, 1, 0, 64, 32, 4, 16, 2, 0, 64, 33, 4, 130, 0, 8, 65, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32])], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := [11]
theorem ok : segCheckF S1 gpre gper 1475 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 1475 + rows.length = 1500 := by decide
end Family.Cert.WB.I59
