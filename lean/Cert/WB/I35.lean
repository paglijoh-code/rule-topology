import Cert.WB.Wall
namespace Family.Cert.WB.I35
open Family
def rows : List (List Move) := [
[.tailRot 3],
[.rot 0 1, .tailRot 1, .fromRight 0],
[.rot 0 6, .tailRot 3, .fromRight 0, .fromLeft 0, .tailIn],
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
[.tailRot 3]]
def s0 : Shape := ⟨[130, 16, 8, 0, 0, 65, 130, 16, 32, 0, 0, 65, 130, 16, 8, 0, 0, 65, 130, 16, 32], [([0, 0, 65, 130, 16, 8, 0, 0, 65, 130, 16, 32], [0, 0, 65, 130, 16, 8, 0, 0, 65, 130, 16, 32, 0, 0, 65, 130, 16, 32, 0, 8, 65, 130, 16, 4, 0, 8, 65, 130, 16, 32, 0, 8, 65, 130, 16, 4, 0, 8, 65, 130, 4, 0, 32, 0, 16, 130, 8, 1, 32, 0, 16, 130, 65, 0, 4, 0, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := [8]
def s1 : Shape := ⟨[32, 16, 0, 0, 130, 4, 32, 65, 0, 0, 130, 4, 32, 16, 0, 0, 130, 4, 32, 65], [([0, 0, 130, 4, 32, 16, 0, 0, 130, 4, 32, 65], [0, 0, 130, 4, 32, 16, 0, 0, 130, 4, 32, 65, 0, 0, 130, 4, 32, 65, 0, 16, 130, 4, 32, 8, 0, 16, 130, 4, 32, 65, 0, 16, 130, 4, 32, 8, 0, 16, 130, 4, 8, 65, 0, 32, 130, 4, 16, 65, 32, 0, 130, 4, 16, 8, 0, 0, 130, 4, 32, 65, 0, 16, 130, 4, 8, 1, 0, 32, 130, 4, 16, 1, 64, 0, 130, 4, 16, 1, 8, 0, 32, 4, 16, 2, 8, 64, 33, 4, 130, 0, 8, 65, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32])], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := [6]
theorem ok : segCheckF S1 gpre gper 875 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 875 + rows.length = 900 := by decide
end Family.Cert.WB.I35
