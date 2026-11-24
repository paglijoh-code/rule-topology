import Cert.WB.Wall
namespace Family.Cert.WB.I17
open Family
def rows : List (List Move) := [
[.tailRot 3],
[.rot 0 9, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromRight 0, .tailIn],
[.rot 0 11, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromRight 0, .fromLeft 0],
[.tailRot 1, .toLeft 0, .tailIn],
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
[.rot 0 1, .tailRot 1, .expand 0 0],
[.tailRot 3, .tailIn, .split 0 13 12 2],
[.rot 0 3, .tailRot 1],
[.rot 0 6, .tailRot 3, .expand 0 0],
[.tailRot 1],
[.tailRot 3, .tailIn]]
def s0 : Shape := ⟨[130, 0, 32, 16, 0, 65, 130, 0, 8, 16, 0, 65, 130, 0, 32, 16, 0, 65, 130], [([0, 8, 16, 0, 65, 130, 0, 32, 16, 0, 65, 130], [0, 8, 16, 0, 65, 130, 0, 32, 16, 0, 65, 130, 0, 8, 16, 0, 65, 130, 8, 32, 16, 0, 65, 130, 8, 32, 16, 0, 65, 130, 8, 4, 0, 0, 65, 130, 16, 32, 0, 8, 1, 130, 16, 64, 4, 8, 33, 130, 64, 4, 0, 32, 16, 130, 64, 8, 0, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := [2]
def s1 : Shape := ⟨[0, 65, 32, 0, 130, 4, 0, 16, 32, 0, 130, 4, 0, 65, 32, 0, 130, 4, 0, 16, 32, 0, 130, 4, 0, 65, 32, 0, 130, 4, 0, 16, 32, 0, 130, 4, 0, 65, 32, 0, 130, 4, 0, 65, 32, 16, 130, 4, 0, 8, 32, 16, 130, 4, 0, 65, 32, 16, 130, 4, 0, 8, 32, 16, 130, 4, 8, 65, 32, 0, 130, 4, 16, 1, 32, 0, 130, 4, 16, 8, 64, 0, 130, 4, 32, 65, 0, 16, 2, 4, 8, 128, 0, 32, 66, 4, 128, 16, 1, 64, 2, 4, 128, 16, 8, 64, 32, 4, 128, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32], [], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 425 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 425 + rows.length = 450 := by decide
end Family.Cert.WB.I17
