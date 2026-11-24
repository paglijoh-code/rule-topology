import Cert.WB.Wall
namespace Family.Cert.WB.I58
open Family
def rows : List (List Move) := [
[.rot 0 6, .tailRot 1, .fromRight 0],
[.tailRot 3],
[.tailRot 1, .tailIn],
[.rot 0 6, .tailRot 3, .fromLeft 0],
[.rot 0 4, .tailRot 1, .fromRight 0],
[.tailRot 3, .tailIn],
[.rot 0 6, .tailRot 1],
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
[.tailRot 1, .toLeft 0, .tailIn]]
def s0 : Shape := ⟨[32, 65, 8, 130, 0, 4, 32, 65, 8, 16, 0, 4, 32, 65, 8, 130], [([0, 4, 32, 65, 8, 16, 0, 4, 32, 65, 8, 130], [0, 4, 32, 65, 8, 16, 0, 4, 32, 65, 8, 130, 0, 4, 32, 65, 130, 16, 0, 8, 32, 65, 4, 0, 8, 0, 32, 65, 4, 130, 16, 0, 32, 65, 4, 0, 16, 0, 8, 65, 4, 0, 130, 0, 8, 65, 32, 0, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32])], [4, 130, 16, 8, 65, 32]⟩
def n0 : List Nat := [15]
def s1 : Shape := ⟨[130, 16, 8, 0, 0, 65, 130, 16, 32, 0, 0, 65, 130, 16, 8, 0, 0, 65, 130, 16, 32], [([0, 0, 65, 130, 16, 8, 0, 0, 65, 130, 16, 32], [0, 0, 65, 130, 16, 8, 0, 0, 65, 130, 16, 32, 0, 0, 65, 130, 16, 32, 0, 8, 65, 130, 16, 4, 0, 8, 65, 130, 16, 32, 0, 8, 65, 130, 16, 4, 0, 8, 65, 130, 4, 32, 0, 16, 65, 130, 0, 8, 16, 0, 65, 130, 8, 4, 32, 0, 1, 130, 8, 0, 32, 0, 16, 130, 64, 1, 4, 0, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n1 : List Nat := [13]
theorem ok : segCheckF S1 gpre gper 1450 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 1450 + rows.length = 1475 := by decide
end Family.Cert.WB.I58
