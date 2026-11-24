import Cert.WB.Wall
namespace Family.Cert.WB.I25
open Family
def rows : List (List Move) := [
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
[.tailRot 1, .toLeft 0, .tailIn],
[.tailRot 3],
[.rot 0 1, .tailRot 1, .fromRight 0],
[.rot 0 6, .tailRot 3, .fromRight 0, .fromLeft 0, .tailIn]]
def s0 : Shape := ⟨[16, 1, 32, 4, 8, 64, 130, 1, 32, 4, 8, 64, 16, 1, 32, 4, 8, 64, 130], [([1, 32, 4, 8, 64, 16, 1, 32, 4, 8, 64, 130], [1, 32, 4, 8, 64, 16, 1, 32, 4, 8, 16, 130, 1, 64, 4, 8, 32, 2, 65, 0, 4, 8, 32, 16, 128, 0, 4, 8, 33, 2, 128, 0, 64, 8, 33, 4, 16, 0, 66, 8, 4, 0, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := [6]
def s1 : Shape := ⟨[2, 0, 8, 16, 128, 4, 2, 0, 8, 16, 128, 65, 2], [([0, 8, 16, 128, 4, 2, 0, 8, 16, 128, 65, 2], [0, 8, 16, 128, 4, 2, 0, 8, 16, 128, 4, 2, 65, 8, 16, 128, 32, 2, 65, 8, 16, 128, 4, 2, 65, 8, 16, 128, 32, 2, 65, 8, 16, 32, 4, 2, 128, 8, 16, 1, 64, 130, 0, 8, 16, 65, 32, 4, 0, 8, 16, 66, 4, 0, 1, 128, 16, 0, 8, 32, 2, 132, 16, 8, 65, 32, 4, 128, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32])], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := [5]
theorem ok : segCheckF S1 gpre gper 625 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 625 + rows.length = 650 := by decide
end Family.Cert.WB.I25
