import Cert.WB.Wall
namespace Family.Cert.WB.I24
open Family
def rows : List (List Move) := [
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
[.rot 0 11, .tailRot 1, .fromRight 0, .fromLeft 0],
[.tailRot 3, .tailIn],
[.rot 0 6, .tailRot 1, .fromRight 0],
[.tailRot 3],
[.tailRot 1],
[.rot 0 6, .tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.rot 0 6, .tailRot 1, .fromRight 0],
[.tailRot 3],
[.tailRot 1, .tailIn]]
def s0 : Shape := ⟨[32, 65, 8, 16, 130, 4, 32, 8, 0, 16, 130, 4, 8, 65, 0, 32, 130, 4, 16, 65, 32, 0, 130, 4, 16, 8, 32, 0, 130, 4, 16, 65, 32], [([0, 130, 4, 16, 8, 32, 0, 130, 4, 16, 65, 32], [0, 130, 4, 16, 8, 32, 0, 130, 4, 16, 65, 32, 0, 130, 4, 0, 8, 0, 16, 130, 4, 8, 1, 64, 0, 32, 4, 16, 2, 64, 0, 33, 4, 130, 0, 8, 1, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32])], [4, 130, 16, 8, 65, 32]⟩
def n0 : List Nat := [5]
def s1 : Shape := ⟨[16, 1, 32, 4, 8, 64, 130, 1, 32, 4, 8, 64, 16, 1, 32, 4, 8, 64, 130], [([1, 32, 4, 8, 64, 16, 1, 32, 4, 8, 64, 130], [1, 32, 4, 8, 64, 16, 1, 32, 4, 8, 16, 130, 1, 64, 4, 8, 32, 2, 65, 0, 4, 8, 32, 16, 128, 0, 4, 8, 33, 2, 128, 0, 64, 8, 33, 4, 16, 0, 66, 8, 4, 0, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n1 : List Nat := [6]
theorem ok : segCheckF S1 gpre gper 600 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 600 + rows.length = 625 := by decide
end Family.Cert.WB.I24
