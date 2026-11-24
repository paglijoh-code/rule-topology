import Cert.WB.Wall
namespace Family.Cert.WB.I69
open Family
def rows : List (List Move) := [
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
[.rot 0 6, .tailRot 3, .fromLeft 0, .tailIn],
[.tailRot 1],
[.tailRot 3]]
def s0 : Shape := ⟨[130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 65, 0, 130, 16, 32, 65, 8, 0, 4, 16, 32, 130, 8, 4, 0, 16, 32, 130, 65, 4, 0, 16, 32, 130, 8, 4, 0, 16, 32, 130, 8, 65, 0, 16, 32, 4, 8, 65, 130, 16, 32, 4, 8, 65, 130, 16, 32, 4, 65, 0, 130, 16, 32, 65, 8, 0, 4, 16, 32, 130, 8, 4, 0, 16, 32, 130, 65, 4], [([0, 16, 32, 130, 8, 4, 0, 16, 32, 130, 65, 4], [0, 16, 32, 130, 8, 4, 0, 16, 32, 130, 65, 4, 0, 16, 32, 130, 8, 4, 0, 16, 32, 0, 1, 64, 130, 16, 32, 1, 64, 8, 0, 4, 32, 2, 128, 8, 0, 4, 32, 16, 128, 65, 0, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := [13]
def s1 : Shape := ⟨[32, 65, 8, 130, 0, 4, 32, 65, 8, 16, 0, 4, 32, 65, 8, 16, 130, 4, 32, 65, 8, 16, 130, 4, 32, 65, 8, 16, 130, 4, 32, 65, 8, 130, 0, 4, 32, 65, 130, 16, 0, 8, 32, 65, 4, 16, 8, 0, 32, 65, 4, 130, 8], [([0, 32, 65, 4, 16, 8, 0, 32, 65, 4, 130, 8], [0, 32, 65, 4, 16, 8, 0, 32, 65, 4, 130, 8, 0, 32, 65, 4, 16, 8, 0, 32, 65, 0, 2, 128, 4, 32, 65, 2, 128, 16, 0, 8, 65, 4, 0, 16, 0, 8, 65, 32, 0, 130, 0, 8, 65, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32])], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := [15]
theorem ok : segCheckF S1 gpre gper 1725 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 1725 + rows.length = 1750 := by decide
end Family.Cert.WB.I69
