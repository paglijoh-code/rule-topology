import Cert.WB.Wall
namespace Family.Cert.WB.I45
open Family
def rows : List (List Move) := [
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
[.tailRot 1, .tailIn],
[.rot 0 6, .tailRot 3, .fromLeft 0],
[.rot 0 4, .tailRot 1, .fromRight 0],
[.tailRot 3, .tailIn],
[.rot 0 6, .tailRot 1],
[.tailRot 3],
[.rot 0 9, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromRight 0, .tailIn],
[.rot 0 11, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromRight 0, .fromLeft 0]]
def s0 : Shape := ⟨[128, 16, 32, 66, 8, 4, 0, 16, 32, 130, 8, 4, 0, 16, 32, 130, 65, 4], [([0, 16, 32, 130, 8, 4, 0, 16, 32, 130, 65, 4], [0, 16, 32, 130, 8, 4, 0, 16, 32, 130, 65, 4, 0, 16, 32, 130, 8, 4, 0, 16, 32, 0, 1, 64, 130, 16, 32, 1, 64, 8, 0, 4, 32, 2, 128, 8, 0, 4, 32, 16, 128, 65, 0, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := [12]
def s1 : Shape := ⟨[32, 65, 8, 4, 0, 0, 32, 65, 8, 16], [([0, 0, 32, 65, 8, 4, 0, 0, 32, 65, 8, 16], [0, 0, 32, 65, 8, 4, 0, 0, 32, 65, 8, 16, 0, 0, 32, 65, 8, 16, 0, 4, 32, 65, 8, 130, 0, 4, 32, 65, 8, 16, 0, 4, 32, 65, 8, 2, 128, 4, 32, 65, 2, 128, 16, 0, 8, 65, 4, 0, 16, 0, 8, 65, 32, 0, 130, 0, 8, 65, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32])], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := [12]
theorem ok : segCheckF S1 gpre gper 1125 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 1125 + rows.length = 1150 := by decide
end Family.Cert.WB.I45
