import Cert.WB.Wall
namespace Family.Cert.WB.I71
open Family
def rows : List (List Move) := [
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
[.rot 0 11, .tailRot 1, .fromRight 0, .fromLeft 0],
[.tailRot 3, .tailIn],
[.rot 0 6, .tailRot 1, .fromRight 0],
[.tailRot 3],
[.tailRot 1]]
def s0 : Shape := ⟨[130, 16, 32, 4, 8, 65, 130, 16, 4, 0, 8, 65, 130, 4, 32, 0, 16, 65, 130, 8, 32, 16, 0, 65, 130, 8, 4, 16, 0, 65, 130, 8, 32, 16], [([0, 65, 130, 8, 4, 16, 0, 65, 130, 8, 32, 16], [0, 65, 130, 8, 4, 16, 0, 65, 130, 8, 32, 16, 0, 65, 130, 0, 4, 0, 8, 65, 130, 4, 0, 32, 0, 16, 130, 8, 1, 32, 0, 16, 130, 65, 0, 4, 0, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := [17]
def s1 : Shape := ⟨[130, 0, 32, 4, 8, 65, 16, 0, 32, 4, 8, 65, 130], [([0, 32, 4, 8, 65, 16, 0, 32, 4, 8, 65, 130], [0, 32, 4, 8, 65, 16, 0, 32, 4, 8, 16, 130, 0, 65, 4, 8, 32, 0, 1, 64, 132, 8, 0, 16, 2, 128, 4, 8, 0, 32, 2, 128, 65, 8, 0, 32, 16, 128, 65, 8, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n1 : List Nat := [19]
theorem ok : segCheckF S1 gpre gper 1775 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 1775 + rows.length = 1795 := by decide
end Family.Cert.WB.I71
