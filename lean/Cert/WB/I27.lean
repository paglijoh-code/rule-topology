import Cert.WB.Wall
namespace Family.Cert.WB.I27
open Family
def rows : List (List Move) := [
[.rot 0 6, .tailRot 3, .fromRight 0, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.rot 0 9, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromRight 0, .tailIn],
[.rot 0 11, .tailRot 1, .fromLeft 0],
[.rot 0 6, .tailRot 3, .fromLeft 0],
[.tailRot 1, .toLeft 0],
[.tailRot 3, .tailIn],
[.rot 0 1, .tailRot 1, .expand 0 0],
[.tailRot 3, .split 0 13 12 2],
[.rot 0 3, .tailRot 1],
[.rot 0 6, .tailRot 3, .expand 0 0, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1, .tailIn],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn]]
def s0 : Shape := ⟨[0, 16, 32, 0, 8, 4, 0, 16, 32, 0, 130, 4, 0, 16, 32], [([0, 8, 4, 0, 16, 32, 0, 130, 4, 0, 16, 32], [0, 8, 4, 0, 16, 32, 0, 130, 4, 0, 16, 32, 0, 8, 4, 0, 16, 32, 0, 8, 4, 130, 16, 32, 0, 65, 4, 130, 16, 32, 0, 8, 4, 130, 16, 32, 0, 65, 4, 130, 16, 32, 65, 8, 4, 0, 16, 32, 130, 8, 4, 0, 16, 32, 130, 65, 4, 0, 16, 32, 130, 8, 4, 0, 16, 32, 130, 8, 4, 0, 16, 32, 130, 8, 4, 0, 16, 32, 2, 8, 65, 128, 16, 32, 4, 65, 0, 130, 16, 32, 65, 8, 0, 0, 4, 32, 130, 16, 0, 0, 8, 32, 16, 1, 64, 8, 4, 32, 16, 130, 64, 8, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8])], [4, 32, 16, 130, 65, 8]⟩
def n0 : List Nat := [2]
def s1 : Shape := ⟨[32, 65, 0, 16, 8, 0, 32, 65, 0, 4, 8, 0, 32, 65, 0, 16, 8, 0, 32, 65, 0, 4, 8, 0, 32, 65, 0, 16, 8, 0, 32, 65, 0, 16, 8, 4, 32, 65, 0, 130, 8, 4, 32, 65, 0, 16, 8, 4, 32, 65, 0, 130, 8, 4, 32, 65, 130, 16, 8, 0, 32, 65, 4, 16, 8, 0, 32, 65, 4, 130, 8, 0, 32, 65, 4, 16, 8, 0, 32, 65, 4, 16, 8, 0, 32, 65, 4, 16, 8, 0, 32, 65, 4, 16, 130, 0, 32, 65, 8, 130, 0, 4, 32, 65, 130, 16, 0, 8, 32, 65, 4, 16, 8, 0, 32, 65, 4, 130, 8, 0, 32, 65, 0, 16, 8, 4, 32, 65, 0, 16, 130, 4, 32, 65, 8, 16, 130, 4, 32, 65, 8, 16, 130, 4, 0, 65, 8, 32, 130, 4, 16, 65, 32, 2, 128, 16, 8, 65, 32, 4, 128, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32], [], [4, 130, 16, 8, 65, 32]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 675 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 675 + rows.length = 700 := by decide
end Family.Cert.WB.I27
