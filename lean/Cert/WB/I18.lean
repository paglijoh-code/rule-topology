import Cert.WB.Wall
namespace Family.Cert.WB.I18
open Family
def rows : List (List Move) := [
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1, .tailIn],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1, .tailIn],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1]]
def s0 : Shape := ⟨[0, 65, 32, 0, 130, 4, 0, 16, 32, 0, 130, 4, 0, 65, 32, 0, 130, 4, 0, 16, 32, 0, 130, 4, 0, 65, 32, 0, 130, 4, 0, 16, 32, 0, 130, 4, 0, 65, 32, 0, 130, 4, 0, 65, 32, 16, 130, 4, 0, 8, 32, 16, 130, 4, 0, 65, 32, 16, 130, 4, 0, 8, 32, 16, 130, 4, 8, 65, 32, 0, 130, 4, 16, 1, 32, 0, 130, 4, 16, 8, 64, 0, 130, 4, 32, 65, 0, 16, 2, 4, 8, 128, 0, 32, 66, 4, 128, 16, 1, 64, 2, 4, 128, 16, 8, 64, 32, 4, 128, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32], [], [4, 130, 16, 8, 65, 32]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[130, 64, 0, 4, 8, 1, 32, 64, 0, 4, 8, 1, 130, 64, 0, 4, 8, 1, 130, 64, 32, 4, 8, 1, 16, 64, 32, 4, 8, 1, 130, 64, 32, 4, 8, 1, 16, 64, 32, 4, 8, 16, 130, 64, 1, 4, 8, 32, 130, 65, 0, 4, 8, 32, 16, 65, 0, 4, 8, 32, 130, 65, 0, 4, 8, 32, 130, 65, 0, 4, 8, 32, 130, 65, 0, 4, 8, 32, 130, 16, 0, 4, 8, 65, 16, 0, 32, 4, 8, 16, 130, 0, 1, 64, 8, 32, 4, 1, 0, 130, 8, 4, 16, 1, 130, 64, 8, 4, 32, 2, 128, 64, 8, 4, 32, 16, 128, 65, 8, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8], [], [4, 32, 16, 130, 65, 8]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 450 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 450 + rows.length = 475 := by decide
end Family.Cert.WB.I18
