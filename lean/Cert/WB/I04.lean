import Cert.WB.Wall
namespace Family.Cert.WB.I04
open Family
def rows : List (List Move) := [
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 1]]
def s0 : Shape := ⟨[0, 65, 8, 32, 130, 0, 16, 65, 32, 4, 130, 16, 8, 65, 32, 4, 130, 16, 8, 65, 32], [], [4, 130, 16, 8, 65, 32]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[130, 8, 32, 16, 0, 1, 130, 8, 64, 16, 0, 33, 130, 64, 4, 0, 32, 1, 130, 64, 8, 0, 32, 16, 130, 64, 8, 4, 32, 16, 130, 65, 8, 4, 32, 16, 130, 65, 8], [], [4, 32, 16, 130, 65, 8]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 100 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 100 + rows.length = 125 := by decide
end Family.Cert.WB.I04
