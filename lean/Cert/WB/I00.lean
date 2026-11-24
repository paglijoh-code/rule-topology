import Cert.WB.Wall
namespace Family.Cert.WB.I00
open Family
def rows : List (List Move) := [
[.tailRot 3],
[.tailRot 1],
[.tailOut],
[],
[.tailRot 1],
[.tailOut],
[],
[],
[],
[.tailRot 4, .tailIn],
[.tailRot 3],
[.tailRot 1],
[.tailRot 3, .tailIn],
[.tailRot 4],
[.tailRot 3],
[],
[],
[],
[.tailRot 5, .tailIn],
[],
[],
[],
[.tailRot 3, .tailIn],
[.tailRot 4],
[.tailRot 3, .tailIn]]
def s0 : Shape := ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [], [0, 0, 0, 0, 0, 0]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[8, 4, 128, 16, 66, 32, 0, 4, 128, 16, 8, 33, 4, 0, 130, 16, 8, 65, 4, 0, 130, 32, 8, 65, 16, 0, 130, 32, 8, 65, 16, 4, 130, 32, 8, 65, 16], [], [4, 130, 32, 8, 65, 16]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 0 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 0 + rows.length = 25 := by decide
end Family.Cert.WB.I00
