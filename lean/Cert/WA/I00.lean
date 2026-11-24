import Cert.WA.Wall
namespace Family.Cert.WA.I00
open Family
def rows : List (List Move) := [
[.tailRot 8],
[],
[.tailRot 3, .tailIn],
[],
[.tailOut],
[],
[.tailRot 6, .tailIn],
[],
[],
[.tailRot 8],
[.tailRot 3],
[.tailOut],
[],
[.tailRot 6, .tailIn],
[],
[],
[.tailRot 8, .tailIn],
[.tailRot 3],
[.tailOut],
[],
[.tailRot 6, .tailIn],
[],
[],
[.tailRot 8, .tailIn],
[.tailRot 3],
[.tailOut],
[],
[.tailRot 6, .tailIn],
[],
[],
[.tailRot 8, .tailIn],
[.tailRot 3],
[.tailOut],
[],
[.tailRot 6, .tailIn],
[],
[],
[.tailRot 8, .tailIn],
[.tailRot 3],
[.tailOut],
[],
[.tailRot 6, .tailIn],
[],
[],
[.tailRot 8, .tailIn],
[.tailRot 3],
[.tailOut],
[],
[.tailRot 6, .tailIn],
[]]
def s0 : Shape := ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [], [0, 0, 0, 0, 0]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[16, 34, 4, 9, 16, 2, 8, 17, 34, 4, 8, 1, 36, 8, 17, 2, 36, 0, 18, 36, 8, 1, 18, 32, 9, 18, 36, 0, 9, 16, 4, 9, 18, 32, 0, 8, 34, 4, 9, 16, 4, 1, 16, 34], [], [0, 8, 34, 4, 9, 16, 4, 1, 16, 34]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 0 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 0 + rows.length = 50 := by decide
end Family.Cert.WA.I00
