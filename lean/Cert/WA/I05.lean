import Cert.WA.Wall
namespace Family.Cert.WA.I05
open Family
def rows : List (List Move) := [
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
[]]
def s0 : Shape := ⟨[0, 9, 18, 32, 9, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 4, 16, 1, 36, 8, 1, 34, 8, 16, 2, 4, 16, 1, 36, 8], [], [1, 34, 8, 16, 2, 4, 16, 1, 36, 8]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[2, 4, 1, 18, 36, 8, 1, 34, 0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 17, 2, 36, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 32, 2, 8, 17, 2, 4, 17, 32, 4, 8, 32, 2, 8, 17], [], [2, 4, 17, 32, 4, 8, 32, 2, 8, 17]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 250 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 250 + rows.length = 300 := by decide
end Family.Cert.WA.I05
