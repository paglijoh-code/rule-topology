import Cert.WA.Wall
namespace Family.Cert.WA.I02
open Family
def rows : List (List Move) := [
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
[],
[.tailRot 6, .tailIn],
[],
[],
[.tailRot 8, .tailIn]]
def s0 : Shape := ⟨[0, 9, 18, 32, 9, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36, 0, 1, 16, 4, 9, 18, 32, 8, 2, 32, 4], [], [1, 16, 4, 9, 18, 32, 8, 2, 32, 4]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[2, 4, 1, 18, 36, 8, 1, 34, 0, 9, 18, 36, 0, 17, 36, 0, 9, 18, 32, 8, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 2, 32, 8, 18, 36, 0, 17, 4], [], [0, 9, 2, 32, 8, 18, 36, 0, 17, 4]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 100 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 100 + rows.length = 150 := by decide
end Family.Cert.WA.I02
