import Cert.WA.Wall
namespace Family.Cert.WA.I25
open Family
def rows : List (List Move) := [
[.rot 0 6, .fromRight 0, .tailOut],
[.rot 0 6, .fromRight 0, .fromLeft 0],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .tailRot 8, .fromRight 0, .tailIn],
[.rot 0 6, .tailRot 3, .fromRight 0],
[.rot 0 6, .fromRight 0, .tailOut],
[.rot 0 6, .fromRight 0, .fromLeft 0],
[.rot 0 6, .tailRot 6, .tailIn],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .tailRot 8, .fromRight 0, .tailIn],
[.rot 0 6, .tailRot 3, .fromRight 0],
[.rot 0 6, .fromRight 0, .tailOut],
[.rot 0 6, .fromLeft 0],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .tailRot 8, .fromRight 0, .tailIn],
[.rot 0 6, .tailRot 3, .fromRight 0],
[.rot 0 6, .tailOut],
[.rot 0 6, .expand 0 0, .split 0 8 35 2],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .tailRot 8, .fromRight 0, .tailIn],
[.rot 0 6, .tailRot 3],
[.rot 0 6, .expand 0 0, .tailOut],
[.split 0 8 35 2],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .tailRot 8, .tailIn],
[.rot 0 6, .tailRot 3, .expand 0 0],
[.tailOut],
[.split 0 8 35 2],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6, .fromRight 0],
[.rot 0 6],
[.rot 0 6, .tailRot 8, .expand 0 0, .tailIn],
[.tailRot 3],
[.tailOut],
[.split 0 8 35 2],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6],
[.rot 0 6, .expand 0 0],
[.tailRot 8, .tailIn],
[.tailRot 3],
[.tailOut]]
def s0 : Shape := ⟨[18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34], [([0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34], [0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 17, 2, 36, 8, 1, 34, 8, 17, 2, 4, 0, 17, 36, 8, 1, 34, 8, 0, 18, 4])], [0, 17, 36, 8, 1, 34, 8, 0, 18, 4]⟩
def n0 : List Nat := [2]
def s1 : Shape := ⟨[8, 1, 34, 0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34, 0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34, 0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 9, 16, 34, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 4, 16, 1, 36, 8, 1, 34, 8, 16, 2, 4, 16, 1, 36, 8], [], [1, 34, 8, 16, 2, 4, 16, 1, 36, 8]⟩
def n1 : List Nat := []
theorem ok : segCheckF S1 gpre gper 1250 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 1250 + rows.length = 1300 := by decide
end Family.Cert.WA.I25
