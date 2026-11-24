import Cert.WA.Wall
namespace Family.Cert.WA.I23
open Family
def rows : List (List Move) := [
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
[.tailRot 6, .tailIn, .split 0 52 35 2],
[.rot 0 6],
[.rot 0 6, .expand 0 0],
[.tailRot 8, .tailIn],
[.tailRot 3],
[.tailOut],
[.split 0 47 35 2],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6],
[.rot 0 6, .expand 0 0],
[.tailRot 8, .tailIn],
[.tailRot 3],
[.tailOut, .split 0 42 35 2],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6],
[.rot 0 6, .expand 0 0],
[.tailRot 8, .tailIn],
[.tailRot 3, .split 0 37 35 2],
[.rot 0 6, .fromRight 0, .tailOut],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6],
[.rot 0 6, .expand 0 0],
[.tailRot 8, .tailIn, .split 0 32 35 2],
[.rot 0 6, .tailRot 3, .fromRight 0],
[.rot 0 6, .fromRight 0, .tailOut],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6],
[.rot 0 6, .expand 0 0, .split 0 27 35 2],
[.rot 0 6, .tailRot 8, .fromRight 0, .tailIn]]
def s0 : Shape := ⟨[8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34, 0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34, 0, 9, 18, 36, 0, 17, 36, 0, 9, 18, 32, 8, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36, 0, 1, 16, 4, 9, 18, 32, 8, 2, 32, 4], [], [1, 16, 4, 9, 18, 32, 8, 2, 32, 4]⟩
def n0 : List Nat := []
def s1 : Shape := ⟨[4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 17, 2, 36, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36], [([0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36], [0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 2, 32, 8, 18, 36, 0, 17, 4])], [0, 9, 2, 32, 8, 18, 36, 0, 17, 4]⟩
def n1 : List Nat := [2]
theorem ok : segCheckF S1 gpre gper 1150 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 1150 + rows.length = 1200 := by decide
end Family.Cert.WA.I23
