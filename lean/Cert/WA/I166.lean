import Cert.WA.Wall
namespace Family.Cert.WA.I166
open Family
def rows : List (List Move) := [
[.rot 0 6, .fromRight 0, .fromLeft 0],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .tailRot 8, .fromRight 0, .tailIn],
[.rot 0 6, .tailRot 3, .fromRight 0],
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
[.rot 0 6, .fromRight 0, .fromLeft 0],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .tailRot 8, .fromRight 0, .tailIn],
[.rot 0 6, .tailRot 3],
[.rot 0 6, .fromRight 0, .tailOut],
[.rot 0 6, .fromRight 0, .fromLeft 0],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .fromRight 0],
[.rot 0 6, .tailRot 8, .tailIn],
[.rot 0 6, .tailRot 3, .fromRight 0],
[.rot 0 6, .fromRight 0, .tailOut],
[.rot 0 6, .fromRight 0, .fromLeft 0],
[.rot 0 6, .tailRot 6, .fromRight 0, .tailIn],
[.rot 0 6, .fromRight 0],
[.rot 0 6],
[.rot 0 6, .tailRot 8, .fromRight 0, .tailIn],
[.rot 0 6, .tailRot 3, .fromRight 0],
[.rot 0 6, .fromRight 0, .tailOut],
[.rot 0 6, .fromRight 0, .fromLeft 0]]
def s0 : Shape := ⟨[8, 1, 34, 0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34], [([0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34], [0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 36, 1, 18, 36, 8, 1, 18, 0, 9, 18, 36, 0, 9, 32, 4, 9, 18, 32, 4, 16, 34, 4, 9, 16, 2, 8, 17, 34, 4, 8, 1, 36, 8, 17, 2, 4, 16, 2, 36, 8, 1, 34, 8, 17, 2, 4, 16, 1, 36, 8, 1, 34, 8, 16, 2, 4, 16, 1, 36, 8])], [1, 34, 8, 16, 2, 4, 16, 1, 36, 8]⟩
def n0 : List Nat := [7]
def s1 : Shape := ⟨[2, 4, 1, 18, 36, 8, 1, 34], [([0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34], [0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 9, 16, 34, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 32, 2, 8, 17, 2, 4, 17, 32, 4, 8, 32, 2, 8, 17])], [2, 4, 17, 32, 4, 8, 32, 2, 8, 17]⟩
def n1 : List Nat := [8]
theorem ok : segCheckF S1 gpre gper 8300 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 8300 + rows.length = 8350 := by decide
end Family.Cert.WA.I166
