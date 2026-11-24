import Cert.WA.Wall
namespace Family.Cert.WA.I108
open Family
def rows : List (List Move) := [
[.rot 0 6, .tailRot 3, .fromRight 0],
[.rot 0 6, .fromRight 0, .tailOut, .split 1 49 35 2],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromLeft 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 6, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromLeft 1],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 8, .fromRight 0, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6, .tailRot 3, .fromRight 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromRight 1, .tailOut],
[.rot 0 6, .rot 1 6, .fromLeft 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 6, .fromRight 0, .fromRight 1, .fromLeft 1, .tailIn],
[.rot 0 6, .rot 1 6, .fromRight 0],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 8, .fromRight 0, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6, .tailRot 3, .fromRight 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .fromRight 1, .tailOut],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromLeft 0, .fromRight 1, .fromLeft 1],
[.rot 0 6, .rot 1 6, .tailRot 6, .fromRight 0, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6, .fromRight 0],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 8, .fromRight 0, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6, .tailRot 3, .fromRight 1],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromRight 1, .fromLeft 1, .tailOut],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromLeft 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 6, .fromRight 0, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6, .fromRight 0],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 8, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6, .tailRot 3, .fromRight 0, .fromRight 1, .fromLeft 1],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromRight 1, .tailOut],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromLeft 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 6, .fromRight 0, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6, .fromRight 0],
[.rot 0 6, .rot 1 6, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 8, .fromRight 0, .fromRight 1, .fromLeft 1, .tailIn],
[.rot 0 6, .rot 1 6, .tailRot 3, .fromRight 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromRight 1, .tailOut],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromLeft 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 6, .fromRight 0, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromRight 1, .fromLeft 1],
[.rot 0 6, .rot 1 6, .tailRot 8, .fromRight 0, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6, .tailRot 3, .fromRight 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromRight 1, .tailOut],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromLeft 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 6, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromLeft 1],
[.rot 0 6, .rot 1 6, .fromRight 0, .fromRight 1],
[.rot 0 6, .rot 1 6, .tailRot 8, .fromRight 0, .fromRight 1, .tailIn],
[.rot 0 6, .rot 1 6, .tailRot 3, .fromRight 0, .fromRight 1]]
def s0 : Shape := ⟨[4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34], [([0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34], [0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 17, 2, 36, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36, 0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 2, 32, 8, 18, 36, 0, 17, 4])], [0, 9, 2, 32, 8, 18, 36, 0, 17, 4]⟩
def n0 : List Nat := [3]
def s1 : Shape := ⟨[18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34], [([0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 8, 17, 34, 4, 8, 2, 36, 8, 17, 2, 4, 1, 18, 36, 8, 1, 34], [0, 9, 18, 36, 0, 17, 32, 4, 9, 18, 32, 8, 16, 34, 4, 9, 16, 4, 9, 16, 34, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36]), ([0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 36, 0, 17, 36, 8, 1, 18, 32, 8, 18, 36], [0, 9, 16, 4, 9, 18, 32, 4, 8, 34, 4, 9, 16, 2, 4, 17, 34, 4, 8, 1, 34, 8, 17, 2, 4, 0, 17, 36, 8, 1, 34, 8, 0, 18, 4])], [0, 17, 36, 8, 1, 34, 8, 0, 18, 4]⟩
def n1 : List Nat := [2, 3]
theorem ok : segCheckF S1 gpre gper 5400 s0 n0 rows s1 n1 = true := by decide +kernel
theorem len : 5400 + rows.length = 5450 := by decide
end Family.Cert.WA.I108
