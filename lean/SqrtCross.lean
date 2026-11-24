import SqrtModel
namespace SqrtM
open LeadA

/-- cross-check: the model equals the table builder `mode0Table` (hence `outcome`) on heaps <= N -/
def crossOK (N : Nat) : Bool :=
  let T := mode0Table [1, 2, 5, 6] [1, 2, 3, 4] N
  (List.range (N + 1)).all fun a => (List.range (N + 1)).all fun b => tget T a b == model a b

theorem cross40 : crossOK 40 = true := by decide +kernel

end SqrtM
