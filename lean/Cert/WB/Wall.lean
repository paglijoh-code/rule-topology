import FamilyFast
namespace Family.Cert.WB
def S1 : List Nat := [1, 2, 3, 4, 7, 8]
def gpre : List Nat := []
def gper : List Nat := [0, 1, 2, 3, 2, 4]
def start : List Family.Move := [.tailOut, .tailOut]
theorem hS : ∀ s ∈ S1, 0 < s := by decide
theorem hp : 0 < gper.length := by decide
end Family.Cert.WB
