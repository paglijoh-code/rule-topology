import FamilyFast
namespace Family.Cert.WA
def S1 : List Nat := [1, 2, 5, 6]
def gpre : List Nat := []
def gper : List Nat := [0, 1, 2, 3, 4]
def start : List Family.Move := [.tailOut, .tailOut]
theorem hS : ∀ s ∈ S1, 0 < s := by decide
theorem hp : 0 < gper.length := by decide
end Family.Cert.WA
