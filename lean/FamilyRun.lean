/-
Generic infinite-run semantics of a letter-to-letter transducer `step : σ → Nat → σ × Nat`.
`stateAt step q u d` is the state before reading `u d` (starting from `q`), and `outAt step q u d`
is the output letter produced at position `d`.  Shared by `FamilyStack` and `FamilyBlock`.
-/
namespace Family

def stateAt {σ : Type} (step : σ → Nat → σ × Nat) (q : σ) (u : Nat → Nat) : Nat → σ
  | 0 => q
  | d + 1 => (step (stateAt step q u d) (u d)).1

def outAt {σ : Type} (step : σ → Nat → σ × Nat) (q : σ) (u : Nat → Nat) (d : Nat) : Nat :=
  (step (stateAt step q u d) (u d)).2

end Family
