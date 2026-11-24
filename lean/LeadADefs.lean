/-
The one-push game as a Lean definition: two heaps, the ruleset Sub(S1) with ONE push
to the ruleset Sub(S2), normal play.  Mirrors `lead_a2.py` (`solve2`) and `leads.solve_k` (k = 2).

The rules.
* A position is a pair of heap sizes (a, b), in mode 0 (before the push) or mode 1 (after it).
* In mode 0 a move is one of: remove s tokens from one heap (s in S1, s <= that heap), or PUSH.
  Pushing costs the turn and changes the mode to 1; the heap sizes stay the same.
* In mode 1 a move is: remove s tokens from one heap, s in S2.  There is no second push.
* Normal play: a player with no move loses.  `true` below means P (the player to move LOSES);
  `false` means N (the player to move wins).
* Only mode 0 has the push, so the mode-1 game is just the two-heap game Sub(S2).

How it is defined.  Both modes are computed by the same table builder, row by row in the first
heap, left to right in the second heap: a cell is P exactly when no move leads to a P position.
The only difference is the extra move "push" in mode 0, which leads to the mode-1 position with
the same heaps.  (`lead_a2.py` uses the Sprague-Grundy sequence g of S2 for the mode-1 outcome
(P iff g a = g b); here we do not, and `LeadACross` checks that the two agree.)

Every function is structurally recursive (explicit fuel), so `decide` can run it in the kernel.
-/

namespace LeadA

/-- `tget T a b`: the entry in row `a`, column `b` of a table (`false` outside the table). -/
def tget (T : List (List Bool)) (a b : Nat) : Bool := (T.getD a []).getD b false

/-- One cell of the P-table of the game with removal set `S` (plus, optionally, a push move).
`prev` holds the finished rows 0..a-1 (rows are lists indexed by the second heap), `cur` the
cells 0..b-1 of row `a`.  The position (a, b) is P iff
  (i) the push is not a winning move (`pushWins a b` = the mode-1 position after pushing is P;
      for a game with no push this is `fun _ _ => false`), and
  (ii) no removal move reaches a P position: no s in S with s <= a and (a-s, b) P,
       and no s in S with s <= b and (a, b-s) P. -/
def cellP (S : List Nat) (pushWins : Nat → Nat → Bool)
    (prev : List (List Bool)) (cur : List Bool) (a b : Nat) : Bool :=
  !(pushWins a b) &&
  !(S.any fun s => (decide (s ≤ a) && tget prev (a - s) b) || (decide (s ≤ b) && cur.getD (b - s) false))

/-- Row `a` of the P-table, columns 0..b-1 appended to `cur` (fuel = number of columns left). -/
def buildRow (S : List Nat) (pushWins : Nat → Nat → Bool) (prev : List (List Bool)) (a : Nat) :
    Nat → List Bool → List Bool
  | 0, cur => cur
  | fuel + 1, cur => buildRow S pushWins prev a fuel (cur ++ [cellP S pushWins prev cur a cur.length])

/-- Rows appended to `acc` (the finished rows 0..acc.length-1), `fuel` more rows, each of width
`N + 1` (heap sizes 0..N). -/
def buildTable (S : List Nat) (pushWins : Nat → Nat → Bool) (N : Nat) :
    Nat → List (List Bool) → List (List Bool)
  | 0, acc => acc
  | fuel + 1, acc =>
      buildTable S pushWins N fuel (acc ++ [buildRow S pushWins acc acc.length (N + 1) []])

/-- P-table (`true` = the player to move loses) of two heaps of sizes 0..N in MODE 1: the plain
two-heap game Sub(S2) with no push, normal play. -/
def mode1Table (S2 : List Nat) (N : Nat) : List (List Bool) :=
  buildTable S2 (fun _ _ => false) N (N + 1) []

/-- P-table of two heaps of sizes 0..N in MODE 0: the game Sub(S1) where, in addition to
removing s in S1 tokens from one heap, a player may push, which moves to the mode-1 game
Sub(S2) on the same heaps. -/
def mode0Table (S1 S2 : List Nat) (N : Nat) : List (List Bool) :=
  let T1 := mode1Table S2 N
  buildTable S1 (fun a b => tget T1 a b) N (N + 1) []

/-- Outcome of the position with heaps `a`, `b` in mode 0 (before the push), for removal set
`S1` before the push and `S2` after it.  `true` = P (player to move loses), `false` = N.
The table is built up to max a b, so this is the game's outcome, whichever heap is larger. -/
def outcome (S1 S2 : List Nat) (a b : Nat) : Bool :=
  tget (mode0Table S1 S2 (max a b)) a b

/-- Outcome of the position with heaps `a`, `b` in mode 1 (after the push): Sub(S2) alone. -/
def outcome1 (S2 : List Nat) (a b : Nat) : Bool :=
  tget (mode1Table S2 (max a b)) a b

/-- The Grundy value sequence of Sub(S) : g x = mex { g (x - s) : s in S, s <= x }, listed for
x = 0 .. (acc.length + fuel - 1) (`acc` = values already computed). -/
def mex (l : List Nat) : Nat := ((List.range (l.length + 1)).find? fun m => !l.contains m).getD 0

def sgBuild (S : List Nat) : Nat → List Nat → List Nat
  | 0, acc => acc
  | fuel + 1, acc =>
      sgBuild S fuel (acc ++ [mex (S.filterMap fun s =>
        if s ≤ acc.length then some (acc.getD (acc.length - s) 0) else none)])

/-- The first `n` Grundy values g 0, ..., g (n-1) of Sub(S) (one heap, normal play). -/
def sgList (S : List Nat) (n : Nat) : List Nat := sgBuild S n []

end LeadA
