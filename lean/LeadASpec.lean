/-
Relational specification of the H.A game (two heaps, one push, Sub(S1) -> Sub(S2)), independent of
the table builder in `LeadADefs`, and the proof that the builder computes it.

The spec.
* `IsP1 S a b`: the mode-1 position (heaps a, b, only removals from S) is P (the player to move
  loses) iff NO removal move reaches a P position: for every s in S, 0 < s, s <= a, the position
  (a - s, b) is not P, and the same for the second heap.
* `IsP0 S1 S2 a b`: the mode-0 position is P iff the push (to the mode-1 position with the same
  heaps) does not reach a P position, i.e. `IsP1 S2 a b` fails, and no removal move from S1
  reaches a P mode-0 position.
Both are defined by well-founded recursion on a + b (each move strictly decreases it), so they are
the unique solutions of these "P iff no move leads to P" equations (`Eqn`, `Eqn.unique`).
Removals of s = 0 are ignored (`0 < s` guard): a 0-removal is not a move; the table builder
ignores them too, and the checker requires every s > 0 anyway.

Main results: `outcome_iff : outcome S1 S2 a b = true ↔ IsP0 S1 S2 a b` and
`outcome1_iff`, for all S1 S2 a b.
-/
import LeadADefs
namespace LeadA

/-- Mode-1 game Sub(S): P-positions, "P iff no move leads to a P position". -/
def IsP1 (S : List Nat) : Nat → Nat → Prop
  | a, b => (∀ s ∈ S, 0 < s → s ≤ a → ¬ IsP1 S (a - s) b) ∧
            (∀ s ∈ S, 0 < s → s ≤ b → ¬ IsP1 S a (b - s))
termination_by a b => a + b

/-- Mode-0 game: the extra move is the push, which reaches the mode-1 position with the same
heaps; so the push is not winning iff that position is not P. -/
def IsP0 (S1 S2 : List Nat) : Nat → Nat → Prop
  | a, b => ¬ IsP1 S2 a b ∧ (∀ s ∈ S1, 0 < s → s ≤ a → ¬ IsP0 S1 S2 (a - s) b) ∧
            (∀ s ∈ S1, 0 < s → s ≤ b → ¬ IsP0 S1 S2 a (b - s))
termination_by a b => a + b

/-- `Q` solves the game equation with removal set `S` and push predicate `W` (`W a b`: the push
from (a, b) reaches a P position): Q a b iff the push is not winning and no removal leads to Q. -/
def Eqn (S : List Nat) (W Q : Nat → Nat → Prop) : Prop :=
  ∀ a b, Q a b ↔ ¬ W a b ∧ (∀ s ∈ S, 0 < s → s ≤ a → ¬ Q (a - s) b) ∧
    (∀ s ∈ S, 0 < s → s ≤ b → ¬ Q a (b - s))

theorem tget_ge (T : List (List Bool)) (a b : Nat) (h : T.length ≤ a) : tget T a b = false := by
  simp [tget, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem cellP_iff (S : List Nat) (pw : Nat → Nat → Bool) (W Q : Nat → Nat → Prop)
    (hE : Eqn S W Q) (prev : List (List Bool)) (cur : List Bool) (a b : Nat)
    (hpw : pw a b = true ↔ W a b) (hprev : prev.length = a) (hcur : cur.length = b)
    (h1 : ∀ i < a, tget prev i b = true ↔ Q i b)
    (h2 : ∀ j < b, cur.getD j false = true ↔ Q a j) :
    cellP S pw prev cur a b = true ↔ Q a b := by
  rw [hE a b]
  unfold cellP
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true']
  rw [← Bool.not_eq_true (S.any _), List.any_eq_true]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  have hT0 : tget prev a b = false := tget_ge _ _ _ (by omega)
  have hC0 : cur.getD b false = false := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show cur.length ≤ b by omega)]
  have e : pw a b = false ↔ ¬ W a b := by rw [← hpw]; simp
  rw [e]
  apply and_congr_right; intro _
  constructor
  · intro h
    refine ⟨fun s hs hs0 hsa hq => h ⟨s, hs, Or.inl ⟨hsa, (h1 _ (by omega)).2 hq⟩⟩,
      fun s hs hs0 hsb hq => h ⟨s, hs, Or.inr ⟨hsb, (h2 _ (by omega)).2 hq⟩⟩⟩
  · rintro ⟨hA, hB⟩ ⟨s, hs, hcase⟩
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · simp [hT0, List.getD_eq_getElem?_getD] at hcase; simp [List.getD_eq_getElem?_getD] at hC0; simp [hC0] at hcase
    · rcases hcase with ⟨hsa, ht⟩ | ⟨hsb, hc⟩
      · exact hA s hs hs0 hsa ((h1 _ (by omega)).1 ht)
      · exact hB s hs hs0 hsb ((h2 _ (by omega)).1 hc)

theorem buildRow_spec (S : List Nat) (pw : Nat → Nat → Bool) (W Q : Nat → Nat → Prop)
    (hE : Eqn S W Q) (prev : List (List Bool)) (a N : Nat)
    (hpw : ∀ b, b ≤ N → (pw a b = true ↔ W a b)) (hprev : prev.length = a)
    (h1 : ∀ i < a, ∀ b, b ≤ N → (tget prev i b = true ↔ Q i b)) :
    ∀ fuel cur, cur.length + fuel ≤ N + 1 → (∀ j < cur.length, cur.getD j false = true ↔ Q a j) →
      (buildRow S pw prev a fuel cur).length = cur.length + fuel ∧
      ∀ j < cur.length + fuel, ((buildRow S pw prev a fuel cur).getD j false = true ↔ Q a j) := by
  intro fuel
  induction fuel with
  | zero => intro cur _ h; exact ⟨by simp [buildRow], by simpa [buildRow] using h⟩
  | succ f ih =>
    intro cur hlen hcur
    have hc := cellP_iff S pw W Q hE prev cur a cur.length (hpw _ (by omega)) hprev rfl
      (fun i hi => h1 i hi _ (by omega)) hcur
    have := ih (cur ++ [cellP S pw prev cur a cur.length]) (by simp; omega) (by
      intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hjl : j < cur.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]; exact hcur j hjl
      · have : j = cur.length := by omega
        subst this
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]; simpa using hc)
    rw [buildRow]
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem buildTable_spec (S : List Nat) (pw : Nat → Nat → Bool) (W Q : Nat → Nat → Prop)
    (hE : Eqn S W Q) (N : Nat) (hpw : ∀ a b, a ≤ N → b ≤ N → (pw a b = true ↔ W a b)) :
    ∀ fuel acc, acc.length + fuel ≤ N + 1 →
      (∀ i < acc.length, ∀ b, b ≤ N → (tget acc i b = true ↔ Q i b)) →
      (buildTable S pw N fuel acc).length = acc.length + fuel ∧
      ∀ i < acc.length + fuel, ∀ b, b ≤ N → (tget (buildTable S pw N fuel acc) i b = true ↔ Q i b) := by
  intro fuel
  induction fuel with
  | zero => intro acc _ h; exact ⟨by simp [buildTable], by simpa [buildTable] using h⟩
  | succ f ih =>
    intro acc hlen hacc
    have hr := buildRow_spec S pw W Q hE acc acc.length N (fun b hb => hpw _ b (by omega) hb) rfl hacc
      (N + 1) [] (by simp) (by simp)
    simp only [List.length_nil, Nat.zero_add] at hr
    obtain ⟨hrl, hrc⟩ := hr
    have := ih (acc ++ [buildRow S pw acc acc.length (N + 1) []]) (by simp; omega) (by
      intro i hi b hb
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hil : i < acc.length
      · have : tget (acc ++ [buildRow S pw acc acc.length (N + 1) []]) i b = tget acc i b := by
          simp [tget, List.getD_eq_getElem?_getD, List.getElem?_append_left hil]
        rw [this]; exact hacc i hil b hb
      · have : i = acc.length := by omega
        subst this
        have : tget (acc ++ [buildRow S pw acc acc.length (N + 1) []]) acc.length b
            = (buildRow S pw acc acc.length (N + 1) []).getD b false := by
          simp [tget, List.getD_eq_getElem?_getD]
        rw [this]; exact hrc b (by omega))
    rw [buildTable]
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem table_spec (S : List Nat) (pw : Nat → Nat → Bool) (W Q : Nat → Nat → Prop)
    (hE : Eqn S W Q) (N : Nat) (hpw : ∀ a b, a ≤ N → b ≤ N → (pw a b = true ↔ W a b))
    (a b : Nat) (ha : a ≤ N) (hb : b ≤ N) :
    tget (buildTable S pw N (N + 1) []) a b = true ↔ Q a b :=
  (buildTable_spec S pw W Q hE N hpw (N + 1) [] (by simp) (by simp)).2 a (by simp; omega) b hb


theorem IsP1_eqn (S : List Nat) : Eqn S (fun _ _ => False) (IsP1 S) := by
  intro a b; rw [IsP1]; simp

theorem IsP0_eqn (S1 S2 : List Nat) : Eqn S1 (IsP1 S2) (IsP0 S1 S2) := by
  intro a b; rw [IsP0]

/-- The game equation has at most one solution. -/
theorem Eqn.unique {S : List Nat} {W Q Q' : Nat → Nat → Prop} (h : Eqn S W Q) (h' : Eqn S W Q') :
    ∀ a b, Q a b ↔ Q' a b := by
  intro a b
  induction hn : a + b using Nat.strongRecOn generalizing a b with
  | _ n ih =>
    rw [h a b, h' a b]
    refine and_congr_right fun _ => and_congr ?_ ?_
    · refine forall_congr' fun s => forall_congr' fun hs => forall_congr' fun hs0 =>
        forall_congr' fun hsa => not_congr ?_
      exact ih _ (by omega) _ _ rfl
    · refine forall_congr' fun s => forall_congr' fun hs => forall_congr' fun hs0 =>
        forall_congr' fun hsb => not_congr ?_
      exact ih _ (by omega) _ _ rfl

/-- If the push predicate is symmetric, so is the solution. -/
theorem Eqn.symm {S : List Nat} {W Q : Nat → Nat → Prop} (h : Eqn S W Q)
    (hW : ∀ a b, W a b ↔ W b a) : ∀ a b, Q a b ↔ Q b a := by
  have h' : Eqn S W (fun a b => Q b a) := by
    intro a b
    show Q b a ↔ _
    rw [h b a, hW]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
  exact fun a b => h.unique h' a b

theorem IsP1_symm (S : List Nat) (a b : Nat) : IsP1 S a b ↔ IsP1 S b a :=
  (IsP1_eqn S).symm (fun _ _ => Iff.rfl) a b

theorem IsP0_symm (S1 S2 : List Nat) (a b : Nat) : IsP0 S1 S2 a b ↔ IsP0 S1 S2 b a :=
  (IsP0_eqn S1 S2).symm (fun a b => IsP1_symm S2 a b) a b

/-- The mode-1 table builder computes the spec. -/
theorem outcome1_iff (S2 : List Nat) (a b : Nat) : outcome1 S2 a b = true ↔ IsP1 S2 a b := by
  unfold outcome1 mode1Table
  exact table_spec S2 _ _ _ (IsP1_eqn S2) (max a b) (by intro a b _ _; simp) a b
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The mode-0 table builder (hence `outcome`) computes the spec, for every S1, S2, a, b. -/
theorem outcome_iff (S1 S2 : List Nat) (a b : Nat) : outcome S1 S2 a b = true ↔ IsP0 S1 S2 a b := by
  unfold outcome mode0Table
  refine table_spec S1 _ (IsP1 S2) _ (IsP0_eqn S1 S2) (max a b) ?_ a b
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  intro a' b' ha hb
  unfold mode1Table
  exact table_spec S2 _ _ _ (IsP1_eqn S2) (max a b) (by intro a b _ _; simp) a' b' ha hb

theorem outcome_symm (S1 S2 : List Nat) (a b : Nat) : outcome S1 S2 a b = outcome S1 S2 b a := by
  have := IsP0_symm S1 S2 a b
  rw [← outcome_iff, ← outcome_iff] at this
  simpa using this

end LeadA
