import FamilyRun

/-!
Generic theory of letter-to-letter transducers on eventually periodic words (no game content).

* `run`, `cat`, `per`, `rep`: finite runs, "w followed by r", "z^ω", "y^n".
* `Shape`/`decode`: symbolic words `x0 y1^n1 x1 ... yj^nj xj z^ω`.
* `run_rep` (block lemma), `tail_out` (tail lemma), `outAt_cat` (finite/infinite run link).
* `sstep`/`sstep_sound`: symbolic step (the caller drops the first letter).
* `Move`/`applyMove`/`applyMove_sound`: decode-preserving normalisation moves.

Counter convention for moves: see `CEdit` and `applyMove_sound`.
-/
namespace Family

variable {σ : Type} (step : σ → Nat → σ × Nat)

/-! ### Words -/

/-- `cat w r` is the word `w` followed by the infinite word `r`. -/
def cat : List Nat → (Nat → Nat) → Nat → Nat
  | [], r, d => r d
  | a :: _, _, 0 => a
  | _ :: w, r, d + 1 => cat w r d

/-- `rep y n = y ++ ... ++ y` (n copies). -/
def rep (y : List Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => y ++ rep y n

/-- `per z = z z z ...` (total: `0` everywhere if `z = []`). -/
def per (z : List Nat) (d : Nat) : Nat := z.getD (d % z.length) 0

@[simp] theorem cat_nil (r : Nat → Nat) : cat [] r = r := rfl

theorem cat_lt {w : List Nat} {r : Nat → Nat} {d : Nat} (h : d < w.length) :
    cat w r d = w.getD d 0 := by
  induction w generalizing d with
  | nil => simp at h
  | cons a w ih => cases d <;> simp_all [cat]

theorem cat_ge {w : List Nat} {r : Nat → Nat} {d : Nat} (h : w.length ≤ d) :
    cat w r d = r (d - w.length) := by
  induction w generalizing d with
  | nil => simp [cat]
  | cons a w ih =>
    cases d with
    | zero => simp at h
    | succ d => simp only [cat, List.length_cons, Nat.add_sub_add_right]; exact ih (by simp at h; omega)

theorem cat_append (a b : List Nat) (r : Nat → Nat) : cat (a ++ b) r = cat a (cat b r) := by
  funext d
  induction a generalizing d with
  | nil => rfl
  | cons x a ih => cases d <;> simp_all [cat]

theorem rep_add (y : List Nat) (a b : Nat) : rep y (a + b) = rep y a ++ rep y b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add]; simp [rep, ih, List.append_assoc]

theorem rep_succ' (y : List Nat) (n : Nat) : rep y (n + 1) = rep y n ++ y := by
  rw [rep_add]; simp [rep]

theorem rep_length (y : List Nat) (n : Nat) : (rep y n).length = y.length * n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp [rep, ih, Nat.mul_succ]; omega

theorem per_lt {o : List Nat} {d : Nat} (h : d < o.length) : per o d = o.getD d 0 := by
  simp [per, Nat.mod_eq_of_lt h]

theorem per_shift (o : List Nat) {d : Nat} (h : o.length ≤ d) : per o (d - o.length) = per o d := by
  have h1 := Nat.add_mod_right (d - o.length) o.length
  rw [Nat.sub_add_cancel h] at h1
  unfold per; rw [h1]

theorem per_cat {z : List Nat} (_hz : z ≠ []) : cat z (per z) = per z := by
  funext d
  by_cases h : d < z.length
  · rw [cat_lt h, per_lt h]
  · rw [cat_ge (by omega), per_shift z (by omega)]

theorem per_rep {z : List Nat} (hz : z ≠ []) (i : Nat) : per z = cat (rep z i) (per z) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [rep, cat_append, ← ih]; exact (per_cat hz).symm

theorem per_rot_aux (p r : List Nat) (e : Nat) :
    per (r ++ p) e = per (p ++ r) (e + p.length) := by
  by_cases hn : r.length + p.length = 0
  · have h1 : r = [] := List.length_eq_zero_iff.1 (by omega)
    have h2 : p = [] := List.length_eq_zero_iff.1 (by omega)
    subst h1; subst h2; simp [per]
  · unfold per
    have e1 : (r ++ p).length = r.length + p.length := List.length_append
    have e2 : (p ++ r).length = r.length + p.length := by rw [List.length_append]; omega
    rw [e1, e2, ← Nat.mod_add_mod e _ p.length]
    have hs : e % (r.length + p.length) < r.length + p.length := Nat.mod_lt _ (by omega)
    generalize e % (r.length + p.length) = s at hs
    by_cases hc : s < r.length
    · rw [Nat.mod_eq_of_lt (by omega : s + p.length < r.length + p.length)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hc,
        List.getElem?_append_right (by omega : p.length ≤ s + p.length)]
    · rw [Nat.mod_eq_sub_mod (by omega : r.length + p.length ≤ s + p.length),
        Nat.mod_eq_of_lt (by omega : s + p.length - (r.length + p.length) < r.length + p.length)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : r.length ≤ s),
        List.getElem?_append_left (by omega : s + p.length - (r.length + p.length) < p.length)]
      congr 2; omega

theorem per_rot (p r : List Nat) : per (p ++ r) = cat p (per (r ++ p)) := by
  funext d
  by_cases h : d < p.length
  · rw [cat_lt h, per_lt (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [cat_ge (by omega), per_rot_aux p r (d - p.length), Nat.sub_add_cancel (by omega)]

/-! ### Finite runs -/

/-- Output word and final state of the run over a finite word. -/
def run : σ → List Nat → List Nat × σ
  | q, [] => ([], q)
  | q, a :: w => ((step q a).2 :: (run (step q a).1 w).1, (run (step q a).1 w).2)

theorem run_append (q : σ) (w1 w2 : List Nat) :
    run step q (w1 ++ w2) = ((run step q w1).1 ++ (run step (run step q w1).2 w2).1,
      (run step (run step q w1).2 w2).2) := by
  induction w1 generalizing q with
  | nil => simp [run]
  | cons a w ih => simp [run, ih]

theorem run_length (q : σ) (w : List Nat) : (run step q w).1.length = w.length := by
  induction w generalizing q with
  | nil => simp [run]
  | cons a w ih => simp [run, ih]

/-- Block lemma. -/
theorem run_rep {q : σ} {y y' : List Nat} (h : run step q y = (y', q)) (n : Nat) :
    run step q (rep y n) = (rep y' n, q) := by
  induction n with
  | zero => simp [rep, run]
  | succ n ih => simp [rep, run_append, h, ih]

/-! ### Finite and infinite runs -/

theorem stateAt_succ' (q : σ) (u : Nat → Nat) (d : Nat) :
    stateAt step q u (d + 1) = stateAt step (step q (u 0)).1 (fun i => u (i + 1)) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show stateAt step q u (d + 1 + 1) = (step (stateAt step q u (d + 1)) (u (d + 1))).1 from rfl, ih]
    rfl

theorem outAt_succ (q : σ) (u : Nat → Nat) (d : Nat) :
    outAt step q u (d + 1) = outAt step (step q (u 0)).1 (fun i => u (i + 1)) d := by
  unfold outAt; rw [stateAt_succ']

/-- Infinite run on `w ++ rest`: finite outputs on `w`, then the run from the final state. -/
theorem outAt_cat (q : σ) (w : List Nat) (r : Nat → Nat) (d : Nat) :
    outAt step q (cat w r) d =
      if d < w.length then (run step q w).1.getD d 0
      else outAt step (run step q w).2 r (d - w.length) := by
  induction w generalizing q d with
  | nil => simp [run, cat]
  | cons a w ih =>
    cases d with
    | zero => simp [outAt, stateAt, cat, run]
    | succ d =>
      have e : outAt step q (cat (a :: w) r) (d + 1) = outAt step (step q a).1 (cat w r) d :=
        outAt_succ step q _ d
      rw [e, ih]
      simp [run]

/-- Function form of `outAt_cat`. -/
theorem outAt_cat' (q : σ) (w : List Nat) (r : Nat → Nat) :
    outAt step q (cat w r) = cat (run step q w).1 (outAt step (run step q w).2 r) := by
  funext d
  rw [outAt_cat]
  have hl := run_length step q w
  by_cases h : d < w.length
  · simp only [h, ↓reduceIte]; rw [cat_lt (by omega)]
  · simp only [h, ↓reduceIte]; rw [cat_ge (by omega), hl]

/-- Tail lemma. -/
theorem tail_out {z : List Nat} (hz : z ≠ []) {q q1 : σ} {i l : Nat} {o1 o2 : List Nat}
    (h1 : run step q (rep z i) = (o1, q1)) (h2 : run step q1 (rep z l) = (o2, q1))
    (hl : 1 ≤ l) : outAt step q (per z) = cat o1 (per o2) := by
  have hL : 0 < (rep z l).length := by
    rw [rep_length]; exact Nat.mul_pos (List.length_pos_iff.2 hz) hl
  have hl2 : o2.length = (rep z l).length := by
    have := run_length step q1 (rep z l); rw [h2] at this; exact this
  have hl1 : o1.length = (rep z i).length := by
    have := run_length step q (rep z i); rw [h1] at this; exact this
  have key2 : ∀ d, outAt step q1 (per z) d = per o2 d := by
    intro d
    induction d using Nat.strongRecOn with
    | _ d ih =>
      have e : per z = cat (rep z l) (per z) := per_rep hz l
      rw [e, outAt_cat, h2]
      by_cases hd : d < (rep z l).length
      · simp only [hd, ↓reduceIte]; rw [per_lt (by omega)]
      · simp only [hd, ↓reduceIte]
        rw [ih (d - (rep z l).length) (by omega), ← hl2, per_shift o2 (by omega)]
  funext d
  have e1 : per z = cat (rep z i) (per z) := per_rep hz i
  rw [e1, outAt_cat, h1]
  by_cases hd : d < (rep z i).length
  · simp only [hd, ↓reduceIte]; rw [cat_lt (by omega)]
  · simp only [hd, ↓reduceIte]
    rw [key2, cat_ge (by omega), hl1]

/-! ### Shapes -/

abbrev Blocks := List (List Nat × List Nat)

/-- `x0 y1^n1 x1 ... yj^nj xj z^ω`; `blocks = [(y1,x1), ..., (yj,xj)]`. Needs `z ≠ []`. -/
structure Shape where
  x0 : List Nat
  blocks : Blocks
  z : List Nat
  deriving DecidableEq, Repr

/-- `y1^n1 x1 ... yj^nj xj` (missing counters read as 0). -/
def finAux : Blocks → List Nat → List Nat
  | [], _ => []
  | (y, x) :: bs, ns => rep y (ns.headD 0) ++ (x ++ finAux bs ns.tail)

/-- The finite prefix `x0 y1^n1 x1 ... yj^nj xj`. -/
def fin (s : Shape) (n : List Nat) : List Nat := s.x0 ++ finAux s.blocks n

/-- The infinite word `fin s n ++ z^ω`. -/
def decode (s : Shape) (n : List Nat) : Nat → Nat := cat (fin s n) (per s.z)

theorem decode_def (s : Shape) (n : List Nat) :
    decode s n = cat (s.x0 ++ finAux s.blocks n) (per s.z) := rfl

theorem decode_lt {s : Shape} {n : List Nat} {d : Nat} (h : d < (fin s n).length) :
    decode s n d = (fin s n).getD d 0 := cat_lt h

theorem decode_ge {s : Shape} {n : List Nat} {d : Nat} (h : (fin s n).length ≤ d) :
    decode s n d = per s.z (d - (fin s n).length) := cat_ge h

/-! ### Symbolic step -/

section Sstep
variable [DecidableEq σ]

/-- `u ≤ n` pointwise, same length. -/
def Pw : List Nat → List Nat → Prop
  | [], [] => True
  | a :: as, b :: bs => a ≤ b ∧ Pw as bs
  | _, _ => False

/-- Pointwise `n - u`. -/
def nsub (n u : List Nat) : List Nat := List.zipWith (· - ·) n u

/-- Search `f i` for `i = start, ..., start + fuel - 1`. -/
def findL {α : Type} (f : Nat → Option α) : Nat → Nat → Option α
  | 0, _ => none
  | fuel + 1, i => match f i with
    | some r => some r
    | none => findL f fuel (i + 1)

theorem findL_spec {α : Type} {f : Nat → Option α} {r : α} :
    ∀ {fuel i : Nat}, findL f fuel i = some r → ∃ j, i ≤ j ∧ f j = some r := by
  intro fuel
  induction fuel with
  | zero => intro i h; simp [findL] at h
  | succ fuel ih =>
    intro i h
    cases hf : f i with
    | some r' =>
      simp only [findL, hf] at h
      cases h
      exact ⟨i, Nat.le_refl _, hf⟩
    | none =>
      simp only [findL, hf] at h
      obtain ⟨j, hj, hj'⟩ := ih h
      exact ⟨j, by omega, hj'⟩

/-- Unroll copies of `y` from state `q` until `y` returns to its state (at most `fuel - 1`
unrolls). Result: (output of the unrolled copies, their number, fixed state, output on `y`). -/
def unroll (y : List Nat) : σ → List Nat → Nat → Nat → Option (List Nat × Nat × σ × List Nat)
  | _, _, _, 0 => none
  | q, acc, k, fuel + 1 =>
    if (run step q y).2 = q then some (acc, k, q, (run step q y).1)
    else unroll y (run step q y).2 (acc ++ (run step q y).1) (k + 1) fuel

theorem unroll_spec (y : List Nat) :
    ∀ (fuel : Nat) (q : σ) (acc : List Nat) (k : Nat) (o : List Nat) (k' : Nat) (q' : σ)
      (y' : List Nat), unroll step y q acc k fuel = some (o, k', q', y') →
      ∃ j o', k' = k + j ∧ o = acc ++ o' ∧ run step q (rep y j) = (o', q') ∧
        run step q' y = (y', q') := by
  intro fuel
  induction fuel with
  | zero => intro q acc k o k' q' y' h; simp [unroll] at h
  | succ fuel ih =>
    intro q acc k o k' q' y' h
    by_cases hq : (run step q y).2 = q
    · simp only [unroll, hq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨0, [], by simp, by simp, by simp [rep, run], Prod.ext rfl hq⟩
    · simp only [unroll, hq, ↓reduceIte] at h
      obtain ⟨j, o', hk, ho, hr, hf⟩ := ih _ _ _ _ _ _ _ h
      refine ⟨j + 1, (run step q y).1 ++ o', by omega, by simp [ho], ?_, hf⟩
      simp [rep, run_append, hr]

/-- Tail search: `i ≤ 8` copies, then a period of `l ∈ [1, 8]` copies of `z` returning to its state. -/
def tailTry (q : σ) (z : List Nat) : Option (List Nat × List Nat) :=
  findL (fun i =>
    findL (fun l =>
      if (run step (run step q (rep z i)).2 (rep z l)).2 = (run step q (rep z i)).2
      then some ((run step q (rep z i)).1, (run step (run step q (rep z i)).2 (rep z l)).1)
      else none) 8 1) 9 0

theorem tailTry_spec {q : σ} {z o1 o2 : List Nat} (h : tailTry step q z = some (o1, o2)) :
    ∃ i l q1, 1 ≤ l ∧ run step q (rep z i) = (o1, q1) ∧ run step q1 (rep z l) = (o2, q1) := by
  obtain ⟨i, -, hi⟩ := findL_spec h
  obtain ⟨l, hl, hl'⟩ := findL_spec hi
  by_cases hc : (run step (run step q (rep z i)).2 (rep z l)).2 = (run step q (rep z i)).2
  · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hl'
    obtain ⟨rfl, rfl⟩ := hl'
    exact ⟨i, l, _, hl, rfl, Prod.ext rfl hc⟩
  · simp [hc] at hl'

/-- Process the blocks from state `q`; returns (output of the unrolled copies of the first block
(or of the tail), new blocks, unroll counts, new tail). -/
def go : σ → Blocks → List Nat → Option (List Nat × Blocks × List Nat × List Nat)
  | q, [], z =>
    if z = [] then none else
    match tailTry step q z with
    | none => none
    | some (o1, o2) => some (o1, [], [], o2)
  | q, (y, x) :: bs, z =>
    match unroll step y q [] 0 9 with
    | none => none
    | some (o, k, q', y') =>
      match go (run step q' x).2 bs z with
      | none => none
      | some (pre, bs', us, z') =>
        some (o, (y', (run step q' x).1 ++ pre) :: bs', k :: us, z')

/-- Symbolic step from state `q` (the caller drops the first letter of the output).
Result: new shape and the per-block unroll counts `u`. -/
def sstep (q : σ) (s : Shape) : Option (Shape × List Nat) :=
  match go step (run step q s.x0).2 s.blocks s.z with
  | none => none
  | some (pre, bs', us, z') => some ({ x0 := (run step q s.x0).1 ++ pre, blocks := bs', z := z' }, us)

theorem go_sound (z : List Nat) : ∀ (bs : Blocks) (q : σ) (pre : List Nat) (bs' : Blocks)
    (us z' : List Nat), go step q bs z = some (pre, bs', us, z') →
    ∀ ns, Pw us ns →
      outAt step q (cat (finAux bs ns) (per z)) =
        cat (pre ++ finAux bs' (nsub ns us)) (per z') := by
  intro bs
  induction bs with
  | nil =>
    intro q pre bs' us z' h ns hp
    by_cases hz : z = []
    · simp [go, hz] at h
    · cases ht : tailTry step q z with
      | none => simp [go, hz, ht] at h
      | some p =>
        obtain ⟨o1, o2⟩ := p
        simp only [go, hz, ht, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        obtain ⟨i, l, q1, hl, h1, h2⟩ := tailTry_spec step ht
        cases ns with
        | cons => simp [Pw] at hp
        | nil => simpa [finAux] using tail_out step hz h1 h2 hl
  | cons b bs ih =>
    obtain ⟨y, x⟩ := b
    intro q pre bs' us z' h ns hp
    cases hu : unroll step y q [] 0 9 with
    | none => simp [go, hu] at h
    | some t =>
      obtain ⟨o, k, q', y'⟩ := t
      cases hg : go step (run step q' x).2 bs z with
      | none => simp [go, hu, hg] at h
      | some t2 =>
        obtain ⟨pre2, bs2, us2, z2⟩ := t2
        simp only [go, hu, hg, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        obtain ⟨j, o', hk, ho, hr, hf⟩ := unroll_spec step y _ _ _ _ _ _ _ _ hu
        cases ns with
        | nil => simp [Pw] at hp
        | cons n ns' =>
          obtain ⟨hkn, hp'⟩ := hp
          obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
          have key : cat (finAux ((y, x) :: bs) ((k + m) :: ns')) (per z) =
              cat (rep y k) (cat (rep y m) (cat x (cat (finAux bs ns') (per z)))) := by
            simp [finAux, rep_add, cat_append]
          have hy : run step q (rep y k) = (o', q') := by
            have : j = k := by omega
            subst this; exact hr
          rw [key, outAt_cat', hy, outAt_cat', run_rep step hf, outAt_cat',
            ih _ _ _ _ _ hg _ hp']
          simp [ho, finAux, nsub, cat_append, List.append_assoc]

theorem sstep_sound {q : σ} {s s' : Shape} {u : List Nat} (h : sstep step q s = some (s', u))
    {n : List Nat} (hp : Pw u n) (d : Nat) :
    outAt step q (decode s n) d = decode s' (nsub n u) d := by
  unfold sstep at h
  cases hg : go step (run step q s.x0).2 s.blocks s.z with
  | none => simp [hg] at h
  | some t =>
    obtain ⟨pre, bs', us, z'⟩ := t
    simp only [hg, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := go_sound step s.z _ _ _ _ _ _ hg _ hp
    rw [decode_def, cat_append, outAt_cat', this, decode_def]
    simp [cat_append, List.append_assoc]

end Sstep

/-! ### Normalisation moves

Block indices are 0-based.  Block `i` has left boundary number `i` (number 0 is `x0`) and right
boundary number `i+1` (the stored `.2` of block `i`).

Counter convention (`CEdit`, applied to the counter list `n` of the old shape):
* `toLeft i`, `toRight i`: `adj i (-1)`  (n_i := n_i - 1; fails if n_i = 0)
* `fromLeft i`, `fromRight i`: `adj i 1`  (n_i := n_i + 1)
* `expand i v`: `del i v`  (entry i dropped; side condition n_i = v)
* `split i k len c`: `ins i c`  (new entry c inserted at index i; the new block is block i)
* `tailIn`, `tailOut`, `tailRot k`: `id`.
`applyMove s m = some (s', e)` and `e.apply n = some n'` give `decode s n = decode s' n'`. -/

/-- Counter edits. -/
inductive CEdit
  | id
  | adj (i : Nat) (d : Int)
  | del (i v : Nat)
  | ins (i c : Nat)
  deriving DecidableEq, Repr

def adjAt (d : Int) : Nat → List Nat → Option (List Nat)
  | 0, n :: ns => if 0 ≤ (n : Int) + d then some (((n : Int) + d).toNat :: ns) else none
  | i + 1, n :: ns => (adjAt d i ns).map (n :: ·)
  | _, [] => none

def delAt (v : Nat) : Nat → List Nat → Option (List Nat)
  | 0, n :: ns => if n = v then some ns else none
  | i + 1, n :: ns => (delAt v i ns).map (n :: ·)
  | _, [] => none

def insAt (c : Nat) : Nat → List Nat → Option (List Nat)
  | 0, ns => some (c :: ns)
  | i + 1, n :: ns => (insAt c i ns).map (n :: ·)
  | _, [] => none

def CEdit.apply : CEdit → List Nat → Option (List Nat)
  | .id, n => some n
  | .adj i d, n => adjAt d i n
  | .del i v, n => delAt v i n
  | .ins i c, n => insAt c i n

/-- Local edit of block `i` given its left boundary. -/
def editAt (f : List Nat → List Nat × List Nat → Option (List Nat × (List Nat × List Nat))) :
    Nat → List Nat → Blocks → Option (List Nat × Blocks)
  | 0, x, b :: bs => (f x b).map fun r => (r.1, r.2 :: bs)
  | i + 1, x, b :: bs => (editAt f i b.2 bs).map fun r => (x, (b.1, r.1) :: r.2)
  | _, _, [] => none

theorem finAux_cons (y x : List Nat) (bs : Blocks) (n : Nat) (ns : List Nat) :
    finAux ((y, x) :: bs) (n :: ns) = rep y n ++ (x ++ finAux bs ns) := rfl

theorem editAt_sound (d : Int)
    (f : List Nat → List Nat × List Nat → Option (List Nat × (List Nat × List Nat)))
    (hf : ∀ x b x' b', f x b = some (x', b') → ∀ n n' : Nat, (n : Int) + d = n' →
      ∀ R, x ++ (rep b.1 n ++ (b.2 ++ R)) = x' ++ (rep b'.1 n' ++ (b'.2 ++ R))) :
    ∀ (i : Nat) (x : List Nat) (bs : Blocks) (x' : List Nat) (bs' : Blocks) (ns ns' : List Nat),
      editAt f i x bs = some (x', bs') → adjAt d i ns = some ns' →
      x ++ finAux bs ns = x' ++ finAux bs' ns' := by
  intro i
  induction i with
  | zero =>
    intro x bs x' bs' ns ns' h hn
    cases bs with
    | nil => simp [editAt] at h
    | cons b bs0 =>
      obtain ⟨y, xr⟩ := b
      cases ns with
      | nil => simp [adjAt] at hn
      | cons n ns0 =>
        cases hf' : f x (y, xr) with
        | none => simp [editAt, hf'] at h
        | some t =>
          obtain ⟨xx, y2, xr2⟩ := t
          simp only [editAt, hf', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          by_cases hg : 0 ≤ (n : Int) + d
          · simp only [adjAt, hg, ↓reduceIte, Option.some.injEq] at hn
            subst hn
            rw [finAux_cons, finAux_cons]
            exact hf x (y, xr) xx (y2, xr2) hf' n _ (by omega) _
          · simp [adjAt, hg] at hn
  | succ i ih =>
    intro x bs x' bs' ns ns' h hn
    cases bs with
    | nil => simp [editAt] at h
    | cons b bs0 =>
      obtain ⟨y, xr⟩ := b
      cases ns with
      | nil => simp [adjAt] at hn
      | cons n ns0 =>
        cases he : editAt f i xr bs0 with
        | none => simp [editAt, he] at h
        | some t =>
          obtain ⟨x1, bs1⟩ := t
          simp only [editAt, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases ha : adjAt d i ns0 with
          | none => simp [adjAt, ha] at hn
          | some ns1 =>
            simp only [adjAt, ha, Option.map_some, Option.some.injEq] at hn
            subst hn
            rw [finAux_cons, finAux_cons, ih _ _ _ _ _ _ he ha]

/-- Boundary edits of block `i`'s neighbours (`toLeft` etc.): `f` data. -/
def fToLeft (x : List Nat) (b : List Nat × List Nat) : Option (List Nat × (List Nat × List Nat)) :=
  some (x ++ b.1, b)

def fToRight (x : List Nat) (b : List Nat × List Nat) : Option (List Nat × (List Nat × List Nat)) :=
  some (x, (b.1, b.1 ++ b.2))

def fFromLeft (x : List Nat) (b : List Nat × List Nat) : Option (List Nat × (List Nat × List Nat)) :=
  if x.drop (x.length - b.1.length) = b.1 then some (x.take (x.length - b.1.length), b) else none

def fFromRight (x : List Nat) (b : List Nat × List Nat) :
    Option (List Nat × (List Nat × List Nat)) :=
  if b.2.take b.1.length = b.1 then some (x, (b.1, b.2.drop b.1.length)) else none

theorem fToLeft_spec : ∀ x b x' b', fToLeft x b = some (x', b') → ∀ n n' : Nat,
    (n : Int) + (-1) = n' → ∀ R, x ++ (rep b.1 n ++ (b.2 ++ R)) = x' ++ (rep b'.1 n' ++ (b'.2 ++ R)) := by
  intro x b x' b' h n n' hn R
  simp only [fToLeft, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain rfl : n = n' + 1 := by omega
  simp [rep, List.append_assoc]

theorem fToRight_spec : ∀ x b x' b', fToRight x b = some (x', b') → ∀ n n' : Nat,
    (n : Int) + (-1) = n' → ∀ R, x ++ (rep b.1 n ++ (b.2 ++ R)) = x' ++ (rep b'.1 n' ++ (b'.2 ++ R)) := by
  intro x b x' b' h n n' hn R
  simp only [fToRight, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain rfl : n = n' + 1 := by omega
  simp [rep_succ', List.append_assoc]

theorem fFromLeft_spec : ∀ x b x' b', fFromLeft x b = some (x', b') → ∀ n n' : Nat,
    (n : Int) + 1 = n' → ∀ R, x ++ (rep b.1 n ++ (b.2 ++ R)) = x' ++ (rep b'.1 n' ++ (b'.2 ++ R)) := by
  intro x b x' b' h n n' hn R
  unfold fFromLeft at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain rfl : n' = n + 1 := by omega
    have hx : x.take (x.length - b.1.length) ++ b.1 = x := by
      conv => rhs; rw [← List.take_append_drop (x.length - b.1.length) x]
      rw [hc]
    conv => lhs; rw [← hx]
    simp [rep, List.append_assoc]
  · simp at h

theorem fFromRight_spec : ∀ x b x' b', fFromRight x b = some (x', b') → ∀ n n' : Nat,
    (n : Int) + 1 = n' → ∀ R, x ++ (rep b.1 n ++ (b.2 ++ R)) = x' ++ (rep b'.1 n' ++ (b'.2 ++ R)) := by
  intro x b x' b' h n n' hn R
  unfold fFromRight at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain rfl : n' = n + 1 := by omega
    have hx : b.1 ++ b.2.drop b.1.length = b.2 := by
      conv => rhs; rw [← List.take_append_drop b.1.length b.2]
      rw [hc]
    conv => lhs; rw [← hx]
    simp [rep_succ', List.append_assoc]
  · simp at h

/-- Rotate block `i` by `r`: `y = a ++ b` becomes `b ++ a`, `a` goes to the left boundary and `b`
to the right one; one copy leaves the counter. -/
def fRot (r : Nat) (x : List Nat) (b : List Nat × List Nat) :
    Option (List Nat × (List Nat × List Nat)) :=
  some (x ++ b.1.take r, (b.1.drop r ++ b.1.take r, b.1.drop r ++ b.2))

theorem rep_rot (a b : List Nat) (k : Nat) : a ++ rep (b ++ a) k = rep (a ++ b) k ++ a := by
  induction k with
  | zero => simp [rep]
  | succ k ih => simp only [rep, List.append_assoc]; rw [← ih]

theorem rep_succ_rot (a b : List Nat) (n : Nat) :
    rep (a ++ b) (n + 1) = a ++ (rep (b ++ a) n ++ b) := by
  rw [rep_succ', ← List.append_assoc, ← rep_rot]; simp

theorem fRot_spec (r : Nat) : ∀ x b x' b', fRot r x b = some (x', b') → ∀ n n' : Nat,
    (n : Int) + (-1) = n' → ∀ R, x ++ (rep b.1 n ++ (b.2 ++ R)) = x' ++ (rep b'.1 n' ++ (b'.2 ++ R)) := by
  intro x b x' b' h n n' hn R
  simp only [fRot, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain rfl : n = n' + 1 := by omega
  have key : rep b.1 (n' + 1) = b.1.take r ++ (rep (b.1.drop r ++ b.1.take r) n' ++ b.1.drop r) := by
    have := rep_succ_rot (b.1.take r) (b.1.drop r) n'
    rwa [List.take_append_drop] at this
  rw [key]
  simp [List.append_assoc]

/-- Merge block `i` (with counter value `v`) into the preceding boundary. -/
def expandAt (v : Nat) : Nat → List Nat → Blocks → Option (List Nat × Blocks)
  | 0, x, (y, xr) :: bs => some (x ++ rep y v ++ xr, bs)
  | i + 1, x, b :: bs => (expandAt v i b.2 bs).map fun r => (x, (b.1, r.1) :: r.2)
  | _, _, [] => none

theorem expandAt_sound (v : Nat) : ∀ (i : Nat) (x : List Nat) (bs : Blocks) (x' : List Nat)
    (bs' : Blocks) (ns ns' : List Nat), expandAt v i x bs = some (x', bs') →
    delAt v i ns = some ns' → x ++ finAux bs ns = x' ++ finAux bs' ns' := by
  intro i
  induction i with
  | zero =>
    intro x bs x' bs' ns ns' h hn
    cases bs with
    | nil => simp [expandAt] at h
    | cons b bs0 =>
      obtain ⟨y, xr⟩ := b
      cases ns with
      | nil => simp [delAt] at hn
      | cons n ns0 =>
        simp only [expandAt, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        by_cases hv : n = v
        · simp only [delAt, hv, ↓reduceIte, Option.some.injEq] at hn
          subst hn; subst hv
          rw [finAux_cons]; simp [List.append_assoc]
        · simp [delAt, hv] at hn
  | succ i ih =>
    intro x bs x' bs' ns ns' h hn
    cases bs with
    | nil => simp [expandAt] at h
    | cons b bs0 =>
      obtain ⟨y, xr⟩ := b
      cases ns with
      | nil => simp [delAt] at hn
      | cons n ns0 =>
        cases he : expandAt v i xr bs0 with
        | none => simp [expandAt, he] at h
        | some t =>
          obtain ⟨x1, bs1⟩ := t
          simp only [expandAt, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases ha : delAt v i ns0 with
          | none => simp [delAt, ha] at hn
          | some ns1 =>
            simp only [delAt, ha, Option.map_some, Option.some.injEq] at hn
            subst hn
            rw [finAux_cons, finAux_cons, ih _ _ _ _ _ _ he ha]

/-- Cut boundary number `i` (word `w`) into `a ++ y^c ++ b`, `y = (w.drop k).take len`;
new block `(y, b)` becomes block `i`. -/
def splitAt' (k len c : Nat) : Nat → List Nat → Blocks → Option (List Nat × Blocks)
  | 0, x, bs =>
    if (x.drop k).take (len * c) = rep ((x.drop k).take len) c then
      some (x.take k, ((x.drop k).take len, (x.drop k).drop (len * c)) :: bs)
    else none
  | i + 1, x, b :: bs => (splitAt' k len c i b.2 bs).map fun r => (x, (b.1, r.1) :: r.2)
  | _, _, [] => none

theorem splitAt'_sound (k len c : Nat) : ∀ (i : Nat) (x : List Nat) (bs : Blocks) (x' : List Nat)
    (bs' : Blocks) (ns ns' : List Nat), splitAt' k len c i x bs = some (x', bs') →
    insAt c i ns = some ns' → x ++ finAux bs ns = x' ++ finAux bs' ns' := by
  intro i
  induction i with
  | zero =>
    intro x bs x' bs' ns ns' h hn
    by_cases hc : (x.drop k).take (len * c) = rep ((x.drop k).take len) c
    · simp only [splitAt', hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [insAt, Option.some.injEq] at hn
      subst hn
      have hx : x.take k ++ ((x.drop k).take (len * c) ++ (x.drop k).drop (len * c)) = x := by
        rw [List.take_append_drop, List.take_append_drop]
      conv => lhs; rw [← hx]
      rw [finAux_cons, hc]
      simp [List.append_assoc]
    · simp [splitAt', hc] at h
  | succ i ih =>
    intro x bs x' bs' ns ns' h hn
    cases bs with
    | nil => simp [splitAt'] at h
    | cons b bs0 =>
      obtain ⟨y, xr⟩ := b
      cases ns with
      | nil => simp [insAt] at hn
      | cons n ns0 =>
        cases he : splitAt' k len c i xr bs0 with
        | none => simp [splitAt', he] at h
        | some t =>
          obtain ⟨x1, bs1⟩ := t
          simp only [splitAt', he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases ha : insAt c i ns0 with
          | none => simp [insAt, ha] at hn
          | some ns1 =>
            simp only [insAt, ha, Option.map_some, Option.some.injEq] at hn
            subst hn
            rw [finAux_cons, finAux_cons, ih _ _ _ _ _ _ he ha]

/-- Edit the last boundary. -/
def lastEdit (f : List Nat → Option (List Nat)) : List Nat → Blocks → Option (List Nat × Blocks)
  | x, [] => (f x).map fun x' => (x', [])
  | x, b :: bs => (lastEdit f b.2 bs).map fun r => (x, (b.1, r.1) :: r.2)

theorem lastEdit_sound (z z' : List Nat) (f : List Nat → Option (List Nat))
    (hf : ∀ x x', f x = some x' → cat x (per z) = cat x' (per z')) :
    ∀ (bs : Blocks) (x x' : List Nat) (bs' : Blocks) (ns : List Nat),
      lastEdit f x bs = some (x', bs') →
      cat (x ++ finAux bs ns) (per z) = cat (x' ++ finAux bs' ns) (per z') := by
  intro bs
  induction bs with
  | nil =>
    intro x x' bs' ns h
    cases hx : f x with
    | none => simp [lastEdit, hx] at h
    | some t =>
      simp only [lastEdit, hx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa [finAux] using hf _ _ hx
  | cons b bs ih =>
    obtain ⟨y, xr⟩ := b
    intro x x' bs' ns h
    cases he : lastEdit f xr bs with
    | none => simp [lastEdit, he] at h
    | some t =>
      obtain ⟨x1, bs1⟩ := t
      simp only [lastEdit, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := ih _ _ _ ns.tail he
      simp only [finAux, cat_append] at this ⊢
      rw [this]

/-- Normalisation moves. -/
inductive Move
  | toLeft (i : Nat)
  | toRight (i : Nat)
  | fromLeft (i : Nat)
  | fromRight (i : Nat)
  | expand (i v : Nat)
  | split (i k len c : Nat)
  | tailIn
  | tailOut
  | tailRot (k : Nat)
  | rot (i r : Nat)
  | tshrink (c : Nat)
  deriving DecidableEq, Repr

def tailF (s : Shape) : Move → Option ((List Nat → Option (List Nat)) × List Nat)
  | .tailOut => some (fun x => some (x ++ s.z), s.z)
  | .tailIn => some (fun x =>
      if x.drop (x.length - s.z.length) = s.z then some (x.take (x.length - s.z.length)) else none,
      s.z)
  | .tailRot k => some (fun x => some (x ++ s.z.take k), s.z.drop k ++ s.z.take k)
  | .tshrink c => some (fun x =>
      if c ≠ 0 ∧ rep (s.z.take (s.z.length / c)) c = s.z then some x else none,
      s.z.take (s.z.length / c))
  | _ => none

/-- Tail moves (`z ≠ []` required). -/
def applyTail (s : Shape) (m : Move) : Option (Shape × CEdit) :=
  if s.z = [] then none else
  match tailF s m with
  | none => none
  | some (f, z') => (lastEdit f s.x0 s.blocks).map
      fun r => ({ x0 := r.1, blocks := r.2, z := z' }, .id)

/-- Apply a move; returns the new shape and the counter edit (see the convention above). -/
def applyMove (s : Shape) : Move → Option (Shape × CEdit)
  | .toLeft i => (editAt fToLeft i s.x0 s.blocks).map
      fun r => ({ s with x0 := r.1, blocks := r.2 }, .adj i (-1))
  | .toRight i => (editAt fToRight i s.x0 s.blocks).map
      fun r => ({ s with x0 := r.1, blocks := r.2 }, .adj i (-1))
  | .fromLeft i => (editAt fFromLeft i s.x0 s.blocks).map
      fun r => ({ s with x0 := r.1, blocks := r.2 }, .adj i 1)
  | .fromRight i => (editAt fFromRight i s.x0 s.blocks).map
      fun r => ({ s with x0 := r.1, blocks := r.2 }, .adj i 1)
  | .expand i v => (expandAt v i s.x0 s.blocks).map
      fun r => ({ s with x0 := r.1, blocks := r.2 }, .del i v)
  | .split i k len c => (splitAt' k len c i s.x0 s.blocks).map
      fun r => ({ s with x0 := r.1, blocks := r.2 }, .ins i c)
  | .rot i r => (editAt (fRot r) i s.x0 s.blocks).map
      fun r' => ({ s with x0 := r'.1, blocks := r'.2 }, .adj i (-1))
  | m => applyTail s m

theorem rep_nil (c : Nat) : rep [] c = [] := by
  induction c with
  | zero => rfl
  | succ c ih => simp [rep, ih]

theorem getD_rep (w : List Nat) (hw : w ≠ []) :
    ∀ (c e : Nat), e < w.length * c → (rep w c).getD e 0 = w.getD (e % w.length) 0 := by
  have hl : 0 < w.length := List.length_pos_iff.2 hw
  intro c
  induction c with
  | zero => intro e h; simp at h
  | succ c ih =>
    intro e h
    simp only [rep]
    by_cases he : e < w.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left he,
        Nat.mod_eq_of_lt he, ← List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        ← List.getD_eq_getElem?_getD, ih (e - w.length)
          (by have : w.length * (c + 1) = w.length * c + w.length := by
                rw [Nat.mul_add, Nat.mul_one]
              omega)]
      congr 1
      have h2 := Nat.add_mod_right (e - w.length) w.length
      rw [Nat.sub_add_cancel (by omega)] at h2
      exact h2.symm

theorem per_rep_eq (w : List Nat) {c : Nat} (hc : c ≠ 0) : per (rep w c) = per w := by
  funext d
  by_cases hw : w = []
  · subst hw; simp [rep_nil, per]
  · have hl : 0 < w.length := List.length_pos_iff.2 hw
    have hc' : 0 < c := Nat.pos_of_ne_zero hc
    unfold per
    rw [rep_length, getD_rep w hw c _ (Nat.mod_lt _ (Nat.mul_pos hl hc')),
      Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right _ _)]

theorem tail_spec (s : Shape) (hz : s.z ≠ []) (m : Move) (f : List Nat → Option (List Nat))
    (z' : List Nat) (h : tailF s m = some (f, z')) :
    ∀ x x', f x = some x' → cat x (per s.z) = cat x' (per z') := by
  intro x x' hx
  cases m with
  | tailOut =>
    simp only [tailF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Option.some.injEq] at hx; subst hx
    rw [cat_append, per_cat hz]
  | tailIn =>
    simp only [tailF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    dsimp only at hx
    split at hx
    · rename_i hc
      simp only [Option.some.injEq] at hx; subst hx
      have : x.take (x.length - s.z.length) ++ s.z = x := by
        conv => rhs; rw [← List.take_append_drop (x.length - s.z.length) x]
        rw [hc]
      conv => lhs; rw [← this]
      rw [cat_append, per_cat hz]
    · simp at hx
  | tailRot k =>
    simp only [tailF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Option.some.injEq] at hx; subst hx
    rw [cat_append]
    conv => lhs; rw [← List.take_append_drop k s.z]
    rw [per_rot]
  | tshrink c =>
    simp only [tailF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    dsimp only at hx
    split at hx
    · rename_i hc
      simp only [Option.some.injEq] at hx; subst hx
      conv => lhs; rw [← hc.2]
      rw [per_rep_eq _ hc.1]
    · simp at hx
  | _ => simp [tailF] at h

theorem applyTail_sound {s s' : Shape} {m : Move} {e : CEdit}
    (h : applyTail s m = some (s', e)) {n n' : List Nat} (hn : e.apply n = some n') :
    decode s n = decode s' n' := by
  unfold applyTail at h
  by_cases hz : s.z = []
  · simp [hz] at h
  · simp only [hz, ↓reduceIte] at h
    cases ht : tailF s m with
    | none => simp [ht] at h
    | some t =>
      obtain ⟨f, z'⟩ := t
      cases he : lastEdit f s.x0 s.blocks with
      | none => simp [ht, he] at h
      | some r =>
        obtain ⟨x1, bs1⟩ := r
        simp only [ht, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [CEdit.apply, Option.some.injEq] at hn
        subst hn
        exact lastEdit_sound s.z z' f (tail_spec s hz m f z' ht) s.blocks _ _ _ _ he

theorem decode_congr {s : Shape} {n n' : List Nat} {x' : List Nat} {bs' : Blocks}
    (h : s.x0 ++ finAux s.blocks n = x' ++ finAux bs' n') :
    decode s n = decode { s with x0 := x', blocks := bs' } n' := by
  simp only [decode_def]; rw [h]

/-- Soundness of all moves: with `e.apply n = some n'`, the decoded words agree. -/
theorem applyMove_sound {s s' : Shape} {m : Move} {e : CEdit}
    (h : applyMove s m = some (s', e)) {n n' : List Nat} (hn : e.apply n = some n') :
    decode s n = decode s' n' := by
  cases m with
  | toLeft i =>
    cases he : editAt fToLeft i s.x0 s.blocks with
    | none => simp [applyMove, he] at h
    | some t =>
      simp only [applyMove, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact decode_congr (editAt_sound _ _ fToLeft_spec i _ _ _ _ _ _ he hn)
  | toRight i =>
    cases he : editAt fToRight i s.x0 s.blocks with
    | none => simp [applyMove, he] at h
    | some t =>
      simp only [applyMove, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact decode_congr (editAt_sound _ _ fToRight_spec i _ _ _ _ _ _ he hn)
  | fromLeft i =>
    cases he : editAt fFromLeft i s.x0 s.blocks with
    | none => simp [applyMove, he] at h
    | some t =>
      simp only [applyMove, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact decode_congr (editAt_sound _ _ fFromLeft_spec i _ _ _ _ _ _ he hn)
  | fromRight i =>
    cases he : editAt fFromRight i s.x0 s.blocks with
    | none => simp [applyMove, he] at h
    | some t =>
      simp only [applyMove, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact decode_congr (editAt_sound _ _ fFromRight_spec i _ _ _ _ _ _ he hn)
  | expand i v =>
    cases he : expandAt v i s.x0 s.blocks with
    | none => simp [applyMove, he] at h
    | some t =>
      simp only [applyMove, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact decode_congr (expandAt_sound v i _ _ _ _ _ _ he hn)
  | split i k len c =>
    cases he : splitAt' k len c i s.x0 s.blocks with
    | none => simp [applyMove, he] at h
    | some t =>
      simp only [applyMove, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact decode_congr (splitAt'_sound k len c i _ _ _ _ _ _ he hn)
  | rot i r =>
    cases he : editAt (fRot r) i s.x0 s.blocks with
    | none => simp [applyMove, he] at h
    | some t =>
      simp only [applyMove, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact decode_congr (editAt_sound _ _ (fRot_spec r) i _ _ _ _ _ _ he hn)
  | tshrink c => exact applyTail_sound (by simpa only [applyMove] using h) hn
  | tailIn => exact applyTail_sound (by simpa only [applyMove] using h) hn
  | tailOut => exact applyTail_sound (by simpa only [applyMove] using h) hn
  | tailRot k => exact applyTail_sound (by simpa only [applyMove] using h) hn

/-! ### Tests (toy parity transducer) -/

/-- State = parity of the ones read so far; output = input xor state. -/
def toyStep (q : Bool) (a : Nat) : Bool × Nat :=
  (q != (a == 1), if q then 1 - a else a)

def toyShape : Shape := ⟨[0, 1, 1], [([1, 1], [0, 0]), ([1, 0, 1], [1])], [1, 0]⟩

example : run toyStep false [1, 1, 0, 1] = ([1, 0, 0, 1], true) := by decide

example : decode toyShape [3, 2] 5 = 1 := by decide

example : (fin toyShape [3, 2]).length = 3 + 6 + 2 + 6 + 1 := by decide

example : sstep toyStep false toyShape =
    some (⟨[0, 1, 0], [([1, 0], [0, 0]), ([1, 1, 0], [1])], [0, 0, 1, 1]⟩, [0, 0]) := by
  decide +kernel

/-- soundness instance: output of the run equals the symbolic output, checked on 60 letters. -/
example : ∀ d < 60, outAt toyStep false (decode toyShape [3, 2]) d =
    decode ⟨[0, 1, 0], [([1, 0], [0, 0]), ([1, 1, 0], [1])], [0, 0, 1, 1]⟩ [3, 2] d := by
  decide +kernel

example : applyMove toyShape (.toLeft 0) =
    some (⟨[0, 1, 1, 1, 1], [([1, 1], [0, 0]), ([1, 0, 1], [1])], [1, 0]⟩, .adj 0 (-1)) := by
  decide +kernel

example : ∀ d < 40, decode toyShape [3, 2] d =
    decode ⟨[0, 1, 1, 1, 1], [([1, 1], [0, 0]), ([1, 0, 1], [1])], [1, 0]⟩ [2, 2] d := by
  decide +kernel

example : (applyMove toyShape (.expand 0 3)).map (·.2) = some (.del 0 3) := by decide +kernel

example : (applyMove toyShape (.tailRot 1)).map (·.1.z) = some [0, 1] := by decide +kernel

example : ∀ d < 40, decode toyShape [3, 2] d =
    decode ⟨[0, 1, 1], [([1, 1], [0, 0]), ([1, 0, 1], [1, 1])], [0, 1]⟩ [3, 2] d := by decide +kernel

end Family
