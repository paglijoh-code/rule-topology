import LeadACheck
import LeadASpec
/-
Soundness of the H.A certificate checker (`LeadACheck`) with respect to the relational spec
(`LeadASpec`): `checkCert S1 S2 c = true` implies that `outcome S1 S2` is eventually doubly
periodic (`checkCert_sound`).  The statement is about `outcome` only.

Layout: (1) Sprague-Grundy values `sgFn` of Sub(S2): `IsP1 S a b <-> sgFn S a = sgFn S b`, and the
checker's `gval` equals `sgFn`; (2) the row recursion equals the game equation; (3) a row that
passes `rowOk` is the true row (finite-state argument); (4) window repeat; (5) the theorem.
-/
namespace LeadA

theorem find_range (p : Nat → Bool) : ∀ n m, (List.range n).find? p = some m → p m = true ∧ ∀ k < m, p k = false := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro m h
    rw [List.range_succ, List.find?_append] at h
    cases h1 : (List.range n).find? p with
    | some m' => rw [h1] at h; simp at h; subst h; exact ih _ h1
    | none =>
      rw [h1] at h
      have hn := List.find?_eq_none.1 h1
      simp only [Option.none_or, List.find?_singleton] at h
      split at h
      · rename_i hp
        simp at h; subst h
        refine ⟨hp, fun k hk => ?_⟩
        have := hn k (List.mem_range.2 hk)
        simpa using this
      · simp at h

theorem pigeon : ∀ (n : Nat) (l : List Nat), (∀ i < n, i ∈ l) → n ≤ l.length := by
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro l h
    have hn : n ∈ l := h n (by omega)
    have := ih (l.erase n) (fun i hi => (List.mem_erase_of_ne (by omega)).2 (h i (by omega)))
    have h2 := List.length_erase_of_mem hn
    have : 0 < l.length := List.length_pos_of_mem hn
    omega

theorem mex_spec (l : List Nat) : (∀ m < mex l, m ∈ l) ∧ mex l ∉ l := by
  unfold mex
  have hex : ∃ m, (List.range (l.length + 1)).find? (fun m => !l.contains m) = some m := by
    cases h : (List.range (l.length + 1)).find? (fun m => !l.contains m) with
    | some m => exact ⟨m, rfl⟩
    | none =>
      exfalso
      have hn := List.find?_eq_none.1 h
      have := pigeon (l.length + 1) l (fun i hi => by
        have := hn i (List.mem_range.2 hi)
        simpa using this)
      omega
  obtain ⟨m, hm⟩ := hex
  rw [hm]
  obtain ⟨h1, h2⟩ := find_range _ _ _ hm
  refine ⟨fun k hk => ?_, ?_⟩
  · have := h2 k hk; simpa using this
  · simpa using h1

/-- The Sprague-Grundy value of one heap of Sub(S). -/
def sgFn (S : List Nat) : Nat → Nat
  | x => mex (S.filterMap fun s => if h : 0 < s ∧ s ≤ x then some (sgFn S (x - s)) else none)
termination_by x => x
decreasing_by omega

theorem mem_moves (S : List Nat) (x m : Nat) :
    m ∈ (S.filterMap fun s => if h : 0 < s ∧ s ≤ x then some (sgFn S (x - s)) else none) ↔
      ∃ s ∈ S, 0 < s ∧ s ≤ x ∧ sgFn S (x - s) = m := by
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, h⟩
    split at h
    · rename_i hh; simp at h; exact ⟨s, hs, hh.1, hh.2, h⟩
    · simp at h
  · rintro ⟨s, hs, h0, h1, h2⟩
    exact ⟨s, hs, by simp [h0, h1, h2]⟩

theorem sgFn_eq (S : List Nat) (x : Nat) : sgFn S x = mex (S.filterMap fun s => if h : 0 < s ∧ s ≤ x then some (sgFn S (x - s)) else none) := by
  rw [sgFn]

theorem sgFn_lt (S : List Nat) (x m : Nat) (h : m < sgFn S x) : ∃ s ∈ S, 0 < s ∧ s ≤ x ∧ sgFn S (x - s) = m := by
  rw [sgFn_eq] at h
  exact (mem_moves S x m).1 ((mex_spec _).1 m h)

theorem sgFn_ne (S : List Nat) (x s : Nat) (hs : s ∈ S) (h0 : 0 < s) (h1 : s ≤ x) : sgFn S (x - s) ≠ sgFn S x := by
  intro h
  have := (mex_spec (S.filterMap fun s => if h : 0 < s ∧ s ≤ x then some (sgFn S (x - s)) else none)).2
  rw [← sgFn_eq] at this
  exact this ((mem_moves S x _).2 ⟨s, hs, h0, h1, h⟩)

theorem IsP1_iff_sg (S : List Nat) : ∀ n a b, a + b = n → (IsP1 S a b ↔ sgFn S a = sgFn S b) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro a b hn
  rw [IsP1]
  have iha : ∀ s, 0 < s → s ≤ a → (IsP1 S (a - s) b ↔ sgFn S (a - s) = sgFn S b) :=
    fun s h0 h1 => ih _ (by omega) _ _ rfl
  have ihb : ∀ s, 0 < s → s ≤ b → (IsP1 S a (b - s) ↔ sgFn S a = sgFn S (b - s)) :=
    fun s h0 h1 => ih _ (by omega) _ _ rfl
  constructor
  · rintro ⟨hA, hB⟩
    refine Classical.byContradiction fun hne => ?_
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨s, hs, h0, h1, h2⟩ := sgFn_lt S b _ hlt
      exact hB s hs h0 h1 ((ihb s h0 h1).2 h2.symm)
    · obtain ⟨s, hs, h0, h1, h2⟩ := sgFn_lt S a _ hgt
      exact hA s hs h0 h1 ((iha s h0 h1).2 h2)
  · intro h
    refine ⟨fun s hs h0 h1 hp => ?_, fun s hs h0 h1 hp => ?_⟩
    · exact sgFn_ne S a s hs h0 h1 (((iha s h0 h1).1 hp).trans h.symm)
    · exact sgFn_ne S b s hs h0 h1 (((ihb s h0 h1).1 hp).symm.trans h)

theorem filterMap_congr' {α β : Type} (f g : α → Option β) (l : List α) (h : ∀ x ∈ l, f x = g x) :
    l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.filterMap_cons]
    rw [h y (List.mem_cons_self), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem getD_of_eq_map (f : Nat → Nat) (l : List Nat) (hl : l = (List.range l.length).map f)
    (i : Nat) (hi : i < l.length) : l.getD i 0 = f i := by
  have := congrArg (fun m => m.getD i 0) hl
  rw [this]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi]

theorem sgBuild_eq (S : List Nat) (hS : ∀ s ∈ S, 0 < s) :
    ∀ fuel acc, acc = (List.range acc.length).map (sgFn S) →
      sgBuild S fuel acc = (List.range (acc.length + fuel)).map (sgFn S) := by
  intro fuel
  induction fuel with
  | zero => intro acc h; simpa [sgBuild] using h
  | succ f ih =>
    intro acc h
    have hk : (mex (S.filterMap fun s =>
        if s ≤ acc.length then some (acc.getD (acc.length - s) 0) else none)) = sgFn S acc.length := by
      rw [sgFn_eq]
      congr 1
      apply filterMap_congr'
      intro s hs
      have h0 := hS s hs
      by_cases hsk : s ≤ acc.length
      · have : acc.getD (acc.length - s) 0 = sgFn S (acc.length - s) :=
          getD_of_eq_map _ acc h _ (by omega)
        simp [hsk, h0]; rw [← List.getD_eq_getElem?_getD]; exact this
      · simp [hsk]
    rw [sgBuild, hk]
    have := ih (acc ++ [sgFn S acc.length]) (by
      simp only [List.length_append, List.length_singleton]
      conv => lhs; rw [h]
      rw [List.range_succ]; simp)
    rw [this]
    simp only [List.length_append, List.length_singleton]
    congr 2; omega

theorem sgList_eq (S : List Nat) (hS : ∀ s ∈ S, 0 < s) (n : Nat) :
    sgList S n = (List.range n).map (sgFn S) := by
  unfold sgList; simpa using sgBuild_eq S hS n [] rfl

theorem sgList_getD (S : List Nat) (hS : ∀ s ∈ S, 0 < s) (n x : Nat) (h : x < n) :
    (sgList S n).getD x 0 = sgFn S x := by
  rw [sgList_eq S hS]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h]

theorem foldl_max_ge (l : List Nat) : ∀ init, init ≤ l.foldl max init := by
  induction l with
  | nil => simp
  | cons y l ih => intro init; simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem le_foldl_max (l : List Nat) : ∀ init x, x ∈ l → x ≤ l.foldl max init := by
  induction l with
  | nil => simp
  | cons y l ih =>
    intro init x hx
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · have : x ≤ max init x := Nat.le_max_right _ _
      have := foldl_max_ge l (max init x)
      omega
    · exact ih _ _ hx


theorem gOk_sound (S2 : List Nat) (gpre gper : Nat) (h : gOk S2 gpre gper = true) :
    0 < gper ∧ (∀ s ∈ S2, 0 < s) ∧ ∀ x, gpre ≤ x → sgFn S2 (x + gper) = sgFn S2 x := by
  unfold gOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨hper, hM⟩, hpos⟩, hwin⟩ := h
  have hpos' : ∀ s ∈ S2, 0 < s := fun s hs => by simpa using hpos s hs
  refine ⟨hper, hpos', ?_⟩
  have win : ∀ i, i < S2.foldl max 0 → sgFn S2 (gpre + i + gper) = sgFn S2 (gpre + i) := by
    intro i hi
    have := hwin i hi
    rw [sgList_getD S2 hpos' _ _ (by omega), sgList_getD S2 hpos' _ _ (by omega)] at this
    have e : gpre + i + gper = gpre + gper + i := by omega
    rw [e]; exact this.symm
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
  intro hx
  by_cases hxw : x < gpre + S2.foldl max 0
  · have := win (x - gpre) (by omega)
    have e : gpre + (x - gpre) = x := by omega
    rwa [e] at this
  · rw [sgFn_eq S2 x, sgFn_eq S2 (x + gper)]
    congr 1
    apply filterMap_congr'
    intro s hs
    have h0 := hpos' s hs
    have h1 : s ≤ S2.foldl max 0 := le_foldl_max S2 0 s hs
    have h2 : s ≤ x := by omega
    have h3 : s ≤ x + gper := by omega
    simp only [h0, h1, h2, h3, true_and, dif_pos]
    have := ih (x - s) (by omega) (by omega)
    have e : x + gper - s = x - s + gper := by omega
    rw [e, this]

theorem sgFn_periodic (S : List Nat) (gpre gper : Nat) (h : ∀ x, gpre ≤ x → sgFn S (x + gper) = sgFn S x) :
    ∀ k x, gpre ≤ x → sgFn S (x + k * gper) = sgFn S x := by
  intro k
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    have e : x + (k + 1) * gper = (x + k * gper) + gper := by rw [Nat.succ_mul]; omega
    rw [e, h _ (by omega), ih x hx]

theorem gval_eq (S2 : List Nat) (gpre gper : Nat) (h : gOk S2 gpre gper = true) (x : Nat) :
    gval (sgList S2 (gpre + gper)) gpre gper x = sgFn S2 x := by
  obtain ⟨hper, hpos, hp⟩ := gOk_sound S2 gpre gper h
  unfold gval
  by_cases hx : x < gpre + gper
  · simp only [hx, ↓reduceIte]; exact sgList_getD S2 hpos _ _ hx
  · simp only [hx, ↓reduceIte]
    have hm : (x - gpre) % gper < gper := Nat.mod_lt _ hper
    rw [sgList_getD S2 hpos _ _ (by omega)]
    have := sgFn_periodic S2 gpre gper hp ((x - gpre) / gper) (gpre + (x - gpre) % gper) (by omega)
    rw [← this]
    congr 1
    have := Nat.mod_add_div (x - gpre) gper
    have : (x - gpre) / gper * gper = gper * ((x - gpre) / gper) := Nat.mul_comm _ _
    omega

/-- The game equation for `outcome`, with the push replaced by the Sprague-Grundy test. -/
theorem outcome_eq (S1 S2 : List Nat) (a b : Nat) :
    outcome S1 S2 a b = true ↔ sgFn S2 a ≠ sgFn S2 b ∧
      (∀ s ∈ S1, 0 < s → s ≤ a → outcome S1 S2 (a - s) b = false) ∧
      (∀ s ∈ S1, 0 < s → s ≤ b → outcome S1 S2 a (b - s) = false) := by
  rw [outcome_iff, IsP0]
  have e := IsP1_iff_sg S2 (a + b) a b rfl
  simp only [← outcome_iff, Bool.eq_false_iff, ne_eq]
  rw [e]

theorem cell_iff (S1 : List Nat) (gl : List Nat) (gpre gper : Nat) (rows : List Row) (a : Nat)
    (r : List Bool) (d : Nat) :
    cell S1 gl gpre gper rows a r d = true ↔
      gval gl gpre gper a ≠ gval gl gpre gper (a + d) ∧ ∀ s ∈ S1,
        ¬ ((s ≤ a ∧ (rowAt rows (a - s)).at (d + s) = true) ∨
           (s ≤ a + d ∧ (if s ≤ d then r.getD (d - s) false
              else (rowAt rows (a + d - s)).at (s - d)) = true)) := by
  unfold cell
  by_cases h : gval gl gpre gper a = gval gl gpre gper (a + d)
  · simp [h]
  · have hb : (gval gl gpre gper a == gval gl gpre gper (a + d)) = false := by simpa using h
    simp only [hb, Bool.false_eq_true, ↓reduceIte, h, ne_eq, not_false_eq_true, true_and]
    rw [Bool.not_eq_true', ← Bool.not_eq_true (S1.any _), List.any_eq_true]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_exists, not_and]

/-- The row recursion `cell` evaluated on the true row prefix gives the true cell. -/
theorem cell_true (S1 S2 : List Nat) (gl : List Nat) (gpre gper : Nat) (rows : List Row) (a : Nat)
    (hS1 : ∀ s ∈ S1, 0 < s) (hg : ∀ x, gval gl gpre gper x = sgFn S2 x)
    (hprev : ∀ i < a, ∀ d, (rowAt rows i).at d = outcome S1 S2 i (i + d)) (d : Nat) :
    cell S1 gl gpre gper rows a ((List.range d).map fun e => outcome S1 S2 a (a + e)) d =
      outcome S1 S2 a (a + d) := by
  rw [Bool.eq_iff_iff, cell_iff, outcome_eq]
  simp only [hg]
  have X1 : ∀ s, 0 < s → s ≤ a → (rowAt rows (a - s)).at (d + s) = outcome S1 S2 (a - s) (a + d) := by
    intro s h0 h1
    rw [hprev (a - s) (by omega)]
    congr 1; omega
  have X2 : ∀ s, 0 < s → s ≤ a + d →
      (if s ≤ d then (((List.range d).map fun e => outcome S1 S2 a (a + e))).getD (d - s) false
        else (rowAt rows (a + d - s)).at (s - d)) = outcome S1 S2 a (a + d - s) := by
    intro s h0 h1
    split
    · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, show d - s < d by omega]
      congr 1; omega
    · rw [hprev (a + d - s) (by omega), outcome_symm]
      congr 1; omega
  refine and_congr_right fun _ => ?_
  constructor
  · intro H
    refine ⟨fun s hs h0 hsa => ?_, fun s hs h0 hsb => ?_⟩
    · cases ho : outcome S1 S2 (a - s) (a + d)
      · rfl
      · exact absurd (Or.inl ⟨hsa, by rw [X1 s h0 hsa]; exact ho⟩) (H s hs)
    · cases ho : outcome S1 S2 a (a + d - s)
      · rfl
      · exact absurd (Or.inr ⟨hsb, by rw [X2 s h0 hsb]; exact ho⟩) (H s hs)
  · rintro ⟨H1, H2⟩ s hs (⟨hsa, h⟩ | ⟨hsb, h⟩)
    · rw [X1 s (hS1 s hs) hsa, H1 s hs (hS1 s hs) hsa] at h; exact Bool.false_ne_true h
    · rw [X2 s (hS1 s hs) hsb, H2 s hs (hS1 s hs) hsb] at h; exact Bool.false_ne_true h

theorem sim_tr (S1 : List Nat) (gl : List Nat) (gpre gper : Nat) (rows : List Row) (a : Nat)
    (tr : Nat → Bool)
    (hcell : ∀ d, cell S1 gl gpre gper rows a ((List.range d).map tr) d = tr d) :
    ∀ n k, sim S1 gl gpre gper rows a n ((List.range k).map tr) = (List.range (k + n)).map tr := by
  intro n
  induction n with
  | zero => intro k; simp [sim]
  | succ n ih =>
    intro k
    rw [sim]
    have : (List.range k).map tr ++ [cell S1 gl gpre gper rows a ((List.range k).map tr)
        ((List.range k).map tr).length] = (List.range (k + 1)).map tr := by
      rw [List.length_map, List.length_range, hcell k, List.range_succ, List.map_append]; rfl
    rw [this, ih]
    congr 2; omega

theorem Row.at_add (R : Row) (hc : 0 < R.cyc.length) {k : Nat} (hk : R.cyc.length ∣ k) (x : Nat)
    (hx : R.pre.length ≤ x) : R.at (x + k) = R.at x := by
  unfold Row.at
  have h1 : ¬ (x + k < R.pre.length) := by omega
  have h2 : ¬ (x < R.pre.length) := by omega
  simp only [h1, h2, if_false]
  congr 1
  obtain ⟨m, rfl⟩ := hk
  have : x + R.cyc.length * m - R.pre.length = (x - R.pre.length) + R.cyc.length * m := by omega
  rw [this, Nat.add_mul_mod_self_left]

theorem tr_period (S1 : List Nat) (M K d1 : Nat) (tr : Nat → Bool) (P : Nat → Prop)
    (Y : Nat → Nat → Prop) (hM : ∀ s ∈ S1, 0 < s ∧ s ≤ M) (hd1 : M ≤ d1)
    (hstep : ∀ d, M ≤ d → (tr d = true ↔ P d ∧ ∀ s ∈ S1, ¬ Y s d ∧ tr (d - s) = false))
    (hP : ∀ d, d1 ≤ d → (P (d + K) ↔ P d))
    (hY : ∀ s ∈ S1, ∀ d, d1 ≤ d → (Y s (d + K) ↔ Y s d))
    (hwin : ∀ i < M, tr (d1 - M + i) = tr (d1 - M + i + K)) :
    ∀ e, d1 - M ≤ e → tr (e + K) = tr e := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
  intro he
  by_cases hed : e < d1
  · have := hwin (e - (d1 - M)) (by omega)
    have e1 : d1 - M + (e - (d1 - M)) = e := by omega
    rw [e1] at this; exact this.symm
  · rw [Bool.eq_iff_iff, hstep (e + K) (by omega), hstep e (by omega), hP e (by omega)]
    refine and_congr_right fun _ => forall_congr' fun s => imp_congr_right fun hs => ?_
    obtain ⟨h0, h1⟩ := hM s hs
    have e2 : e + K - s = (e - s) + K := by omega
    rw [e2, ih (e - s) (by omega) (by omega), hY s hs e (by omega)]

theorem tr_eq_row (R : Row) (tr : Nat → Bool) (K d1 M : Nat) (hc : 0 < R.cyc.length)
    (hK : R.cyc.length ∣ K) (hK0 : 0 < K) (hd1 : R.pre.length + M ≤ d1)
    (hmatch : ∀ d < d1 + K, tr d = R.at d) (hper : ∀ e, d1 - M ≤ e → tr (e + K) = tr e) :
    ∀ d, tr d = R.at d := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  by_cases hd : d < d1 + K
  · exact hmatch d hd
  · have e1 : d = (d - K) + K := by omega
    rw [e1, hper (d - K) (by omega), ih (d - K) (by omega)]
    exact (Row.at_add R hc hK (d - K) (by omega)).symm

theorem lcm_fold (xs : List Nat) : ∀ init, init ∣ xs.foldl Nat.lcm init ∧ ∀ x ∈ xs, x ∣ xs.foldl Nat.lcm init := by
  induction xs with
  | nil => intro init; simp
  | cons y xs ih =>
    intro init
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (Nat.lcm init y)
    refine ⟨Nat.dvd_trans (Nat.dvd_lcm_left _ _) h1, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.dvd_trans (Nat.dvd_lcm_right _ _) h1
    · exact h2 x hx


theorem lcm_fold_pos (xs : List Nat) (hx : ∀ x ∈ xs, 0 < x) :
    ∀ init, 0 < init → 0 < xs.foldl Nat.lcm init := by
  induction xs with
  | nil => intro init h; simpa using h
  | cons y xs ih =>
    intro init h
    simp only [List.foldl_cons]
    exact ih (fun x hx' => hx x (List.mem_cons_of_mem _ hx')) _
      (Nat.lcm_pos h (hx y List.mem_cons_self))

/-- A row that passes `rowOk` is the true row `d -> outcome a (a + d)`, given the earlier rows. -/
theorem row_sound (S1 S2 : List Nat) (gl : List Nat) (gpre gper : Nat) (rows : List Row) (a : Nat)
    (hS1 : ∀ s ∈ S1, 0 < s) (hg : ∀ x, gval gl gpre gper x = sgFn S2 x) (hgper : 0 < gper)
    (hp : ∀ x, gpre ≤ x → sgFn S2 (x + gper) = sgFn S2 x)
    (hprev : ∀ i < a, ∀ d, (rowAt rows i).at d = outcome S1 S2 i (i + d))
    (hrow : rowOk S1 gl gpre gper rows a = true) :
    ∀ d, (rowAt rows a).at d = outcome S1 S2 a (a + d) := by
  unfold rowOk at hrow
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at hrow
  obtain ⟨⟨⟨hc0, hins⟩, hmatch⟩, hwin⟩ := hrow
  generalize hMdef : S1.foldl max 0 = M at hmatch hwin
  generalize hinsdef : ((S1.filter fun s => decide (s ≤ a)).map fun s => rowAt rows (a - s)) = ins
    at hins hmatch hwin
  generalize hD0def : (ins.map (fun x => x.pre.length) ++ [gpre, M]).foldl max 0 + M = D0
    at hmatch hwin
  generalize hLdef : ((ins.map fun x => x.cyc.length) ++ [gper]).foldl Nat.lcm 1 = L at hmatch hwin
  generalize hRdef : rowAt rows a = R at hc0 hmatch hwin ⊢
  generalize hd1def : max D0 (R.pre.length + M) = d1 at hmatch hwin
  generalize hKdef : R.cyc.length.lcm L = K at hmatch hwin
  let tr : Nat → Bool := fun d => outcome S1 S2 a (a + d)
  have htr : ∀ d, tr d = outcome S1 S2 a (a + d) := fun _ => rfl
  have hM : ∀ s ∈ S1, 0 < s ∧ s ≤ M := fun s hs => ⟨hS1 s hs, hMdef ▸ le_foldl_max S1 0 s hs⟩
  have hinsmem : ∀ s ∈ S1, s ≤ a → rowAt rows (a - s) ∈ ins := by
    intro s hs hsa
    rw [← hinsdef]
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨s, ⟨hs, hsa⟩, rfl⟩
  have hDpre : ∀ s ∈ S1, s ≤ a → (rowAt rows (a - s)).pre.length + M ≤ D0 := by
    intro s hs hsa
    have := le_foldl_max (ins.map (fun x => x.pre.length) ++ [gpre, M]) 0
      (rowAt rows (a - s)).pre.length (by
        simp only [List.mem_append, List.mem_map]; exact Or.inl ⟨_, hinsmem s hs hsa, rfl⟩)
    omega
  have hDg : gpre + M ≤ D0 := by
    have := le_foldl_max (ins.map (fun x => x.pre.length) ++ [gpre, M]) 0 gpre (by simp)
    omega
  have hDM : M ≤ D0 := by omega
  have hL := lcm_fold ((ins.map fun x => x.cyc.length) ++ [gper]) 1
  rw [hLdef] at hL
  have hLpos : 0 < L := hLdef ▸ lcm_fold_pos _ (by
    intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl
    · exact hins y hy
    · exact hgper) 1 (by omega)
  have hKpos : 0 < K := hKdef ▸ Nat.lcm_pos hc0 hLpos
  have hRK : R.cyc.length ∣ K := hKdef ▸ Nat.dvd_lcm_left _ _
  have hLK : L ∣ K := hKdef ▸ Nat.dvd_lcm_right _ _
  have hgK : gper ∣ K := Nat.dvd_trans (hL.2 gper (by simp)) hLK
  have hcycK : ∀ s ∈ S1, s ≤ a → (rowAt rows (a - s)).cyc.length ∣ K := by
    intro s hs hsa
    exact Nat.dvd_trans (hL.2 _ (by
      simp only [List.mem_append, List.mem_map]; exact Or.inl ⟨_, hinsmem s hs hsa, rfl⟩)) hLK
  have hd1D : D0 ≤ d1 := hd1def ▸ Nat.le_max_left _ _
  have hd1R : R.pre.length + M ≤ d1 := hd1def ▸ Nat.le_max_right _ _
  -- the true row satisfies the recursion
  have hcell := cell_true S1 S2 gl gpre gper rows a hS1 hg hprev
  have hsim := sim_tr S1 gl gpre gper rows a tr hcell (d1 + K) 0
  simp only [List.range_zero, List.map_nil, Nat.zero_add] at hsim
  have hr : ∀ x, x < d1 + K → (sim S1 gl gpre gper rows a (d1 + K) []).getD x false = tr x := by
    intro x hx
    rw [hsim]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hx]
  have hstep : ∀ d, M ≤ d → (tr d = true ↔ sgFn S2 a ≠ sgFn S2 (a + d) ∧ ∀ s ∈ S1,
      ¬ (s ≤ a ∧ (rowAt rows (a - s)).at (d + s) = true) ∧ tr (d - s) = false) := by
    intro d hd
    rw [htr, outcome_eq]
    refine and_congr Iff.rfl ?_
    constructor
    · rintro ⟨H1, H2⟩ s hs
      obtain ⟨h0, h1⟩ := hM s hs
      refine ⟨fun ⟨hsa, hh⟩ => ?_, ?_⟩
      · rw [hprev (a - s) (by omega), show a - s + (d + s) = a + d by omega,
          H1 s hs h0 hsa] at hh
        exact Bool.false_ne_true hh
      · have := H2 s hs h0 (by omega)
        simpa [htr, show a + d - s = a + (d - s) by omega] using this
    · intro H
      refine ⟨fun s hs h0 hsa => ?_, fun s hs h0 hsb => ?_⟩
      · have := (H s hs).1
        rw [hprev (a - s) (by omega), show a - s + (d + s) = a + d by omega] at this
        cases h : outcome S1 S2 (a - s) (a + d)
        · rfl
        · exact absurd ⟨hsa, h⟩ this
      · have := (H s hs).2
        have h1 := (hM s hs).2
        simpa [htr, show a + d - s = a + (d - s) by omega] using this
  have hper := tr_period S1 M K d1 tr (fun d => sgFn S2 a ≠ sgFn S2 (a + d))
    (fun s d => s ≤ a ∧ (rowAt rows (a - s)).at (d + s) = true) hM (by omega) hstep
    (by
      intro d hd
      obtain ⟨k, hk⟩ := hgK
      have := sgFn_periodic S2 gpre gper hp k (a + d) (by omega)
      show sgFn S2 a ≠ sgFn S2 (a + (d + K)) ↔ _
      rw [show a + (d + K) = a + d + k * gper by rw [hk]; rw [Nat.mul_comm]; omega, this])
    (by
      intro s hs d hd
      refine and_congr_right fun hsa => ?_
      have e : d + K + s = (d + s) + K := by omega
      have := hDpre s hs hsa
      show (rowAt rows (a - s)).at (d + K + s) = true ↔ (rowAt rows (a - s)).at (d + s) = true
      rw [e, Row.at_add _ (hins _ (hinsmem s hs hsa)) (hcycK s hs hsa) (d + s) (by omega)])
    (by
      intro i hi
      have h1 := hwin i hi
      have e1 := hr (d1 - M + i) (by omega)
      have e2 := hr (d1 + K - M + i) (by omega)
      rw [e1, e2] at h1
      rw [h1]; congr 1; omega)
  have := tr_eq_row R tr K d1 M hc0 hRK hKpos hd1R
    (fun d hd => by rw [← hr d hd]; exact hmatch d hd) hper
  exact fun d => (this d).symm


/-- All listed rows are the true rows. -/
theorem rows_correct (S1 S2 : List Nat) (gl : List Nat) (gpre gper : Nat) (rows : List Row)
    (hS1 : ∀ s ∈ S1, 0 < s) (hg : ∀ x, gval gl gpre gper x = sgFn S2 x) (hgper : 0 < gper)
    (hp : ∀ x, gpre ≤ x → sgFn S2 (x + gper) = sgFn S2 x)
    (hrows : ∀ x < rows.length, rowOk S1 gl gpre gper rows x = true) :
    ∀ i < rows.length, ∀ d, (rowAt rows i).at d = outcome S1 S2 i (i + d) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro hi
  exact row_sound S1 S2 gl gpre gper rows i hS1 hg hgper hp (fun j hj => ih j hj (by omega))
    (hrows i hi)

/-- Window repeat: if rows A0 .. a0 + M - 1 repeat with shift q (q a multiple of the period of g,
a0 >= M + gpre), then every row a >= A0 repeats with shift q. -/
theorem window_repeat (S1 S2 : List Nat) (gpre gper q A0 a0 M : Nat)
    (hS1 : ∀ s ∈ S1, 0 < s ∧ s ≤ M) (hper : ∀ x, gpre ≤ x → sgFn S2 (x + gper) = sgFn S2 x)
    (hgq : gper ∣ q) (ha0 : M + gpre ≤ a0) (hA0 : A0 ≤ a0)
    (hbase : ∀ a, A0 ≤ a → a < a0 + M → ∀ d,
      outcome S1 S2 (a + q) (a + q + d) = outcome S1 S2 a (a + d)) :
    ∀ a, A0 ≤ a → ∀ d, outcome S1 S2 (a + q) (a + q + d) = outcome S1 S2 a (a + d) := by
  have hsg : ∀ x, gpre ≤ x → sgFn S2 (x + q) = sgFn S2 x := by
    obtain ⟨k, hk⟩ := hgq
    intro x hx
    have := sgFn_periodic S2 gpre gper hper k x hx
    rw [hk, Nat.mul_comm]; exact this
  intro a
  induction a using Nat.strongRecOn with
  | _ a iha =>
  intro hA d
  by_cases hlt : a < a0 + M
  · exact hbase a hA hlt d
  · induction d using Nat.strongRecOn with
    | _ d ihd =>
    rw [Bool.eq_iff_iff, outcome_eq, outcome_eq]
    refine and_congr ?_ (and_congr ?_ ?_)
    · rw [hsg a (by omega), show a + q + d = (a + d) + q by omega, hsg (a + d) (by omega)]
    · refine forall_congr' fun s => forall_congr' fun hs => forall_congr' fun h0 => ?_
      have := hS1 s hs
      rw [imp_iff_right (show s ≤ a + q by omega), imp_iff_right (show s ≤ a by omega)]
      have key : outcome S1 S2 (a + q - s) (a + q + d) = outcome S1 S2 (a - s) (a + d) := by
        have := iha (a - s) (by omega) (by omega) (d + s)
        rw [show a - s + q = a + q - s by omega, show a + q - s + (d + s) = a + q + d by omega,
          show a - s + (d + s) = a + d by omega] at this
        exact this
      rw [key]
    · refine forall_congr' fun s => forall_congr' fun hs => forall_congr' fun h0 => ?_
      have := hS1 s hs
      rw [imp_iff_right (show s ≤ a + q + d by omega), imp_iff_right (show s ≤ a + d by omega)]
      have key : outcome S1 S2 (a + q) (a + q + d - s) = outcome S1 S2 a (a + d - s) := by
        by_cases hsd : s ≤ d
        · have := ihd (d - s) (by omega)
          rw [show a + q + (d - s) = a + q + d - s by omega,
            show a + (d - s) = a + d - s by omega] at this
          exact this
        · rw [outcome_symm S1 S2 (a + q) (a + q + d - s), outcome_symm S1 S2 a (a + d - s)]
          have := iha (a + d - s) (by omega) (by omega) (s - d)
          rw [show a + d - s + q = a + q + d - s by omega,
            show a + q + d - s + (s - d) = a + q by omega,
            show a + d - s + (s - d) = a by omega] at this
          exact this
      rw [key]

theorem window_iter (S1 S2 : List Nat) (q A0 : Nat)
    (hW : ∀ a, A0 ≤ a → ∀ d, outcome S1 S2 (a + q) (a + q + d) = outcome S1 S2 a (a + d)) :
    ∀ k a', A0 ≤ a' → ∀ d,
      outcome S1 S2 (a' + k * q) (a' + k * q + d) = outcome S1 S2 a' (a' + d) := by
  intro k
  induction k with
  | zero => intro a' _ d; simp
  | succ k ih =>
    intro a' ha' d
    have e : a' + (k + 1) * q = (a' + k * q) + q := by rw [Nat.succ_mul]; omega
    rw [e, hW _ (by omega) d, ih a' ha' d]

theorem Row.beq_eq (x y : Row) (h : (x == y) = true) : x = y := by
  obtain ⟨p1, c1⟩ := x
  obtain ⟨p2, c2⟩ := y
  have h' : (p1 == p2 && c1 == c2) = true := h
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  rw [h'.1, h'.2]

/-- Soundness of the checker: a certificate that passes implies the two-heap outcome of
Sub(S1) -> Sub(S2) is eventually doubly periodic with the certified A0, q, T, p. -/
theorem checkCert_sound (S1 S2 : List Nat) (c : Cert) (h : checkCert S1 S2 c = true) :
    0 < c.q ∧ 0 < c.p ∧
    (∀ a, c.A0 ≤ a → ∀ d, outcome S1 S2 (a + c.q) (a + c.q + d) = outcome S1 S2 a (a + d)) ∧
    (∀ a, c.A0 ≤ a → ∀ d, c.T ≤ d → outcome S1 S2 a (a + d + c.p) = outcome S1 S2 a (a + d)) := by
  unfold checkCert at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hS1, hM0⟩, hgOk⟩, hlen⟩, hrows⟩, hq⟩, hqg⟩, ha0⟩, hA0⟩, hwinR⟩, hb⟩ := h
  generalize hMdef : S1.foldl max 0 = M at hlen ha0 hwinR
  have hMb : ∀ s ∈ S1, 0 < s ∧ s ≤ M := fun s hs => ⟨hS1 s hs, hMdef ▸ le_foldl_max S1 0 s hs⟩
  obtain ⟨hgper, -, hp⟩ := gOk_sound S2 c.gpre c.gper hgOk
  have hg := gval_eq S2 c.gpre c.gper hgOk
  have hcor := rows_correct S1 S2 _ c.gpre c.gper c.rows hS1 hg hgper hp hrows
  have hW := window_repeat S1 S2 c.gpre c.gper c.q c.A0 c.a0 M hMb hp
    (Nat.dvd_of_mod_eq_zero hqg) ha0 hA0 (by
      intro a hA hlt d
      have hx := hwinR (a - c.A0) (by omega)
      rw [show c.A0 + (a - c.A0) = a by omega] at hx
      have he := Row.beq_eq _ _ hx
      have h1 := hcor a (by omega) d
      have h2 := hcor (a + c.q) (by omega) d
      rw [he] at h1
      rw [← h1, ← h2])
  unfold boundsOk at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hb
  obtain ⟨hp0, hb⟩ := hb
  refine ⟨hq, hp0, hW, ?_⟩
  intro a hA d hd
  have hmod : (a - c.A0) % c.q < c.q := Nat.mod_lt _ hq
  obtain ⟨hpre, hpm⟩ := hb _ hmod
  have hdecomp : a = (c.A0 + (a - c.A0) % c.q) + (a - c.A0) / c.q * c.q := by
    have := Nat.mod_add_div (a - c.A0) c.q
    have := Nat.mul_comm c.q ((a - c.A0) / c.q)
    omega
  have hall : ∀ e, outcome S1 S2 a (a + e) =
      outcome S1 S2 (c.A0 + (a - c.A0) % c.q) (c.A0 + (a - c.A0) % c.q + e) := by
    intro e
    have := window_iter S1 S2 c.q c.A0 hW ((a - c.A0) / c.q) (c.A0 + (a - c.A0) % c.q) (by omega) e
    rw [← hdecomp] at this
    exact this
  have hidx : c.A0 + (a - c.A0) % c.q < c.rows.length := by omega
  have hrow := hcor _ hidx
  have hcpos : 0 < (rowAt c.rows (c.A0 + (a - c.A0) % c.q)).cyc.length := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, Nat.mod_zero] at hpm
    omega
  rw [show a + d + c.p = a + (d + c.p) by omega, hall (d + c.p), hall d, ← hrow, ← hrow]
  exact Row.at_add _ hcpos (Nat.dvd_of_mod_eq_zero hpm) d (by omega)

end LeadA
