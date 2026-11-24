import FamilyWall
/-!
Phases of one round (symbolic in the class index `j`): runs of rows with affine counters, the
iteration lemma for cycles, the row-tag check and the wall checks of every row.

* `runBody`: a list of rows (one `step`, or the `len` rows of one cycle iteration) on counters
  `a*j + e*t + b`; each row checks its tag representative (`tagOk`), runs `symRow` and checks the wall
  position bound (`wallOk`); the very first row of a round also checks the exact onset (`wallEx`).
* `runPhase`/`runPhases`: `step` and `cycle` phases; the cycle must return to its shape with the
  counters moved by the constant `d`.
-/
namespace Family

structure Env where
  S1 : List Nat
  gpre : List Nat
  gper : List Nat
  π : Nat
  P : Int × Int      -- affine bound `w_k + c` on the wall position of every row
  P0 : Int × Int     -- affine exact wall position `w_k` of the first row
  Tm : Nat → Nat     -- first row `t_k` of the round of class index `j`

inductive PhaseC
  | step (rt : Nat) (mv : List Move)
  | cycle (len : Nat) (ca cb : Int) (d : List Int) (rts : List Nat) (mvs : List (List Move))

/-! ### Row index and its tag -/

/-- row index of step `si` of iteration `t`: `t_k + off + t*len + si` -/
def xval (Tm : Nat → Nat) (off : Int × Int) (len si j t : Nat) : Nat :=
  ((Tm j : Int) + (off.1 * j + off.2) + si + t * len).toNat

def rowAt (Tm : Nat → Nat) (off : Int × Int) (j : Nat) : Nat :=
  ((Tm j : Int) + (off.1 * j + off.2)).toNat

theorem xval_int (Tm : Nat → Nat) {off : Int × Int} (len si j t : Nat) (h : 0 ≤ off.1 * j + off.2) :
    (xval Tm off len si j t : Int) = Tm j + (off.1 * j + off.2) + si + t * len := by
  unfold xval
  have : 0 ≤ (t : Int) * len := Int.mul_nonneg (by omega) (by omega)
  omega

theorem xval_zero (Tm : Nat → Nat) {off : Int × Int} (len j : Nat) (h : 0 ≤ off.1 * j + off.2) :
    xval Tm off len 0 j 0 = rowAt Tm off j := by
  unfold xval rowAt; simp

theorem xval_succ (Tm : Nat → Nat) {off : Int × Int} (len si j t : Nat) (h : 0 ≤ off.1 * j + off.2) :
    xval Tm off len (si + 1) j t = xval Tm off len si j t + 1 := by
  have h1 := xval_int Tm (off := off) len (si + 1) j t h
  have h2 := xval_int Tm (off := off) len si j t h
  push_cast at h1
  omega

theorem xval_iter (Tm : Nat → Nat) {off : Int × Int} (len si j t : Nat) (h : 0 ≤ off.1 * j + off.2) :
    xval Tm off len (si + len) j t = xval Tm off len si j (t + 1) := by
  have h1 := xval_int Tm (off := off) len (si + len) j t h
  have h2 := xval_int Tm (off := off) len si j (t + 1) h
  push_cast at h1 h2
  have : ((t : Int) + 1) * len = t * len + len := by grind
  omega

theorem xval_ge (Tm : Nat → Nat) {off : Int × Int} (len si j t : Nat) (h : 0 ≤ off.1 * j + off.2) :
    Tm j ≤ xval Tm off len si j t := by
  have h1 := xval_int Tm (off := off) len si j t h
  have : 0 ≤ (t : Int) * len := Int.mul_nonneg (by omega) (by omega)
  omega

def tagOk (env : Env) (j0 : Nat) (off : Int × Int) (len si : Nat) (cyc : Bool) (rt : Nat) : Bool :=
  (List.range (2 * env.gper.length)).all fun u =>
    (List.range (if cyc then env.gper.length else 1)).all fun t =>
      eqTags env.gpre env.gper (xval env.Tm off len si (j0 + u) t) rt

theorem tagOk_sound (env : Env) (hp : 0 < env.gper.length) (j0 : Nat)
    (hTper : ∀ j, j0 ≤ j → ∀ m, (env.gper.length : Int) ∣ (env.Tm (j + 2 * env.gper.length * m) : Int) - env.Tm j)
    (hTge : ∀ j, j0 ≤ j → env.gpre.length ≤ env.Tm j)
    {off : Int × Int} (hoff : posA j0 off.1 off.2 = true) (len si : Nat) (cyc : Bool) (rt : Nat)
    (h : tagOk env j0 off len si cyc rt = true) {j t : Nat} (hj : j0 ≤ j) (ht : cyc = true ∨ t = 0) :
    eqTags env.gpre env.gper (xval env.Tm off len si j t) rt = true := by
  have hoj : ∀ j', j0 ≤ j' → 0 ≤ off.1 * j' + off.2 := fun j' hj' => posA_ev hoff hj'
  have h2p : 0 < 2 * env.gper.length := by omega
  obtain ⟨m, u, hu, rfl⟩ : ∃ m u, u < 2 * env.gper.length ∧ j = j0 + u + 2 * env.gper.length * m :=
    ⟨(j - j0) / (2 * env.gper.length), (j - j0) % (2 * env.gper.length), Nat.mod_lt _ h2p, by
      have := Nat.div_add_mod (j - j0) (2 * env.gper.length); omega⟩
  obtain ⟨n, t', cc, ht', hcc, rfl⟩ : ∃ (n t' cc : Nat), t' < (if cyc then env.gper.length else 1) ∧
      (env.gper.length : Int) ∣ (cc : Int) ∧ t = t' + cc * n := by
    cases cyc with
    | true =>
      exact ⟨t / env.gper.length, t % env.gper.length, env.gper.length, by simpa using Nat.mod_lt t hp,
        Int.dvd_refl _, by rw [Nat.mod_add_div]⟩
    | false =>
      rcases ht with h' | h'
      · simp at h'
      · subst h'; exact ⟨0, 0, 0, by simp, Int.dvd_zero _, by simp⟩
  have hmem : eqTags env.gpre env.gper (xval env.Tm off len si (j0 + u) t') rt = true := by
    unfold tagOk at h
    rw [List.all_eq_true] at h
    have := h u (List.mem_range.2 hu)
    rw [List.all_eq_true] at this
    exact this t' (List.mem_range.2 ht')
  have hj1 : j0 ≤ j0 + u := Nat.le_add_right _ _
  have hj2 : j0 ≤ j0 + u + 2 * env.gper.length * m := by omega
  have hN := Nat.le_trans (hTge _ hj2) (xval_ge env.Tm (off := off) len si _ (t' + cc * n) (hoj _ hj2))
  have hN' := Nat.le_trans (hTge _ hj1) (xval_ge env.Tm (off := off) len si _ t' (hoj _ hj1))
  have hdiv : (env.gper.length : Int) ∣
      (xval env.Tm off len si (j0 + u + 2 * env.gper.length * m) (t' + cc * n) : Int) -
        xval env.Tm off len si (j0 + u) t' := by
    rw [xval_int env.Tm len si _ _ (hoj _ hj2), xval_int env.Tm len si _ _ (hoj _ hj1)]
    have hT := hTper (j0 + u) (Nat.le_add_right _ _) m
    obtain ⟨c1, hc1⟩ := hT
    obtain ⟨c2, hc2⟩ := hcc
    refine ⟨c1 + 2 * off.1 * m + c2 * n * len, ?_⟩
    push_cast
    rw [hc2]
    have : (env.Tm (j0 + u + 2 * env.gper.length * m) : Int) = env.Tm (j0 + u) +
        env.gper.length * c1 := by omega
    rw [this]
    grind
  rw [eqTags_cong env.gpre env.gper hN hN' hdiv rt]
  exact hmem

/-! ### A run of rows on affine counters -/

def runBody (env : Env) (cx : Cx) (off : Int × Int) (len : Nat) (cyc ex : Bool) :
    Nat → List Nat → List (List Move) → Shape → List A3 → Option (Shape × List A3)
  | _, [], [], s, cn => some (s, cn)
  | si, rt :: rts, mv :: mvs, s, cn =>
    if tagOk env cx.j0 off len si cyc rt then
      match symRow env.S1 env.gpre env.gper cx rt s cn mv with
      | none => none
      | some (s', cn') =>
        if wallOk cx env.π env.P s' cn' && (!(ex && si == 0) || wallEx env.π env.P0 s' cn') then
          runBody env cx off len cyc ex (si + 1) rts mvs s' cn'
        else none
    else none
  | _, _, _, _, _ => none

theorem runBody_sound (env : Env) (hS : ∀ s ∈ env.S1, 0 < s) (hm : 0 < mOf env.S1)
    (hp : 0 < env.gper.length) (cx : Cx)
    (hTper : ∀ j, cx.j0 ≤ j → ∀ m, (env.gper.length : Int) ∣ (env.Tm (j + 2 * env.gper.length * m) : Int) - env.Tm j)
    (hTge : ∀ j, cx.j0 ≤ j → env.gpre.length ≤ env.Tm j)
    {off : Int × Int} (hoff : posA cx.j0 off.1 off.2 = true) (len : Nat) (cyc ex : Bool) :
    ∀ (rts : List Nat) (mvs : List (List Move)) (si : Nat) (s : Shape) (cn : List A3)
      (s' : Shape) (cn' : List A3),
      runBody env cx off len cyc ex si rts mvs s cn = some (s', cn') →
      ∀ {j t : Nat}, cx.dom j t → (cyc = true ∨ t = 0) → Pos cn j t →
      (∀ x, decode s (evC cn j t) x = St env.S1 env.gpre env.gper (xval env.Tm off len si j t) x) →
      (∀ x, decode s' (evC cn' j t) x =
        St env.S1 env.gpre env.gper (xval env.Tm off len (si + rts.length) j t) x) ∧
      Pos cn' j t ∧
      (∀ r, r < rts.length → PerFrom
        (St env.S1 env.gpre env.gper (xval env.Tm off len (si + r) j t + 1)) env.π
        (env.P.1 * j + env.P.2).toNat) ∧
      (ex = true → si = 0 → rts ≠ [] → ∃ q : Nat, (q : Int) = env.P0.1 * j + env.P0.2 ∧
        IsPreG env.S1 env.gpre env.gper env.π (xval env.Tm off len 0 j t) q) := by
  intro rts
  induction rts with
  | nil =>
    intro mvs si s cn s' cn' h j t hd hc hpos hdec
    cases mvs with
    | nil =>
      simp only [runBody, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simpa using hdec, hpos, fun r hr => by simp at hr, fun _ _ h => absurd rfl h⟩
    | cons => simp [runBody] at h
  | cons rt rts ih =>
    intro mvs si s cn s' cn' h j t hd hc hpos hdec
    cases mvs with
    | nil => simp [runBody] at h
    | cons mv mvs =>
      simp only [runBody] at h
      by_cases htg : tagOk env cx.j0 off len si cyc rt = true
      · simp only [htg, ↓reduceIte] at h
        cases hr : symRow env.S1 env.gpre env.gper cx rt s cn mv with
        | none => simp [hr] at h
        | some r1 =>
          obtain ⟨s1, cn1⟩ := r1
          simp only [hr] at h
          by_cases hw : (wallOk cx env.π env.P s1 cn1 && (!(ex && si == 0) || wallEx env.π env.P0 s1 cn1)) = true
          · simp only [hw, ↓reduceIte] at h
            have hoj : 0 ≤ off.1 * j + off.2 := posA_ev hoff hd.1
            have heq := tagOk_sound env hp cx.j0 hTper hTge hoff len si cyc rt htg hd.1 hc
            have htag := tstep_eqTags env.S1 env.gpre env.gper hp heq
            obtain ⟨hdec1, hpos1⟩ := symRow_sound env.S1 env.gpre env.gper hS hr hd hpos htag hdec
            simp only [Bool.and_eq_true] at hw
            obtain ⟨hw1, hw2⟩ := hw
            have hper := wallOk_sound hw1 hd hpos1
            have e1o : decode s1 (evC cn1 j t) =
                St env.S1 env.gpre env.gper (xval env.Tm off len si j t + 1) := funext hdec1
            have e2 : xval env.Tm off len (si + 1) j t = xval env.Tm off len si j t + 1 :=
              xval_succ env.Tm len si j t hoj
            have e1 : decode s1 (evC cn1 j t) = St env.S1 env.gpre env.gper (xval env.Tm off len (si + 1) j t) := by
              rw [e2]; exact e1o
            obtain ⟨ih1, ih2, ih3, -⟩ := ih mvs (si + 1) s1 cn1 s' cn' h hd hc hpos1 (fun x => by rw [e1])
            refine ⟨?_, ih2, ?_, ?_⟩
            · intro x
              rw [ih1 x, List.length_cons, show si + 1 + rts.length = si + (rts.length + 1) by omega]
            · intro r hr
              cases r with
              | zero =>
                rw [e1o] at hper
                simpa using hper
              | succ r =>
                have := ih3 r (by simp at hr; omega)
                rwa [show si + 1 + r = si + (r + 1) by omega] at this
            · intro hex hs0 _
              subst hs0
              have hw3 : wallEx env.π env.P0 s1 cn1 = true := by
                simp [hex] at hw2; exact hw2
              obtain ⟨q, hq1, hq2, hq3, hq4⟩ := wallEx_sound hw3 hpos1
              rw [e1o] at hq3 hq4
              exact ⟨q, hq1, isPre_of env.S1 env.gpre env.gper hm hq3 hq2 hq4⟩
          · rw [if_neg hw] at h; exact absurd h (by simp)
      · simp [htg] at h

/-! ### Phases -/

theorem rowAt_succ (Tm : Nat → Nat) {off : Int × Int} (j : Nat) (h : 0 ≤ off.1 * j + off.2) :
    rowAt Tm (off.1, off.2 + 1) j = rowAt Tm off j + 1 := by
  unfold rowAt; simp only; omega

theorem xval_t0 (Tm : Nat → Nat) {off : Int × Int} (len si j : Nat) (h : 0 ≤ off.1 * j + off.2) :
    xval Tm off len si j 0 = rowAt Tm (off.1, off.2 + si) j := by
  unfold xval rowAt; simp only; omega

/-- every row `x` of `[lo, hi)` has its bit-0 word periodic from the affine bound `P` -/
def Cov (env : Env) (j lo hi : Nat) : Prop :=
  ∀ x, lo ≤ x → x < hi →
    PerFrom (St env.S1 env.gpre env.gper (x + 1)) env.π (env.P.1 * (j : Int) + env.P.2).toNat

theorem Cov_empty (env : Env) (j lo : Nat) : Cov env j lo lo := fun x h1 h2 => absurd h2 (by omega)

theorem Cov_append (env : Env) {j a b c : Nat} (h1 : Cov env j a b) (h2 : Cov env j b c) :
    Cov env j a c := by
  intro x hx1 hx2
  by_cases hb : x < b
  · exact h1 x hx1 hb
  · exact h2 x (by omega) hx2

def runPhase (env : Env) (j0 : Nat) (first : Bool) :
    PhaseC → Shape → List A3 → Int × Int → Option (Shape × List A3 × Int × Int)
  | .step rt mv, s, cn, off =>
    if posA j0 off.1 off.2 then
      match runBody env ⟨j0, 0, 1⟩ off 1 false first 0 [rt] [mv] s cn with
      | none => none
      | some (s', cn') => some (s', cn', (off.1, off.2 + 1))
    else none
  | .cycle len ca cb d rts mvs, s, cn, off =>
    if !first && rts.length == len && mvs.length == len && d.length == cn.length &&
        posA j0 off.1 off.2 && posA j0 ca cb && posA j0 (off.1 + len * ca) (off.2 + len * cb) then
      match runBody env ⟨j0, ca, cb⟩ off len true false 0 rts mvs s
          (List.zipWith (fun x di => { x with e := di }) cn d) with
      | none => none
      | some (s1, cn1) =>
        if s1 = s ∧ cn1 = (List.zipWith (fun x di => { x with e := di }) cn d).map
            (fun x => { x with b := x.b + x.e }) ∧
            (List.zipWith (fun x di => (⟨x.a + di * ca, 0, x.b + di * cb⟩ : A3)) cn d).all
              (nn ⟨j0, 0, 1⟩) = true then
          some (s, List.zipWith (fun x di => (⟨x.a + di * ca, 0, x.b + di * cb⟩ : A3)) cn d,
            (off.1 + len * ca, off.2 + len * cb))
        else none
    else none

theorem evC_shift (cc : List A3) (j t : Nat) :
    evC (cc.map fun x => { x with b := x.b + x.e }) j t = evC cc j (t + 1) := by
  unfold evC
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp, A3.ev]
  congr 1
  push_cast
  grind

theorem Pos_shift (cc : List A3) (j t : Nat) (h : Pos (cc.map fun x => { x with b := x.b + x.e }) j t) :
    Pos cc j (t + 1) := by
  intro x hx
  have := h _ (List.mem_map_of_mem hx)
  simp only [A3.ev] at this ⊢
  push_cast at this ⊢
  grind

/-- the cycle iteration lemma: `n` iterations of a body that returns to its shape with the
counters moved by their `t`-coefficients -/
theorem cycle_iter (env : Env) (hS : ∀ s ∈ env.S1, 0 < s) (hm : 0 < mOf env.S1)
    (hp : 0 < env.gper.length) (cx : Cx)
    (hTper : ∀ j, cx.j0 ≤ j → ∀ m, (env.gper.length : Int) ∣ (env.Tm (j + 2 * env.gper.length * m) : Int) - env.Tm j)
    (hTge : ∀ j, cx.j0 ≤ j → env.gpre.length ≤ env.Tm j)
    {off : Int × Int} (hoff : posA cx.j0 off.1 off.2 = true) (len : Nat)
    (rts : List Nat) (mvs : List (List Move)) (s : Shape) (cc cn1 : List A3)
    (hb : runBody env cx off len true false 0 rts mvs s cc = some (s, cn1))
    (hcn1 : cn1 = cc.map fun x => { x with b := x.b + x.e }) (hlen : rts.length = len)
    {j : Nat} (hj : cx.j0 ≤ j) :
    ∀ n : Nat, (n : Int) ≤ cx.ca * j + cx.cb →
      (∀ x, decode s (evC cc j 0) x = St env.S1 env.gpre env.gper (xval env.Tm off len 0 j 0) x) →
      Pos cc j 0 →
      (∀ x, decode s (evC cc j n) x = St env.S1 env.gpre env.gper (xval env.Tm off len 0 j n) x) ∧
      Pos cc j n ∧
      ∀ t, t < n → ∀ r, r < len → PerFrom
        (St env.S1 env.gpre env.gper (xval env.Tm off len r j t + 1)) env.π
        (env.P.1 * (j : Int) + env.P.2).toNat := by
  intro n
  induction n with
  | zero => intro _ h0 hp0; exact ⟨h0, hp0, fun t ht => absurd ht (by omega)⟩
  | succ n ih =>
    intro hn h0 hp0
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega) h0 hp0
    have hd : cx.dom j n := ⟨hj, by omega⟩
    obtain ⟨r1, r2, r3, -⟩ := runBody_sound env hS hm hp cx hTper hTge hoff len true false rts mvs 0 s cc
      s cn1 hb hd (Or.inl rfl) ih2 (by simpa [Nat.zero_add] using ih1)
    have hoj : 0 ≤ off.1 * j + off.2 := posA_ev hoff hj
    rw [hlen, Nat.zero_add] at r1
    rw [show xval env.Tm off len len j n = xval env.Tm off len 0 j (n + 1) from by
      simpa using xval_iter env.Tm (off := off) len 0 j n hoj] at r1
    rw [hcn1, evC_shift] at r1
    rw [hcn1] at r2
    refine ⟨r1, Pos_shift cc j n r2, ?_⟩
    intro t ht r hr
    by_cases htn : t < n
    · exact ih3 t htn r hr
    · have : t = n := by omega
      subst this
      simpa [hlen, Nat.zero_add] using r3 r (by omega)

theorem evC_zipe (j t : Nat) : ∀ (cn : List A3) (d : List Int), d.length = cn.length →
    evC (List.zipWith (fun x di => { x with e := di }) cn d) j 0 = evC cn j 0 := by
  intro cn
  induction cn with
  | nil => intro d h; cases d <;> simp_all [evC]
  | cons x xs ih =>
    intro d h
    cases d with
    | nil => simp at h
    | cons di ds =>
      have := ih ds (by simpa using h)
      unfold evC at this ⊢
      simp only [List.zipWith_cons_cons, List.map_cons, this]
      simp [A3.ev]

theorem Pos_zipe (j : Nat) : ∀ (cn : List A3) (d : List Int), d.length = cn.length →
    Pos cn j 0 → Pos (List.zipWith (fun x di => { x with e := di }) cn d) j 0 := by
  intro cn
  induction cn with
  | nil => intro d h _; cases d <;> simp_all [Pos_nil]
  | cons x xs ih =>
    intro d h hp
    cases d with
    | nil => simp at h
    | cons di ds =>
      simp only [List.zipWith_cons_cons]
      apply Pos_cons
      · have := Pos_head hp
        simpa [A3.ev] using this
      · exact ih ds (by simpa using h) (Pos_tail hp)

theorem evC_zipc (ca cb : Int) (j n : Nat) (hn : (n : Int) = ca * j + cb) :
    ∀ (cn : List A3) (d : List Int), d.length = cn.length →
    evC (List.zipWith (fun x di => { x with e := di }) cn d) j n =
      evC (List.zipWith (fun x di => (⟨x.a + di * ca, 0, x.b + di * cb⟩ : A3)) cn d) j 0 := by
  intro cn
  induction cn with
  | nil => intro d h; cases d <;> simp_all [evC]
  | cons x xs ih =>
    intro d h
    cases d with
    | nil => simp at h
    | cons di ds =>
      have := ih ds (by simpa using h)
      unfold evC at this ⊢
      simp only [List.zipWith_cons_cons, List.map_cons, this]
      congr 2
      simp only [A3.ev]
      rw [hn]
      push_cast
      grind

theorem rowAt_int (Tm : Nat → Nat) {off : Int × Int} (j : Nat) (h : 0 ≤ off.1 * j + off.2) :
    (rowAt Tm off j : Int) = Tm j + (off.1 * j + off.2) := by
  unfold rowAt; omega

theorem runPhase_sound (env : Env) (hS : ∀ s ∈ env.S1, 0 < s) (hm : 0 < mOf env.S1)
    (hp : 0 < env.gper.length) (j0 : Nat)
    (hTper : ∀ j, j0 ≤ j → ∀ m, (env.gper.length : Int) ∣ (env.Tm (j + 2 * env.gper.length * m) : Int) - env.Tm j)
    (hTge : ∀ j, j0 ≤ j → env.gpre.length ≤ env.Tm j) (first : Bool) (ph : PhaseC)
    {s s' : Shape} {cn cn' : List A3} {off off' : Int × Int}
    (h : runPhase env j0 first ph s cn off = some (s', cn', off')) :
    posA j0 off.1 off.2 = true ∧ posA j0 off'.1 off'.2 = true ∧
    ∀ j, j0 ≤ j → (∀ x, decode s (evC cn j 0) x = St env.S1 env.gpre env.gper (rowAt env.Tm off j) x) →
      Pos cn j 0 →
      (∀ x, decode s' (evC cn' j 0) x = St env.S1 env.gpre env.gper (rowAt env.Tm off' j) x) ∧
      Pos cn' j 0 ∧ Cov env j (rowAt env.Tm off j) (rowAt env.Tm off' j) ∧
      (first = true → ∃ q : Nat, (q : Int) = env.P0.1 * j + env.P0.2 ∧
        IsPreG env.S1 env.gpre env.gper env.π (rowAt env.Tm off j) q) := by
  cases ph with
  | step rt mv =>
    unfold runPhase at h
    by_cases hoff : posA j0 off.1 off.2 = true
    · simp only [hoff, ↓reduceIte] at h
      cases hr : runBody env ⟨j0, 0, 1⟩ off 1 false first 0 [rt] [mv] s cn with
      | none => simp [hr] at h
      | some r1 =>
        obtain ⟨s1, cn1⟩ := r1
        simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hoff1 : posA j0 off.1 (off.2 + 1) = true := by
          simp only [posA, Bool.and_eq_true, decide_eq_true_eq] at hoff ⊢
          omega
        refine ⟨hoff, hoff1, ?_⟩
        intro j hj hdec hpos
        have hoj : 0 ≤ off.1 * j + off.2 := posA_ev hoff hj
        have hd : (Cx.mk j0 0 1).dom j 0 := ⟨hj, by simp⟩
        obtain ⟨r1, r2, r3, r4⟩ := runBody_sound env hS hm hp ⟨j0, 0, 1⟩ hTper hTge hoff 1 false first
          [rt] [mv] 0 s cn s1 cn1 hr hd (Or.inr rfl) hpos
          (by rw [xval_t0 env.Tm 1 0 j hoj] at *; simpa using hdec)
        have e1 : xval env.Tm off 1 (0 + [rt].length) j 0 = rowAt env.Tm (off.1, off.2 + 1) j := by
          rw [xval_t0 env.Tm _ _ j hoj]; simp
        refine ⟨fun x => by rw [r1 x, e1], r2, ?_, ?_⟩
        · intro x hx1 hx2
          have e2 := rowAt_succ env.Tm j hoj
          have hx : x = rowAt env.Tm off j := by omega
          have := r3 0 (by simp)
          rw [xval_t0 env.Tm 1 (0 + 0) j hoj] at this
          subst hx
          simpa using this
        · intro hf
          obtain ⟨q, hq1, hq2⟩ := r4 hf rfl (by simp)
          rw [xval_t0 env.Tm 1 0 j hoj] at hq2
          exact ⟨q, hq1, by simpa using hq2⟩
    · simp [hoff] at h
  | cycle len ca cb d rts mvs =>
    unfold runPhase at h
    by_cases hc : (!first && rts.length == len && mvs.length == len && d.length == cn.length &&
        posA j0 off.1 off.2 && posA j0 ca cb && posA j0 (off.1 + len * ca) (off.2 + len * cb)) = true
    · simp only [hc, ↓reduceIte] at h
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨⟨⟨⟨hf, hl1⟩, hl2⟩, hl3⟩, hoff⟩, hcnt⟩, hoff'⟩ := hc
      cases hr : runBody env ⟨j0, ca, cb⟩ off len true false 0 rts mvs s
          (List.zipWith (fun x di => { x with e := di }) cn d) with
      | none => simp [hr] at h
      | some r1 =>
        obtain ⟨s1, cn1⟩ := r1
        simp only [hr] at h
        by_cases hq : s1 = s ∧ cn1 = (List.zipWith (fun x di => { x with e := di }) cn d).map
            (fun x => { x with b := x.b + x.e }) ∧
            (List.zipWith (fun x di => (⟨x.a + di * ca, 0, x.b + di * cb⟩ : A3)) cn d).all
              (nn ⟨j0, 0, 1⟩) = true
        · rw [if_pos hq] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨hs1, hq2, hq3⟩ := hq
          rw [hs1] at hr
          refine ⟨hoff, hoff', ?_⟩
          intro j hj hdec hpos
          have hoj : 0 ≤ off.1 * j + off.2 := posA_ev hoff hj
          have hcj : 0 ≤ ca * j + cb := posA_ev hcnt hj
          have hoj' : 0 ≤ (off.1 + len * ca) * j + (off.2 + len * cb) := posA_ev hoff' hj
          obtain ⟨n, hn⟩ : ∃ n : Nat, (n : Int) = ca * j + cb := ⟨(ca * j + cb).toNat, by omega⟩
          have hdec0 : ∀ x, decode s (evC (List.zipWith (fun x di => { x with e := di }) cn d) j 0) x =
              St env.S1 env.gpre env.gper (xval env.Tm off len 0 j 0) x := by
            intro x
            rw [evC_zipe j 0 cn d hl3, xval_t0 env.Tm len 0 j hoj]
            simpa using hdec x
          obtain ⟨c1, c2, c3⟩ := cycle_iter env hS hm hp ⟨j0, ca, cb⟩ hTper hTge hoff len rts mvs s _ cn1
            hr hq2 hl1 hj n (by show (n : Int) ≤ ca * j + cb; omega) hdec0 (Pos_zipe j cn d hl3 hpos)
          have e6 : ((off.1 + len * ca) * j + (off.2 + len * cb) : Int) = off.1 * j + off.2 + n * len := by
            rw [show (n : Int) * len = len * (ca * j + cb) by rw [hn]; grind]; grind
          have a1 := rowAt_int env.Tm (off := off) j hoj
          have a2 := rowAt_int env.Tm (off := (off.1 + len * ca, off.2 + len * cb)) j hoj'
          simp only at a2
          have hrow : xval env.Tm off len 0 j n = rowAt env.Tm (off.1 + len * ca, off.2 + len * cb) j := by
            have a0 := xval_int env.Tm (off := off) len 0 j n hoj
            omega
          have hcnd : ∀ x ∈ (List.zipWith (fun x di => (⟨x.a + di * ca, 0, x.b + di * cb⟩ : A3)) cn d),
              nn ⟨j0, 0, 1⟩ x = true := by
            intro x hx
            exact List.all_eq_true.1 hq3 x hx
          refine ⟨fun x => ?_, fun x hx => ?_, ?_, fun hf' => absurd hf' (by simp [hf])⟩
          · rw [← evC_zipc ca cb j n hn cn d hl3, c1 x, hrow]
          · exact nn_ev (hcnd x hx) (j := j) (t := 0) ⟨hj, by simp⟩
          · intro x hx1 hx2
            have hxlt : x - rowAt env.Tm off j < n * len := by
              have : (x : Int) < rowAt env.Tm off j + ((n * len : Nat) : Int) := by
                push_cast; omega
              omega
            have hlen : 0 < len := Nat.pos_of_ne_zero (fun h0 => by subst h0; simp at hxlt)
            have hdm := Nat.div_add_mod' (x - rowAt env.Tm off j) len
            have hml := Nat.mod_lt (x - rowAt env.Tm off j) hlen
            have hxn : (x - rowAt env.Tm off j) / len < n := (Nat.div_lt_iff_lt_mul hlen).2 hxlt
            generalize (x - rowAt env.Tm off j) / len = q at hdm hxn
            generalize (x - rowAt env.Tm off j) % len = r at hdm hml
            have := c3 q hxn r hml
            have a3 := xval_int env.Tm (off := off) len r j q hoj
            have hdmI : ((q * len + r : Nat) : Int) = ((x - rowAt env.Tm off j : Nat) : Int) := by rw [hdm]
            push_cast at hdmI
            have ex : xval env.Tm off len r j q = x := by omega
            rw [ex] at this
            exact this
        · rw [if_neg hq] at h
          exact absurd h (by simp)
    · simp [hc] at h

def runPhases (env : Env) (j0 : Nat) :
    Bool → List PhaseC → Shape → List A3 → Int × Int → Option (Shape × List A3 × Int × Int)
  | _, [], s, cn, off => some (s, cn, off)
  | first, ph :: phs, s, cn, off =>
    match runPhase env j0 first ph s cn off with
    | none => none
    | some (s1, cn1, off1) => runPhases env j0 false phs s1 cn1 off1

theorem runPhases_sound (env : Env) (hS : ∀ s ∈ env.S1, 0 < s) (hm : 0 < mOf env.S1)
    (hp : 0 < env.gper.length) (j0 : Nat)
    (hTper : ∀ j, j0 ≤ j → ∀ m, (env.gper.length : Int) ∣ (env.Tm (j + 2 * env.gper.length * m) : Int) - env.Tm j)
    (hTge : ∀ j, j0 ≤ j → env.gpre.length ≤ env.Tm j) :
    ∀ (phs : List PhaseC) (first : Bool) {s s' : Shape} {cn cn' : List A3} {off off' : Int × Int},
    runPhases env j0 first phs s cn off = some (s', cn', off') → posA j0 off.1 off.2 = true →
    posA j0 off'.1 off'.2 = true ∧
    ∀ j, j0 ≤ j → (∀ x, decode s (evC cn j 0) x = St env.S1 env.gpre env.gper (rowAt env.Tm off j) x) →
      Pos cn j 0 →
      (∀ x, decode s' (evC cn' j 0) x = St env.S1 env.gpre env.gper (rowAt env.Tm off' j) x) ∧
      Pos cn' j 0 ∧ Cov env j (rowAt env.Tm off j) (rowAt env.Tm off' j) ∧
      (first = true → phs ≠ [] → ∃ q : Nat, (q : Int) = env.P0.1 * j + env.P0.2 ∧
        IsPreG env.S1 env.gpre env.gper env.π (rowAt env.Tm off j) q) := by
  intro phs
  induction phs with
  | nil =>
    intro first s s' cn cn' off off' h ho
    simp only [runPhases, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨ho, fun j hj hd hp => ⟨hd, hp, Cov_empty _ _ _, fun _ h => absurd rfl h⟩⟩
  | cons ph phs ih =>
    intro first s s' cn cn' off off' h ho
    simp only [runPhases] at h
    cases hr : runPhase env j0 first ph s cn off with
    | none => simp [hr] at h
    | some r1 =>
      obtain ⟨s1, cn1, off1⟩ := r1
      simp only [hr] at h
      obtain ⟨-, ho1, hs1⟩ := runPhase_sound env hS hm hp j0 hTper hTge first ph hr
      obtain ⟨ho2, hs2⟩ := ih false h ho1
      refine ⟨ho2, fun j hj hd hpos => ?_⟩
      obtain ⟨d1, p1, c1, e1⟩ := hs1 j hj hd hpos
      obtain ⟨d2, p2, c2, -⟩ := hs2 j hj d1 p1
      exact ⟨d2, p2, Cov_append env c1 c2, fun hf _ => e1 hf⟩

end Family
