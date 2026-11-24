import FamilyPhase
import FamilyJump
import FamilyGame
/-!
The round checker and the general wall theorem.

`CertD` is the certificate data: wall parameters, the law numbers and, for every residue class `i < R`
of the round index `k = R*j + i`, the shape and affine counters at the start of the round and the
phases of the round.  `check` is a `Bool` function; `family_wall` says that a passing certificate with
a true initial run gives the wall law for every round `k >= k0`.
-/
namespace Family

/-- A checkpointed stretch of phases: the literal state before and after (this cuts the kernel's term
sharing and lets every chunk be a separate `decide +kernel` theorem). -/
structure Chunk where
  phases : List PhaseC
  s0 : Shape
  cn0 : List A3
  off0 : Int × Int
  s1 : Shape
  cn1 : List A3
  off1 : Int × Int

structure ClassC where
  j0 : Nat
  init : Shape
  cnt : List (Int × Int)          -- counter `a*j + b`
  chunks : List Chunk

/-- Certificate data. `t k` is the first row of round `k`: `t k0 = T0`, `t (k+1) = t k + α k + β`. -/
structure CertD where
  S1 : List Nat
  gpre : List Nat
  gper : List Nat
  π : Nat
  α : Nat
  β : Nat
  Δ : Nat
  w0 : Nat
  c : Nat
  R : Nat
  k0 : Nat
  T0 : Nat
  classes : List ClassC

def tRec (T0 k0 α β : Nat) : Nat → Nat
  | 0 => T0
  | n + 1 => tRec T0 k0 α β n + α * (k0 + n) + β

def CertD.t (C : CertD) (k : Nat) : Nat := tRec C.T0 C.k0 C.α C.β (k - C.k0)

def dflt : ClassC := ⟨0, ⟨[], [], []⟩, [], []⟩

def CertD.cls (C : CertD) (i : Nat) : ClassC := C.classes.getD i dflt

def ClassC.cn0 (cl : ClassC) : List A3 := cl.cnt.map fun ab => ⟨ab.1, 0, ab.2⟩

def CertD.env (C : CertD) (i : Nat) : Env where
  S1 := C.S1
  gpre := C.gpre
  gper := C.gper
  π := C.π
  P := ((C.Δ : Int) * C.R, (C.w0 : Int) + C.Δ * i + C.c)
  P0 := ((C.Δ : Int) * C.R, (C.w0 : Int) + C.Δ * i)
  Tm := fun j => C.t (C.R * j + i)

/-- the initial-run fact: the first steady shape decodes to the stack after `T0` rows -/
def CertD.InitOk (C : CertD) : Prop :=
  ∀ x, decode (C.cls (C.k0 % C.R)).init (evC (C.cls (C.k0 % C.R)).cn0 (C.k0 / C.R) 0) x =
    St C.S1 C.gpre C.gper C.T0 x

structure Cert extends CertD where
  initOk : toCertD.InitOk

def chunkOk (env : Env) (j0 : Nat) (first : Bool) (c : Chunk) : Bool :=
  match runPhases env j0 first c.phases c.s0 c.cn0 c.off0 with
  | none => false
  | some (s', cn', off') => decide (s' = c.s1 ∧ cn' = c.cn1 ∧ off' = c.off1)

def chunksOk (env : Env) (j0 : Nat) : Bool → List Chunk → Bool
  | _, [] => true
  | first, c :: cs => chunkOk env j0 first c && chunksOk env j0 false cs

/-- the chunks chain: each starts where the previous one ended -/
def linksB : Shape → List A3 → Int × Int → List Chunk → Option (Shape × List A3 × Int × Int)
  | s, cn, off, [] => some (s, cn, off)
  | s, cn, off, c :: cs =>
    if decide (s = c.s0 ∧ cn = c.cn0 ∧ off = c.off0) then linksB c.s1 c.cn1 c.off1 cs else none

def firstNonempty : List Chunk → Bool
  | [] => false
  | c :: _ => !c.phases.isEmpty

/-- everything about a class except the (expensive) chunk runs -/
def checkClassL (C : CertD) (i : Nat) : Bool :=
  let cl := C.cls i
  let nxt := C.cls ((i + 1) % C.R)
  let δ : Int := if i + 1 == C.R then 1 else 0
  decide (C.k0 ≤ C.R * cl.j0 + i) && decide (C.R * cl.j0 + i < C.k0 + C.R) &&
  cl.cnt.all (fun ab => posA cl.j0 ab.1 ab.2) && firstNonempty cl.chunks &&
  decide (nxt.cnt.length = cl.cnt.length) &&
  match linksB cl.init cl.cn0 (0, 0) cl.chunks with
  | none => false
  | some (s', cn', off') =>
    decide (s' = nxt.init) &&
    decide (cn' = nxt.cnt.map fun ab => (⟨ab.1, 0, ab.2 + ab.1 * δ⟩ : A3)) &&
    decide (off' = ((C.α : Int) * C.R, (C.α : Int) * i + C.β))

def checkClass (C : CertD) (i : Nat) : Bool :=
  checkClassL C i && chunksOk (C.env i) (C.cls i).j0 true (C.cls i).chunks

def globalOk (C : CertD) : Bool :=
  decide (0 < C.R) && decide (C.classes.length = C.R) && decide (0 < C.gper.length) &&
  !C.S1.isEmpty && C.S1.all (fun s => decide (0 < s)) && decide (C.gpre.length ≤ C.T0)

def check (C : CertD) : Bool :=
  globalOk C && (List.range C.R).all (checkClass C)

/-- `check` from its cheap part and the chunk runs, which can then be separate kernel theorems -/
theorem check_of_parts (C : CertD) (h1 : globalOk C = true)
    (h2 : ∀ i, i < C.R → checkClassL C i = true)
    (h3 : ∀ i, i < C.R → chunksOk (C.env i) (C.cls i).j0 true (C.cls i).chunks = true) :
    check C = true := by
  unfold check
  rw [Bool.and_eq_true]
  refine ⟨h1, List.all_eq_true.2 fun i hi => ?_⟩
  have hi' := List.mem_range.1 hi
  unfold checkClass
  rw [Bool.and_eq_true]
  exact ⟨h2 i hi', h3 i hi'⟩

theorem chunksOk_nil (env : Env) (j0 : Nat) (first : Bool) : chunksOk env j0 first [] = true := rfl

theorem chunksOk_cons {env : Env} {j0 : Nat} {first : Bool} {c : Chunk} {cs : List Chunk}
    (h1 : chunkOk env j0 first c = true) (h2 : chunksOk env j0 false cs = true) :
    chunksOk env j0 first (c :: cs) = true := by
  simp only [chunksOk, Bool.and_eq_true]; exact ⟨h1, h2⟩

/-! ### The round-start function -/

theorem tRec_add (T0 k0 α β n : Nat) : ∀ d : Nat,
    2 * (tRec T0 k0 α β (n + d) : Int) = 2 * tRec T0 k0 α β n + 2 * β * d +
      α * (2 * n * d + d * (d - 1) + 2 * k0 * d) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    have e : tRec T0 k0 α β (n + (d + 1)) = tRec T0 k0 α β (n + d) + α * (k0 + (n + d)) + β := rfl
    rw [e]
    push_cast
    grind

theorem tRec_ge (T0 k0 α β : Nat) : ∀ n, T0 ≤ tRec T0 k0 α β n := by
  intro n
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => show T0 ≤ tRec T0 k0 α β n + α * (k0 + n) + β; omega

theorem CertD.t_succ (C : CertD) {k : Nat} (hk : C.k0 ≤ k) :
    C.t (k + 1) = C.t k + C.α * k + C.β := by
  unfold CertD.t
  have : k + 1 - C.k0 = (k - C.k0) + 1 := by omega
  rw [this]
  show tRec C.T0 C.k0 C.α C.β (k - C.k0) + C.α * (C.k0 + (k - C.k0)) + C.β = _
  rw [show C.k0 + (k - C.k0) = k by omega]

theorem CertD.t_k0 (C : CertD) : C.t C.k0 = C.T0 := by
  unfold CertD.t; simp [tRec]

theorem CertD.t_ge (C : CertD) (k : Nat) : C.T0 ≤ C.t k := tRec_ge _ _ _ _ _

theorem CertD.t_closed (C : CertD) {k : Nat} (hk : C.k0 ≤ k) :
    2 * (C.t k : Int) = 2 * C.T0 + 2 * C.β * ((k : Int) - C.k0) +
      C.α * ((k : Int) * (k - 1) - (C.k0 : Int) * (C.k0 - 1)) := by
  have h := tRec_add C.T0 C.k0 C.α C.β 0 (k - C.k0)
  have e : C.t k = tRec C.T0 C.k0 C.α C.β (0 + (k - C.k0)) := by unfold CertD.t; simp
  rw [e]
  have h0 : tRec C.T0 C.k0 C.α C.β 0 = C.T0 := rfl
  rw [h0] at h
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
  subst hd
  rw [show C.k0 + d - C.k0 = d by omega]
  push_cast at h ⊢
  have : (d : Int) - 1 + 1 = d := by omega
  grind

theorem CertD.t_per (C : CertD) (p : Nat) {k : Nat} (hk : C.k0 ≤ k) (m : Nat) :
    (p : Int) ∣ (C.t (k + 2 * p * m) : Int) - C.t k := by
  have h := tRec_add C.T0 C.k0 C.α C.β (k - C.k0) (2 * p * m)
  have e1 : C.t k = tRec C.T0 C.k0 C.α C.β (k - C.k0) := rfl
  have e2 : C.t (k + 2 * p * m) = tRec C.T0 C.k0 C.α C.β ((k - C.k0) + 2 * p * m) := by
    unfold CertD.t; congr 1; omega
  rw [e2] at *
  rw [e1]
  refine ⟨2 * C.β * m + C.α * m * (2 * ((k - C.k0 : Nat) : Int) + (2 * p * m - 1) + 2 * C.k0), ?_⟩
  push_cast at h ⊢
  grind

/-! ### Chunks -/

theorem chunks_sound (env : Env) (hS : ∀ s ∈ env.S1, 0 < s) (hm : 0 < mOf env.S1)
    (hp : 0 < env.gper.length) (j0 : Nat)
    (hTper : ∀ j, j0 ≤ j → ∀ m, (env.gper.length : Int) ∣ (env.Tm (j + 2 * env.gper.length * m) : Int) - env.Tm j)
    (hTge : ∀ j, j0 ≤ j → env.gpre.length ≤ env.Tm j) :
    ∀ (cs : List Chunk) (first : Bool) {s s' : Shape} {cn cn' : List A3} {off off' : Int × Int},
    chunksOk env j0 first cs = true → linksB s cn off cs = some (s', cn', off') →
    posA j0 off.1 off.2 = true →
    posA j0 off'.1 off'.2 = true ∧
    ∀ j, j0 ≤ j → (∀ x, decode s (evC cn j 0) x = St env.S1 env.gpre env.gper (rowAt env.Tm off j) x) →
      Pos cn j 0 →
      (∀ x, decode s' (evC cn' j 0) x = St env.S1 env.gpre env.gper (rowAt env.Tm off' j) x) ∧
      Pos cn' j 0 ∧ Cov env j (rowAt env.Tm off j) (rowAt env.Tm off' j) ∧
      (first = true → firstNonempty cs = true → ∃ q : Nat, (q : Int) = env.P0.1 * j + env.P0.2 ∧
        IsPreG env.S1 env.gpre env.gper env.π (rowAt env.Tm off j) q) := by
  intro cs
  induction cs with
  | nil =>
    intro first s s' cn cn' off off' _ h ho
    simp only [linksB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨ho, fun j hj hd hp => ⟨hd, hp, Cov_empty _ _ _, fun _ h => by simp [firstNonempty] at h⟩⟩
  | cons c cs ih =>
    intro first s s' cn cn' off off' hc h ho
    simp only [chunksOk, Bool.and_eq_true] at hc
    simp only [linksB] at h
    by_cases hl : (s = c.s0 ∧ cn = c.cn0 ∧ off = c.off0)
    · rw [if_pos (by simpa using hl)] at h
      obtain ⟨rfl, rfl, rfl⟩ := hl
      have hr : runPhases env j0 first c.phases c.s0 c.cn0 c.off0 = some (c.s1, c.cn1, c.off1) := by
        have := hc.1
        unfold chunkOk at this
        cases hh : runPhases env j0 first c.phases c.s0 c.cn0 c.off0 with
        | none => simp [hh] at this
        | some r =>
          obtain ⟨s2, cn2, off2⟩ := r
          simp only [hh, decide_eq_true_eq] at this
          obtain ⟨rfl, rfl, rfl⟩ := this
          rfl
      obtain ⟨ho1, hs1⟩ := runPhases_sound env hS hm hp j0 hTper hTge c.phases first hr ho
      obtain ⟨ho2, hs2⟩ := ih false hc.2 h ho1
      refine ⟨ho2, fun j hj hd hpos => ?_⟩
      obtain ⟨d1, p1, c1, e1⟩ := hs1 j hj hd hpos
      obtain ⟨d2, p2, c2, -⟩ := hs2 j hj d1 p1
      refine ⟨d2, p2, Cov_append env c1 c2, fun hf hne => e1 hf ?_⟩
      intro h0
      simp [firstNonempty, h0] at hne
    · rw [if_neg (by simpa using hl)] at h
      exact absurd h (by simp)

/-! ### One class -/

theorem checkClass_sound (C : CertD) (hp : 0 < C.gper.length) (hS : ∀ s ∈ C.S1, 0 < s)
    (hne : C.S1 ≠ []) (hgN : C.gpre.length ≤ C.T0) {i : Nat} (h : checkClass C i = true)
    {j : Nat} (hj : (C.cls i).j0 ≤ j)
    (hd : ∀ x, decode (C.cls i).init (evC (C.cls i).cn0 j 0) x =
      St C.S1 C.gpre C.gper (C.t (C.R * j + i)) x) :
    (∀ x, decode (C.cls ((i + 1) % C.R)).init
      (evC (C.cls ((i + 1) % C.R)).cn0 (j + (if i + 1 = C.R then 1 else 0)) 0) x =
        St C.S1 C.gpre C.gper (C.t (C.R * j + i) + C.α * (C.R * j + i) + C.β) x) ∧
    (∀ a, C.t (C.R * j + i) ≤ a → a < C.t (C.R * j + i) + C.α * (C.R * j + i) + C.β →
      ∃ q, q ≤ C.w0 + C.Δ * (C.R * j + i) + C.c ∧ IsPreG C.S1 C.gpre C.gper C.π a q) ∧
    IsPreG C.S1 C.gpre C.gper C.π (C.t (C.R * j + i)) (C.w0 + C.Δ * (C.R * j + i)) := by
  have hm := mOf_pos C.S1 hS hne
  unfold checkClass at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hchk⟩ := h
  unfold checkClassL at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hr1, hr2⟩, hcnt⟩, hph⟩, hlen⟩, hrun⟩ := h
  have hk : C.k0 ≤ C.R * j + i := by
    have : C.R * (C.cls i).j0 ≤ C.R * j := Nat.mul_le_mul_left _ hj
    omega
  cases hq : linksB (C.cls i).init (C.cls i).cn0 (0, 0) (C.cls i).chunks with
  | none => simp [hq] at hrun
  | some r1 =>
    obtain ⟨s', cn', off'⟩ := r1
    simp only [hq, Bool.and_eq_true, decide_eq_true_eq] at hrun
    obtain ⟨⟨hs', hcn'⟩, hoff'⟩ := hrun
    have hTper : ∀ j', (C.cls i).j0 ≤ j' → ∀ m, (((C.env i).gper.length : Nat) : Int) ∣
        ((C.env i).Tm (j' + 2 * (C.env i).gper.length * m) : Int) - (C.env i).Tm j' := by
      intro j' hj' m
      have hk' : C.k0 ≤ C.R * j' + i := by
        have : C.R * (C.cls i).j0 ≤ C.R * j' := Nat.mul_le_mul_left _ hj'
        omega
      have := C.t_per C.gper.length hk' (C.R * m)
      have e : C.R * (j' + 2 * C.gper.length * m) + i = C.R * j' + i + 2 * C.gper.length * (C.R * m) := by
        grind
      show (C.gper.length : Int) ∣ (C.t (C.R * (j' + 2 * C.gper.length * m) + i) : Int) - C.t (C.R * j' + i)
      rw [e]; exact this
    have hTge : ∀ j', (C.cls i).j0 ≤ j' → (C.env i).gpre.length ≤ (C.env i).Tm j' :=
      fun j' _ => Nat.le_trans hgN (C.t_ge _)
    obtain ⟨ho', hsound⟩ := chunks_sound (C.env i) hS hm hp (C.cls i).j0 hTper hTge
      (C.cls i).chunks true hchk hq (by simp [posA])
    have hpos0 : Pos (C.cls i).cn0 j 0 := by
      intro x hx
      unfold ClassC.cn0 at hx
      obtain ⟨ab, hab, rfl⟩ := List.mem_map.1 hx
      have := posA_ev (List.all_eq_true.1 hcnt ab hab) hj
      simpa [A3.ev] using this
    have hrow0 : rowAt (C.env i).Tm (0, 0) j = C.t (C.R * j + i) := by
      simp [rowAt, CertD.env]
    obtain ⟨d1, p1, c1, e1⟩ := hsound j hj (by rw [hrow0]; exact hd) hpos0
    subst hoff'
    have hoj : 0 ≤ ((C.α : Int) * C.R) * j + ((C.α : Int) * i + C.β) := posA_ev ho' hj
    have hrow1 : rowAt (C.env i).Tm ((C.α : Int) * C.R, (C.α : Int) * i + C.β) j =
        C.t (C.R * j + i) + C.α * (C.R * j + i) + C.β := by
      have := rowAt_int (C.env i).Tm (off := ((C.α : Int) * C.R, (C.α : Int) * i + C.β)) j hoj
      simp only at this
      apply Int.ofNat.inj
      show (rowAt _ _ j : Int) = _
      rw [this]
      show ((C.t (C.R * j + i) : Nat) : Int) + _ = _
      push_cast
      grind
    rw [hrow0, hrow1] at c1
    rw [hrow1] at d1
    obtain ⟨q0, hq0, hq0'⟩ := e1 rfl hph
    rw [hrow0] at hq0'
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [← hs']
      refine Eq.trans ?_ (d1 x)
      have hδ : (if i + 1 == C.R then (1 : Int) else 0) =
          ((if i + 1 = C.R then 1 else 0 : Nat) : Int) := by
        by_cases hc : i + 1 = C.R <;> simp [hc]
      have hev : evC (C.cls ((i + 1) % C.R)).cn0 (j + (if i + 1 = C.R then 1 else 0)) 0 =
          evC cn' j 0 := by
        rw [hcn']
        unfold evC ClassC.cn0
        simp only [List.map_map]
        apply List.map_congr_left
        intro ab _
        simp only [Function.comp, A3.ev]
        congr 1
        rw [hδ]
        push_cast
        grind
      rw [hev]
    · intro a ha1 ha2
      have := c1 a ha1 ha2
      obtain ⟨q, hq1, hq2⟩ := exists_pre C.S1 C.gpre C.gper hm this
      refine ⟨q, ?_, hq2⟩
      have e : ((C.Δ : Int) * C.R) * (j : Int) + ((C.w0 : Int) + C.Δ * i + C.c) =
          ((C.w0 + C.Δ * (C.R * j + i) + C.c : Nat) : Int) := by push_cast; grind
      have hq1' : q ≤ (((C.Δ : Int) * C.R) * (j : Int) + ((C.w0 : Int) + C.Δ * i + C.c)).toNat := hq1
      rw [e, Int.toNat_natCast] at hq1'
      exact hq1'
    · have e2 : ((C.Δ : Int) * C.R) * (j : Int) + ((C.w0 : Int) + C.Δ * i) =
          ((C.w0 + C.Δ * (C.R * j + i) : Nat) : Int) := by push_cast; grind
      have hq0'' : (q0 : Int) = ((C.w0 + C.Δ * (C.R * j + i) : Nat) : Int) := by
        rw [hq0]; exact e2
      have : q0 = C.w0 + C.Δ * (C.R * j + i) := by exact_mod_cast hq0''
      rw [← this]
      exact hq0'

/-! ### The chain of rounds -/

theorem checkClass_range {C : CertD} {i : Nat} (h : checkClass C i = true) :
    C.k0 ≤ C.R * (C.cls i).j0 + i ∧ C.R * (C.cls i).j0 + i < C.k0 + C.R := by
  unfold checkClass checkClassL at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2⟩

theorem j0_le {C : CertD} {i : Nat} (h : checkClass C i = true) {j : Nat} (hk : C.k0 ≤ C.R * j + i) :
    (C.cls i).j0 ≤ j := by
  obtain ⟨-, h2⟩ := checkClass_range h
  have : C.R * (C.cls i).j0 < C.R * (j + 1) := by rw [Nat.mul_add]; omega
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left this)

theorem check_facts {C : CertD} (h : check C = true) :
    0 < C.R ∧ 0 < C.gper.length ∧ (∀ s ∈ C.S1, 0 < s) ∧ C.S1 ≠ [] ∧ C.gpre.length ≤ C.T0 ∧
    ∀ i, i < C.R → checkClass C i = true := by
  unfold check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hg, hall⟩ := h
  unfold globalOk at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨hR, -⟩, hp⟩, hne⟩, hS⟩, hgN⟩ := hg
  refine ⟨hR, hp, ?_, ?_, hgN, ?_⟩
  · intro s hs
    have := List.all_eq_true.1 hS s hs
    simpa using this
  · intro h0; simp [h0] at hne
  · intro i hi
    exact List.all_eq_true.1 hall i (List.mem_range.2 hi)

theorem chain (C : Cert) (h : check C.toCertD = true) :
    ∀ n j i, i < C.R → C.R * j + i = C.k0 + n →
      ∀ x, decode (C.cls i).init (evC (C.cls i).cn0 j 0) x = St C.S1 C.gpre C.gper (C.t (C.k0 + n)) x := by
  obtain ⟨hR, hp, hS, hne, hgN, hall⟩ := check_facts h
  intro n
  induction n with
  | zero =>
    intro j i hi hk x
    have hu := (Nat.div_mod_unique hR).2 (show i + C.R * j = C.k0 + 0 ∧ i < C.R by omega)
    obtain ⟨hj, hi'⟩ := hu
    subst hi' hj
    simpa [CertD.t_k0] using C.initOk x
  | succ n ih =>
    intro j i hi hk
    have hk1 : C.k0 ≤ C.R * j + i := by omega
    by_cases hi0 : i = 0
    · subst hi0
      have hj1 : 1 ≤ j := Nat.pos_of_ne_zero (fun hj0 => by subst hj0; omega)
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hR1 : C.R - 1 < C.R := by omega
      have hk' : C.R * j' + (C.R - 1) = C.k0 + n := by
        rw [Nat.mul_add] at hk; omega
      have hk'' : C.k0 ≤ C.R * j' + (C.R - 1) := by omega
      have ih' := ih j' (C.R - 1) hR1 hk'
      rw [← hk'] at ih'
      have := (checkClass_sound C.toCertD hp hS hne hgN (hall _ hR1) (j0_le (hall _ hR1) hk'') ih').1
      have e1 : (C.R - 1 + 1) % C.R = 0 := by
        rw [show C.R - 1 + 1 = C.R by omega]; exact Nat.mod_self _
      have e2 : C.R - 1 + 1 = C.R := by omega
      have ts := C.t_succ (k := C.R * j' + (C.R - 1)) hk''
      intro x
      have := this x
      simp only [e2, Nat.mod_self, ↓reduceIte] at this
      rw [show C.k0 + (n + 1) = C.R * j' + (C.R - 1) + 1 by omega, ts]
      exact this
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hi1 : i' < C.R := by omega
      have hk' : C.R * j + i' = C.k0 + n := by omega
      have hk'' : C.k0 ≤ C.R * j + i' := by omega
      have ih' := ih j i' hi1 hk'
      rw [← hk'] at ih'
      have := (checkClass_sound C.toCertD hp hS hne hgN (hall _ hi1) (j0_le (hall _ hi1) hk'') ih').1
      have e1 : (i' + 1) % C.R = i' + 1 := Nat.mod_eq_of_lt hi
      have e2 : ¬ (i' + 1 = C.R) := by omega
      have ts := C.t_succ (k := C.R * j + i') hk''
      intro x
      have := this x
      simp only [e1, e2, ↓reduceIte, Nat.add_zero] at this
      rw [show C.k0 + (n + 1) = C.R * j + i' + 1 by omega, ts]
      exact this

/-! ### The theorem -/

/-- **Wall law of a family.**  Let `C` pass `check` and carry a true initial run (`initOk`).  Then the
round starts `t k` (`t k0 = T0`, `t (k+1) = t k + α k + β`, closed form below) satisfy, for every
`k ≥ k0`: row `t k` of `PG` is `π`-periodic from exactly column `w0 + Δ k`, and every row `a` of
round `k` is `π`-periodic from some least column `q ≤ w0 + Δ k + c`. -/
theorem family_wall (C : Cert) (h : check C.toCertD = true) :
    C.t C.k0 = C.T0 ∧ ∀ k, C.k0 ≤ k →
      C.t (k + 1) = C.t k + C.α * k + C.β ∧
      2 * (C.t k : Int) = 2 * C.T0 + 2 * C.β * ((k : Int) - C.k0) +
        C.α * ((k : Int) * (k - 1) - (C.k0 : Int) * (C.k0 - 1)) ∧
      IsPreG C.S1 C.gpre C.gper C.π (C.t k) (C.w0 + C.Δ * k) ∧
      ∀ a, C.t k ≤ a → a < C.t (k + 1) →
        ∃ q, IsPreG C.S1 C.gpre C.gper C.π a q ∧ q ≤ C.w0 + C.Δ * k + C.c := by
  refine ⟨C.t_k0, fun k hk => ⟨C.t_succ hk, C.t_closed hk, ?_⟩⟩
  obtain ⟨hR, hp, hS, hne, hgN, hall⟩ := check_facts h
  have hmod : C.R * (k / C.R) + k % C.R = k := Nat.div_add_mod k C.R
  have hi : k % C.R < C.R := Nat.mod_lt _ hR
  have hk' : C.R * (k / C.R) + k % C.R = C.k0 + (k - C.k0) := by omega
  have hch := chain C h (k - C.k0) (k / C.R) (k % C.R) hi hk'
  have hjle := j0_le (hall _ hi) (show C.k0 ≤ C.R * (k / C.R) + k % C.R by omega)
  have hkk : C.k0 + (k - C.k0) = k := by omega
  rw [hkk] at hch
  have hch' : ∀ x, decode (C.cls (k % C.R)).init (evC (C.cls (k % C.R)).cn0 (k / C.R) 0) x =
      St C.S1 C.gpre C.gper (C.t (C.R * (k / C.R) + k % C.R)) x := by
    rw [hmod]; exact hch
  obtain ⟨-, h2, h3⟩ := checkClass_sound C.toCertD hp hS hne hgN (hall _ hi) hjle hch'
  rw [hmod] at h2 h3
  refine ⟨h3, fun a ha1 ha2 => ?_⟩
  rw [C.t_succ hk] at ha2
  obtain ⟨q, hq1, hq2⟩ := h2 a ha1 ha2
  exact ⟨q, hq2, hq1⟩

/-- the statement of `family_wall`, as a named proposition -/
def WallLaw (C : CertD) : Prop :=
  C.t C.k0 = C.T0 ∧ ∀ k, C.k0 ≤ k →
    C.t (k + 1) = C.t k + C.α * k + C.β ∧
    2 * (C.t k : Int) = 2 * C.T0 + 2 * C.β * ((k : Int) - C.k0) +
      C.α * ((k : Int) * (k - 1) - (C.k0 : Int) * (C.k0 - 1)) ∧
    IsPreG C.S1 C.gpre C.gper C.π (C.t k) (C.w0 + C.Δ * k) ∧
    ∀ a, C.t k ≤ a → a < C.t (k + 1) →
      ∃ q, IsPreG C.S1 C.gpre C.gper C.π a q ∧ q ≤ C.w0 + C.Δ * k + C.c

theorem family_wall_law (C : Cert) (h : check C.toCertD = true) : WallLaw C.toCertD :=
  family_wall C h

/-- `IsPreG` stated with the game outcome of `LeadA` -/
def IsPreO (S1 S2 : List Nat) (π a q : Nat) : Prop :=
  (∀ d, q ≤ d → LeadA.outcome S1 S2 a (a + (d + π)) = LeadA.outcome S1 S2 a (a + d)) ∧
  ∀ q', q' < q → ∃ d, q' ≤ d ∧ LeadA.outcome S1 S2 a (a + (d + π)) ≠ LeadA.outcome S1 S2 a (a + d)

theorem IsPreG_to_O {S1 S2 gpre gper : List Nat} (hS : ∀ s ∈ S1, 0 < s)
    (hg : ∀ x, LeadA.sgFn S2 x = gv gpre gper x) {π a q : Nat} (h : IsPreG S1 gpre gper π a q) :
    IsPreO S1 S2 π a q := by
  unfold IsPreG at h
  unfold IsPreO
  simp only [outcome_eq_PG S1 S2 gpre gper hS hg]
  exact h

/-- the same law for the game `LeadA.outcome S1 S2`, when `g` is the Grundy function of `Sub(S2)` -/
theorem family_wall_outcome (C : Cert) (S2 : List Nat) (hg : ∀ x, LeadA.sgFn S2 x = gv C.gpre C.gper x)
    (h : check C.toCertD = true) :
    C.t C.k0 = C.T0 ∧ ∀ k, C.k0 ≤ k →
      C.t (k + 1) = C.t k + C.α * k + C.β ∧
      2 * (C.t k : Int) = 2 * C.T0 + 2 * C.β * ((k : Int) - C.k0) +
        C.α * ((k : Int) * (k - 1) - (C.k0 : Int) * (C.k0 - 1)) ∧
      IsPreO C.S1 S2 C.π (C.t k) (C.w0 + C.Δ * k) ∧
      ∀ a, C.t k ≤ a → a < C.t (k + 1) →
        ∃ q, IsPreO C.S1 S2 C.π a q ∧ q ≤ C.w0 + C.Δ * k + C.c := by
  obtain ⟨-, -, hS, -⟩ := check_facts h
  obtain ⟨h0, hk⟩ := family_wall C h
  refine ⟨h0, fun k hk' => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hk k hk'
  refine ⟨a1, a2, IsPreG_to_O hS hg a3, fun a ha1 ha2 => ?_⟩
  obtain ⟨q, hq, hq'⟩ := a4 a ha1 ha2
  exact ⟨q, IsPreG_to_O hS hg hq, hq'⟩

/-! ### Generator support (not used in proofs) -/

/-- Fill in the counter shift `d` of every cycle phase of a class by running one iteration at `t = 0`
(guards at `t = 0` are the same with or without the `t`-coefficient).  Emitter helper only; the
filled phases are then checked by `check`. -/
def probePhases (env : Env) (j0 : Nat) :
    Bool → List PhaseC → Shape → List A3 → Int × Int → Option (List PhaseC)
  | _, [], _, _, _ => some []
  | first, ph :: phs, s, cn, off =>
    let ph' : Option PhaseC :=
      match ph with
      | .step .. => some ph
      | .cycle len ca cb _ rts mvs =>
        match runBody env ⟨j0, 0, 1⟩ off len true false 0 rts mvs s cn with
        | none => none
        | some (_, cn1) => some (.cycle len ca cb (List.zipWith (fun x y => y.b - x.b) cn cn1) rts mvs)
    match ph' with
    | none => none
    | some ph1 =>
      match runPhase env j0 first ph1 s cn off with
      | none => none
      | some (s1, cn1, off1) => (probePhases env j0 false phs s1 cn1 off1).map (ph1 :: ·)

def PhaseC.dOf : PhaseC → List (List Int)
  | .step .. => []
  | .cycle _ _ _ d .. => [d]

def statesAt (env : Env) (j0 : Nat) :
    Bool → List PhaseC → List Nat → Shape → List A3 → Int × Int →
      Option (List (Shape × List A3 × Int × Int))
  | _, _, [], _, _, _ => some []
  | first, phs, n :: ns, s, cn, off =>
    match runPhases env j0 first (phs.take n) s cn off with
    | none => none
    | some (s1, cn1, off1) =>
      (statesAt env j0 false (phs.drop n) ns s1 cn1 off1).map ((s1, cn1, off1) :: ·)

def intSrc (i : Int) : String := if i < 0 then s!"({i} : Int)" else toString i
def listSrc {α : Type} (f : α → String) (xs : List α) : String := "[" ++ ", ".intercalate (xs.map f) ++ "]"
def shapeSrc (s : Shape) : String :=
  "⟨" ++ listSrc toString s.x0 ++ ", " ++
    listSrc (fun (yx : List Nat × List Nat) => "(" ++ listSrc toString yx.1 ++ ", " ++ listSrc toString yx.2 ++ ")")
      s.blocks ++ ", " ++ listSrc toString s.z ++ "⟩"
def a3Src (x : A3) : String := "⟨" ++ intSrc x.a ++ ", " ++ intSrc x.e ++ ", " ++ intSrc x.b ++ "⟩"
def stateSrc (r : Shape × List A3 × Int × Int) : String :=
  shapeSrc r.1 ++ " | " ++ listSrc a3Src r.2.1 ++ " | (" ++ intSrc r.2.2.1 ++ ", " ++ intSrc r.2.2.2 ++ ")"

/-- Emitter probe for class `i` (its chunks are ignored, only the phases are read): the counter shifts of
the cycles (`D ...` line, one list per cycle) and the states after each of the `cuts` (phase counts,
one `S shape | counters | offset` line each). -/
def probeRun (C : CertD) (i : Nat) (cuts : List Nat) : IO Unit := do
  let cl := C.cls i
  let phs := cl.chunks.flatMap (·.phases)
  match probePhases (C.env i) cl.j0 true phs cl.init cl.cn0 (0, 0) with
  | none => IO.println "FAIL probe"
  | some phs' =>
    IO.println ("D " ++ listSrc (listSrc toString) (phs'.flatMap PhaseC.dOf))
    match statesAt (C.env i) cl.j0 true phs' cuts cl.init cl.cn0 (0, 0) with
    | none => IO.println "FAIL states"
    | some sts => for r in sts do IO.println ("S " ++ stateSrc r)

end Family
