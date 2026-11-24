import FamilyRound
/-!
Wall predicates for the round checker.

* `IsPreG S1 gpre gper π a q`: row `a` of `PG` is `π`-periodic from column `q`, and `q` is least.
* `PerFrom w π q`: bit 0 of the letters of the word `w` is `π`-periodic from `q` (for `w = St (a+1)` this
  says row `a` is periodic, `perFrom_iff`).
* `perFromB xb z π q`: Bool check on the word `xb ++ z^ω` (last boundary and tail of a shape);
  `perFromB_sound`.  `misB`: a witness that `q` is least.
* `startA`: the (affine) column where the last boundary of a shape starts.
-/
namespace Family

/-! ### Periodicity of the bit-0 word -/

def PerFrom (w : Nat → Nat) (π q : Nat) : Prop := ∀ d, q ≤ d → w (d + π) % 2 = w d % 2

theorem PerFrom_mono {w : Nat → Nat} {π q q' : Nat} (h : PerFrom w π q) (hq : q ≤ q') :
    PerFrom w π q' := fun d hd => h d (Nat.le_trans hq hd)

def IsPreG (S1 gpre gper : List Nat) (π a q : Nat) : Prop :=
  (∀ d, q ≤ d → PG S1 gpre gper a (a + (d + π)) = PG S1 gpre gper a (a + d)) ∧
  ∀ q', q' < q → ∃ d, q' ≤ d ∧ PG S1 gpre gper a (a + (d + π)) ≠ PG S1 gpre gper a (a + d)

theorem mod2_iff (x y : Nat) : x % 2 = y % 2 ↔ decide (x % 2 = 1) = decide (y % 2 = 1) := by
  by_cases hx : x % 2 = 1 <;> by_cases hy : y % 2 = 1 <;> simp [hx, hy] <;> omega

theorem mOf_pos (S1 : List Nat) (hS : ∀ s ∈ S1, 0 < s) (hne : S1 ≠ []) : 0 < mOf S1 := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil S1 hne
  have := le_mOf S1 s hs
  have := hS s hs
  omega

theorem perFrom_iff (S1 gpre gper : List Nat) (hm : 0 < mOf S1) (π a q : Nat) :
    PerFrom (St S1 gpre gper (a + 1)) π q ↔
      ∀ d, q ≤ d → PG S1 gpre gper a (a + (d + π)) = PG S1 gpre gper a (a + d) := by
  have key : ∀ d, (St S1 gpre gper (a + 1) (d + π) % 2 = St S1 gpre gper (a + 1) d % 2) ↔
      PG S1 gpre gper a (a + (d + π)) = PG S1 gpre gper a (a + d) := by
    intro d
    rw [mod2_iff]
    have h1 := R_of_St S1 gpre gper hm a (d + π)
    have h2 := R_of_St S1 gpre gper hm a d
    unfold R at h1 h2
    rw [← h1, ← h2]
  constructor
  · intro h d hd; exact (key d).1 (h d hd)
  · intro h d hd; exact (key d).2 (h d hd)

theorem mis_iff (S1 gpre gper : List Nat) (hm : 0 < mOf S1) (π a d : Nat) :
    St S1 gpre gper (a + 1) (d + π) % 2 ≠ St S1 gpre gper (a + 1) d % 2 ↔
      PG S1 gpre gper a (a + (d + π)) ≠ PG S1 gpre gper a (a + d) := by
  have key := perFrom_iff S1 gpre gper hm π a d
  have h1 := R_of_St S1 gpre gper hm a (d + π)
  have h2 := R_of_St S1 gpre gper hm a d
  unfold R at h1 h2
  rw [Ne, Ne, mod2_iff, ← h1, ← h2]

theorem least_onset (E : Nat → Prop) : ∀ P : Nat, (∀ d, P ≤ d → E d) →
    ∃ q, q ≤ P ∧ (∀ d, q ≤ d → E d) ∧ ∀ q', q' < q → ∃ d, q' ≤ d ∧ ¬ E d := by
  intro P
  induction P with
  | zero => intro h; exact ⟨0, Nat.le_refl _, h, fun q' hq' => by omega⟩
  | succ P ih =>
    intro h
    by_cases hP : ∀ d, P ≤ d → E d
    · obtain ⟨q, hq, h1, h2⟩ := ih hP
      exact ⟨q, by omega, h1, h2⟩
    · refine ⟨P + 1, Nat.le_refl _, h, fun q' hq' => ?_⟩
      have : ∃ d, P ≤ d ∧ ¬ E d := by
        by_cases hc : ∃ d, P ≤ d ∧ ¬ E d
        · exact hc
        · exact absurd (fun d hd => by
            by_cases hE : E d
            · exact hE
            · exact absurd ⟨d, hd, hE⟩ hc) hP
      obtain ⟨d, hd, hn⟩ := this
      exact ⟨d, by omega, hn⟩

/-- a periodic row has a least onset `q <= P` -/
theorem exists_pre (S1 gpre gper : List Nat) (hm : 0 < mOf S1) {π a P : Nat}
    (h : PerFrom (St S1 gpre gper (a + 1)) π P) : ∃ q, q ≤ P ∧ IsPreG S1 gpre gper π a q := by
  have h' := (perFrom_iff S1 gpre gper hm π a P).1 h
  obtain ⟨q, hq, h1, h2⟩ := least_onset
    (fun d => PG S1 gpre gper a (a + (d + π)) = PG S1 gpre gper a (a + d)) P h'
  exact ⟨q, hq, h1, h2⟩

/-- exact onset: periodic from `P`, mismatch at `P - 1` -/
theorem isPre_of (S1 gpre gper : List Nat) (hm : 0 < mOf S1) {π a P : Nat}
    (h : PerFrom (St S1 gpre gper (a + 1)) π P) (hP : 1 ≤ P)
    (hmis : St S1 gpre gper (a + 1) (P - 1 + π) % 2 ≠ St S1 gpre gper (a + 1) (P - 1) % 2) :
    IsPreG S1 gpre gper π a P := by
  refine ⟨(perFrom_iff S1 gpre gper hm π a P).1 h, fun q' hq' => ⟨P - 1, by omega, ?_⟩⟩
  exact (mis_iff S1 gpre gper hm π a (P - 1)).1 hmis

/-! ### The finite check on `xb ++ z^ω` -/

theorem cat_word (xb z : List Nat) (hz : z ≠ []) (c : Nat) (i : Nat) (hi : i < xb.length + (rep z c).length) :
    cat xb (per z) i = (xb ++ rep z c).getD i 0 := by
  rw [per_rep hz c, ← cat_append]
  rw [cat_lt (by simpa using hi)]

theorem map_mod2_getD (l : List Nat) (i : Nat) : (l.map (· % 2)).getD i 0 = l.getD i 0 % 2 := by
  by_cases h : i < l.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  · have : l[i]? = none := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, this]

def bitsOf (xb z : List Nat) (π : Nat) : List Nat := (xb ++ rep z (π + 1)).map (· % 2)

/-- bit 0 of `xb ++ z^ω` is `π`-periodic from `q` -/
def perFromB (xb z : List Nat) (π q : Nat) : Bool :=
  !z.isEmpty &&
  ((((bitsOf xb z π).drop q).take (xb.length - q)) == (((bitsOf xb z π).drop (q + π)).take (xb.length - q))) &&
  (List.range z.length).all fun e => z.getD ((e + π) % z.length) 0 % 2 == z.getD e 0 % 2

theorem per_shift_mod2 (z : List Nat) (π : Nat) (hz : z ≠ [])
    (h : ((List.range z.length).all fun e => z.getD ((e + π) % z.length) 0 % 2 == z.getD e 0 % 2) = true)
    (e : Nat) : per z (e + π) % 2 = per z e % 2 := by
  have hl : 0 < z.length := List.length_pos_iff.2 hz
  rw [List.all_eq_true] at h
  have := h (e % z.length) (List.mem_range.2 (Nat.mod_lt _ hl))
  rw [beq_iff_eq, Nat.mod_add_mod] at this
  unfold per
  exact this

theorem bitsOf_getD (xb z : List Nat) (π i : Nat) :
    (bitsOf xb z π).getD i 0 = (xb ++ rep z (π + 1)).getD i 0 % 2 := map_mod2_getD _ _

theorem perFromB_sound {xb z : List Nat} {π q : Nat} (h : perFromB xb z π q = true) :
    PerFrom (cat xb (per z)) π q := by
  simp only [perFromB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq] at h
  obtain ⟨⟨hz, hl⟩, hr⟩ := h
  have hzl : 0 < z.length := List.length_pos_iff.2 hz
  have hrep : (rep z (π + 1)).length = z.length * (π + 1) := rep_length z (π + 1)
  have hge : π + 1 ≤ (rep z (π + 1)).length := by
    rw [hrep]; exact Nat.le_trans (Nat.le_mul_of_pos_left _ hzl) (Nat.le_refl _) |> fun _ => by
      have := Nat.mul_le_mul_right (π + 1) hzl; omega
  intro d hd
  by_cases hdl : d < xb.length
  · have e1 := congrArg (fun l => l.getD (d - q) 0) hl
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop] at e1
    have hi : d - q < xb.length - q := by omega
    simp only [hi, ↓reduceIte, show q + (d - q) = d by omega,
      show q + π + (d - q) = d + π by omega] at e1
    have c1 := cat_word xb z hz (π + 1) d (by omega)
    have c2 := cat_word xb z hz (π + 1) (d + π) (by omega)
    rw [c1, c2]
    have b1 := bitsOf_getD xb z π d
    have b2 := bitsOf_getD xb z π (d + π)
    simp only [List.getD_eq_getElem?_getD] at b1 b2 ⊢
    rw [← b1, ← b2]
    exact e1.symm
  · have hd' : xb.length ≤ d := by omega
    unfold PerFrom at *
    rw [cat_ge hd', cat_ge (by omega), show d + π - xb.length = (d - xb.length) + π by omega]
    exact per_shift_mod2 z π hz hr _

/-- `q` is a mismatch position of `xb ++ z^ω` -/
def misB (xb z : List Nat) (π d : Nat) : Bool :=
  !z.isEmpty && decide (d < xb.length) && decide ((bitsOf xb z π).getD (d + π) 0 ≠ (bitsOf xb z π).getD d 0)

theorem misB_sound {xb z : List Nat} {π d : Nat} (h : misB xb z π d = true) :
    cat xb (per z) (d + π) % 2 ≠ cat xb (per z) d % 2 := by
  simp only [misB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    decide_eq_true_eq] at h
  obtain ⟨⟨hz, hd⟩, hne⟩ := h
  have hzl : 0 < z.length := List.length_pos_iff.2 hz
  have hrep : (rep z (π + 1)).length = z.length * (π + 1) := rep_length z (π + 1)
  have hge : π + 1 ≤ (rep z (π + 1)).length := by
    rw [hrep]; have := Nat.mul_le_mul_right (π + 1) hzl; omega
  rw [cat_word xb z hz (π + 1) d (by omega), cat_word xb z hz (π + 1) (d + π) (by omega)]
  rw [bitsOf_getD, bitsOf_getD] at hne
  exact hne

/-! ### Position of the last boundary -/

def lastBd : List Nat → Blocks → List Nat
  | x, [] => x
  | _, b :: bs => lastBd b.2 bs

/-- number of letters before the last boundary -/
def startL : List Nat → Blocks → List Nat → Nat
  | _, [], _ => 0
  | x, (y, x') :: bs, ns => x.length + y.length * ns.headD 0 + startL x' bs ns.tail

theorem fin_split : ∀ (bs : Blocks) (x : List Nat) (ns : List Nat),
    ∃ pre : List Nat, pre.length = startL x bs ns ∧ x ++ finAux bs ns = pre ++ lastBd x bs := by
  intro bs
  induction bs with
  | nil => intro x ns; exact ⟨[], by simp [startL], by simp [finAux, lastBd]⟩
  | cons b bs ih =>
    obtain ⟨y, x'⟩ := b
    intro x ns
    obtain ⟨pre', hl, he⟩ := ih x' ns.tail
    refine ⟨x ++ rep y (ns.headD 0) ++ pre', ?_, ?_⟩
    · simp [startL, rep_length, hl]; omega
    · simp only [finAux, lastBd]
      rw [← List.append_assoc, List.append_assoc x, List.append_assoc x, he]
      simp [List.append_assoc]

theorem decode_last (s : Shape) (n : List Nat) (d : Nat) :
    decode s n (startL s.x0 s.blocks n + d) = cat (lastBd s.x0 s.blocks) (per s.z) d := by
  obtain ⟨pre, hl, he⟩ := fin_split s.blocks s.x0 n
  rw [decode_def, he, cat_append, ← hl, cat_ge (by omega)]
  congr 1; omega

/-- affine version of `startL` -/
def startA : List Nat → Blocks → List A3 → A3
  | _, [], _ => ⟨0, 0, 0⟩
  | x, (y, x') :: bs, cn =>
    let c := cn.headD ⟨0, 0, 0⟩
    let r := startA x' bs cn.tail
    ⟨y.length * c.a + r.a, y.length * c.e + r.e, x.length + y.length * c.b + r.b⟩

theorem startA_ev : ∀ (bs : Blocks) (x : List Nat) (cn : List A3) {j t : Nat}, Pos cn j t →
    (startA x bs cn).ev j t = (startL x bs (evC cn j t) : Int) := by
  intro bs
  induction bs with
  | nil => intro x cn j t hp; simp [startA, startL, A3.ev]
  | cons b bs ih =>
    obtain ⟨y, x'⟩ := b
    intro x cn j t hp
    have ht : Pos cn.tail j t := fun u hu => hp u (List.mem_of_mem_tail hu)
    have h1 := ih x' cn.tail ht
    have hc : (evC cn j t).headD 0 = ((cn.headD ⟨0, 0, 0⟩).ev j t).toNat := by
      cases cn with
      | nil => simp [evC, A3.ev]
      | cons c cs => simp [evC]
    have hnn : 0 ≤ (cn.headD ⟨0, 0, 0⟩).ev j t := by
      cases cn with
      | nil => simp [A3.ev]
      | cons c cs => exact Pos_head hp
    have htl : (evC cn j t).tail = evC cn.tail j t := by simp [evC, List.map_tail]
    simp only [startA, startL, A3.ev] at h1 ⊢
    rw [hc, htl]
    push_cast
    have : (((cn.headD ⟨0, 0, 0⟩).ev j t).toNat : Int) = (cn.headD ⟨0, 0, 0⟩).ev j t := by omega
    rw [this]
    unfold A3.ev at *
    rw [← h1]
    grind

/-! ### Wall check of one shape -/

/-- offset of the affine position `P` from the start of the last boundary -/
def wallO (P : Int × Int) (s : Shape) (cn : List A3) : A3 :=
  let S := startA s.x0 s.blocks cn
  ⟨P.1 - S.a, -S.e, P.2 - S.b⟩

theorem wallO_ev (P : Int × Int) (s : Shape) (cn : List A3) {j t : Nat} (hp : Pos cn j t) :
    (wallO P s cn).ev j t = P.1 * j + P.2 - (startL s.x0 s.blocks (evC cn j t) : Int) := by
  have h := startA_ev s.blocks s.x0 cn hp
  unfold A3.ev at h ⊢
  unfold wallO
  rw [← h]
  simp only
  grind

/-- Bit 0 of the word of shape `s` (counters `cn`) is `π`-periodic from the affine position
`P = (pa, pb)` (in `j`), for every `(j, t)` of the domain. -/
def wallOk (cx : Cx) (π : Nat) (P : Int × Int) (s : Shape) (cn : List A3) : Bool :=
  nn cx (wallO P s cn) && perFromB (lastBd s.x0 s.blocks) s.z π (lbOf cx (wallO P s cn)).toNat

theorem lbOf_nonneg {cx : Cx} {x : A3} (h : nn cx x = true) : 0 ≤ lbOf cx x := by
  simp only [nn, Bool.and_eq_true, posA, decide_eq_true_eq] at h
  unfold lbOf
  omega

theorem wallOk_sound {cx : Cx} {π : Nat} {P : Int × Int} {s : Shape} {cn : List A3}
    (h : wallOk cx π P s cn = true) {j t : Nat} (hd : cx.dom j t) (hp : Pos cn j t) :
    PerFrom (decode s (evC cn j t)) π (P.1 * j + P.2).toNat := by
  simp only [wallOk, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hb := perFromB_sound h2
  have hge := nn_min h1 hd
  have hnn := lbOf_nonneg h1
  have hS := wallO_ev P s cn hp
  generalize lbOf cx (wallO P s cn) = lb at hge hnn hb
  generalize (wallO P s cn).ev j t = ev at hge hS
  obtain ⟨S, hSd⟩ : ∃ S, S = startL s.x0 s.blocks (evC cn j t) := ⟨_, rfl⟩
  rw [← hSd] at hS
  intro d hd'
  have hdS : S ≤ d := by omega
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hdS
  rw [show S + d' + π = S + (d' + π) by omega, hSd, decode_last, decode_last]
  exact hb d' (by omega)

/-- Exact onset at the affine position `P0`: the offset from the last boundary is a constant `o >= 1`,
periodic from there and not from `o - 1`. -/
def wallEx (π : Nat) (P0 : Int × Int) (s : Shape) (cn : List A3) : Bool :=
  let O := wallO P0 s cn
  O.a == 0 && O.e == 0 && decide (1 ≤ O.b) && perFromB (lastBd s.x0 s.blocks) s.z π O.b.toNat &&
    misB (lastBd s.x0 s.blocks) s.z π (O.b.toNat - 1)

theorem wallEx_sound {π : Nat} {P0 : Int × Int} {s : Shape} {cn : List A3}
    (h : wallEx π P0 s cn = true) {j t : Nat} (hp : Pos cn j t) :
    ∃ P : Nat, (P : Int) = P0.1 * j + P0.2 ∧ 1 ≤ P ∧ PerFrom (decode s (evC cn j t)) π P ∧
      decode s (evC cn j t) (P - 1 + π) % 2 ≠ decode s (evC cn j t) (P - 1) % 2 := by
  simp only [wallEx, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨ha, he⟩, hb1⟩, hper⟩, hmis⟩ := h
  have hS := wallO_ev P0 s cn hp
  have hev : (wallO P0 s cn).ev j t = (wallO P0 s cn).b := by simp [A3.ev, ha, he]
  generalize wallO P0 s cn = O at *
  obtain ⟨S, hSd⟩ : ∃ S, S = startL s.x0 s.blocks (evC cn j t) := ⟨_, rfl⟩
  rw [← hSd] at hS
  have hpf := perFromB_sound hper
  have hm := misB_sound hmis
  have hlt : (misB (lastBd s.x0 s.blocks) s.z π (O.b.toNat - 1)) = true := hmis
  refine ⟨S + O.b.toNat, by omega, by omega, ?_, ?_⟩
  · intro d hd
    obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le (show S ≤ d by omega)
    rw [show S + d' + π = S + (d' + π) by omega, hSd, decode_last, decode_last]
    exact hpf d' (by omega)
  · rw [show S + O.b.toNat - 1 + π = S + (O.b.toNat - 1 + π) by omega,
      show S + O.b.toNat - 1 = S + (O.b.toNat - 1) by omega, hSd, decode_last, decode_last]
    exact hm

end Family
