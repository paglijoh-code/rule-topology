/-
The equation of the model on the "virtual tables": `Lrow r e` (L phase) and `Rrow s e` (R phase)
extended to all columns e in Z, with no left boundary.  Everything here is k-free.
`EqF f r e` is the game equation (P iff the g-test passes and no S1 move reaches P) for the table f
at (r, e): the cell (r, e) moves to (r - s, e + s) and (r, e - s) (rows a, columns d = b - a, valid
away from the diagonal d < 6).
-/
import SqrtModel
namespace SqrtM

def EqF (f : Nat → Int → Bool) (r : Nat) (e : Int) : Bool :=
  f r e == (e % 5 != 0 && !f (r-1) (e+1) && !f r (e-1) && !f (r-2) (e+2) && !f r (e-2)
    && !f (r-5) (e+5) && !f r (e-5) && !f (r-6) (e+6) && !f r (e-6))

theorem EqF_congr (f g : Nat → Int → Bool) (r : Nat) (e : Int)
    (hf : ∀ s : Nat, s ∈ [0, 1, 2, 5, 6] → f (r - s) (e + s) = g (r - s) (e + s))
    (hg : ∀ s : Nat, s ∈ [0, 1, 2, 5, 6] → f r (e - s) = g r (e - s)) :
    EqF f r e = EqF g r e := by
  have h0 : f r e = g r e := by simpa using hf 0 (by simp)
  have a1 : f (r-1) (e+1) = g (r-1) (e+1) := by simpa using hf 1 (by simp)
  have a2 : f (r-2) (e+2) = g (r-2) (e+2) := by simpa using hf 2 (by simp)
  have a5 : f (r-5) (e+5) = g (r-5) (e+5) := by simpa using hf 5 (by simp)
  have a6 : f (r-6) (e+6) = g (r-6) (e+6) := by simpa using hf 6 (by simp)
  have b1 : f r (e-1) = g r (e-1) := by simpa using hg 1 (by simp)
  have b2 : f r (e-2) = g r (e-2) := by simpa using hg 2 (by simp)
  have b5 : f r (e-5) = g r (e-5) := by simpa using hg 5 (by simp)
  have b6 : f r (e-6) = g r (e-6) := by simpa using hg 6 (by simp)
  unfold EqF
  rw [h0, a1, a2, a5, a6, b1, b2, b5, b6]

/-- A table that is row-periodic mod 7 and column-periodic mod pc (5 | pc) satisfies the equation
everywhere (rows >= 6) as soon as it does on one period. -/
theorem EqF_pure (f : Nat → Int → Bool) (pc : Nat) (h5 : 5 ∣ pc) (hpc : 0 < pc)
    (hrow : ∀ r r' e, r % 7 = r' % 7 → f r e = f r' e)
    (hcol : ∀ r e e', (e - e') % (pc : Int) = 0 → f r e = f r e')
    (hfin : ∀ z, z < 7 → ∀ j, j < pc → EqF f (z + 7) (j : Int) = true) :
    ∀ r, 6 ≤ r → ∀ e, EqF f r e = true := by
  intro r hr e
  have hcl : ∀ r' (x : Int) (s : Int), f r' (x + s) = f r' ((x % (pc : Int)) + s) := by
    intro r' x s
    apply hcol
    have e1 : x + s - (x % (pc : Int) + s) = (pc : Int) * (x / (pc : Int)) := by
      have := Int.mul_ediv_add_emod x (pc : Int)
      omega
    rw [e1]; exact Int.mul_emod_right _ _
  have hcl' : ∀ r' (x : Int) (s : Int), f r' (x - s) = f r' ((x % (pc : Int)) - s) := by
    intro r' x s
    have := hcl r' x (-s)
    simpa [Int.sub_eq_add_neg] using this
  have hrw : ∀ s, s ≤ 6 → ∀ x, f (r - s) x = f (r % 7 + 7 - s) x := by
    intro s hs x
    apply hrow
    omega
  have hm : (e % (pc : Int)) % 5 = e % 5 := Int.emod_emod_of_dvd e (by exact_mod_cast h5)
  have hr0 : ∀ x, f r x = f (r % 7 + 7) x := fun x => hrow _ _ _ (by omega)
  have key : EqF f r e = EqF f (r % 7 + 7) (e % (pc : Int)) := by
    unfold EqF
    simp only [hr0, hrw 1 (by omega), hrw 2 (by omega), hrw 5 (by omega), hrw 6 (by omega), hm]
    simp only [hcl _ e 1, hcl _ e 2, hcl _ e 5, hcl _ e 6, hcl' _ e 1, hcl' _ e 2, hcl' _ e 5,
      hcl' _ e 6]
    have hc0 : ∀ r' (x : Int), f r' x = f r' (x % (pc : Int)) := by
      intro r' x
      have := hcl r' x 0
      simpa using this
    rw [hc0 (r % 7 + 7) e]
  rw [key]
  have hpos : 0 ≤ e % (pc : Int) := Int.emod_nonneg _ (by omega)
  have hlt : e % (pc : Int) < pc := Int.emod_lt_of_pos _ (by omega)
  have := hfin (r % 7) (by omega) (e % (pc : Int)).toNat (by omega)
  rwa [Int.toNat_of_nonneg hpos] at this


theorem alpha_congr (x y : Int) (h : (x - y) % 35 = 0) : alpha x = alpha y := by
  unfold alpha
  have : x % 35 = y % 35 := by omega
  rw [this]

theorem beta_congr (x y : Int) (h : (x - y) % 35 = 0) : beta x = beta y := by
  unfold beta
  have : x % 35 = y % 35 := by omega
  rw [this]

theorem tl_congr (z : Nat) (x y : Int) (h : (x - y) % 10 = 0) : tl z x = tl z y := by
  unfold tl
  have : x % 10 = y % 10 := by omega
  rw [this]

/-- pure media as tables -/
def fa (r : Nat) (e : Int) : Bool := alpha (e - 5 * (r : Int))
def fb (r : Nat) (e : Int) : Bool := beta (e - 5 * (r : Int))
def ft (r : Nat) (e : Int) : Bool := tl (r % 7) e

theorem fa_ok : ∀ r, 6 ≤ r → ∀ e, EqF fa r e = true :=
  EqF_pure fa 35 (by omega) (by omega)
    (fun r r' e h => alpha_congr _ _ (by omega)) (fun r e e' h => alpha_congr _ _ (by omega))
    (by decide +kernel)

theorem fb_ok : ∀ r, 6 ≤ r → ∀ e, EqF fb r e = true :=
  EqF_pure fb 35 (by omega) (by omega)
    (fun r r' e h => beta_congr _ _ (by omega)) (fun r e e' h => beta_congr _ _ (by omega))
    (by decide +kernel)

theorem ft_ok : ∀ r, 6 ≤ r → ∀ e, EqF ft r e = true :=
  EqF_pure ft 10 (by omega) (by omega)
    (fun r r' e h => by unfold ft; rw [h]) (fun r e e' h => tl_congr _ _ _ (by omega))
    (by decide +kernel)

/-- row-periodic tables: reduce the row to its residue mod 7 (rows >= 6 stay >= 6). -/
theorem EqF_row7 (f : Nat → Int → Bool) (hrow : ∀ r r' e, r % 7 = r' % 7 → f r e = f r' e)
    (r : Nat) (hr : 6 ≤ r) (e : Int) : EqF f r e = EqF f (r % 7 + 7) e := by
  have hrw : ∀ s, s ≤ 6 → ∀ x, f (r - s) x = f (r % 7 + 7 - s) x := by
    intro s hs x
    apply hrow
    omega
  have hr0 : ∀ x, f r x = f (r % 7 + 7) x := fun x => hrow _ _ _ (by omega)
  unfold EqF
  simp only [hr0, hrw 1 (by omega), hrw 2 (by omega), hrw 5 (by omega), hrw 6 (by omega)]

def Eq9 (v0 v1 v2 v3 v4 v5 v6 v7 v8 : Bool) (m : Int) : Bool :=
  v0 == (m % 5 != 0 && !v1 && !v2 && !v3 && !v4 && !v5 && !v6 && !v7 && !v8)

/-- the equation for a one-dimensional medium f (u = e - 5 r) -/
def Eq1 (f : Int → Bool) (u : Int) : Bool :=
  Eq9 (f u) (f (u+6)) (f (u-1)) (f (u+12)) (f (u-2)) (f (u+30)) (f (u-5)) (f (u+36)) (f (u-6)) u

theorem EqF_skew (g : Int → Bool) (hg : ∀ x y, (x - y) % 35 = 0 → g x = g y) (r : Nat)
    (hr : 6 ≤ r) (e : Int) :
    EqF (fun r e => g (e - 5 * (r : Int))) r e = Eq1 g (e - 5 * (r : Int)) := by
  unfold EqF Eq1 Eq9
  have e1 : e % 5 = (e - 5 * (r : Int)) % 5 := by omega
  rw [← e1]
  have c1 : ∀ x : Int, g (x + 1 - 5 * ((r - 1 : Nat) : Int)) = g (x - 5 * (r:Int) + 6) := by
    intro x; apply hg; omega
  have c2 : ∀ x : Int, g (x + 2 - 5 * ((r - 2 : Nat) : Int)) = g (x - 5 * (r:Int) + 12) := by
    intro x; apply hg; omega
  have c5 : ∀ x : Int, g (x + 5 - 5 * ((r - 5 : Nat) : Int)) = g (x - 5 * (r:Int) + 30) := by
    intro x; apply hg; omega
  have c6 : ∀ x : Int, g (x + 6 - 5 * ((r - 6 : Nat) : Int)) = g (x - 5 * (r:Int) + 36) := by
    intro x; apply hg; omega
  have d1 : ∀ x : Int, g (x - 1 - 5 * (r:Int)) = g (x - 5 * (r:Int) - 1) := by
    intro x; apply hg; omega
  have d2 : ∀ x : Int, g (x - 2 - 5 * (r:Int)) = g (x - 5 * (r:Int) - 2) := by
    intro x; apply hg; omega
  have d5 : ∀ x : Int, g (x - 5 - 5 * (r:Int)) = g (x - 5 * (r:Int) - 5) := by
    intro x; apply hg; omega
  have d6 : ∀ x : Int, g (x - 6 - 5 * (r:Int)) = g (x - 5 * (r:Int) - 6) := by
    intro x; apply hg; omega
  simp only [c1, c2, c5, c6, d1, d2, d5, d6]

theorem alpha_eq1 (u : Int) : Eq1 alpha u = true := by
  have h := fa_ok 7 (by omega) (u + 35)
  have h2 : EqF fa 7 (u + 35) = Eq1 alpha (u + 35 - 5 * ((7 : Nat) : Int)) :=
    EqF_skew alpha alpha_congr 7 (by omega) (u + 35)
  rw [h2] at h
  simpa using h

theorem beta_eq1 (u : Int) : Eq1 beta u = true := by
  have h := fb_ok 7 (by omega) (u + 35)
  have h2 : EqF fb 7 (u + 35) = Eq1 beta (u + 35 - 5 * ((7 : Nat) : Int)) :=
    EqF_skew beta beta_congr 7 (by omega) (u + 35)
  rw [h2] at h
  simpa using h

/-- the alpha | beta seam picture in the coordinate c = e - p1L r (seam at c = 0) -/
def LA (c : Int) : Bool := if c < 0 then alpha (c - 9) else beta (c - 9)
def fLA (r : Nat) (e : Int) : Bool := LA (e - p1L r)
def dl (y s : Nat) : Int := if y < s then 35 else 0

theorem LA_neg (x : Int) (h : x < 0) : LA x = alpha (x - 9) := by unfold LA; simp [h]
theorem LA_pos (x : Int) (h : 0 ≤ x) : LA x = beta (x - 9) := by
  unfold LA; simp [Int.not_lt.2 h]

theorem LA_a (x δ : Int) (hδ : δ = 0 ∨ δ = 35) (h : x < 0) : LA (x - δ) = alpha (x - 9) := by
  rw [LA_neg _ (by omega)]; exact alpha_congr _ _ (by omega)
theorem LA_b (x δ : Int) (hδ : δ = 0 ∨ δ = 35) (h : 35 ≤ x) : LA (x - δ) = beta (x - 9) := by
  rw [LA_pos _ (by omega)]; exact beta_congr _ _ (by omega)

theorem dl_cases (y s : Nat) : dl y s = 0 ∨ dl y s = 35 := by unfold dl; split <;> simp

def EqLA (y : Nat) (c : Int) : Bool :=
  Eq9 (LA c) (LA (c + 6 - dl y 1)) (LA (c - 1)) (LA (c + 12 - dl y 2)) (LA (c - 2))
    (LA (c + 30 - dl y 5)) (LA (c - 5)) (LA (c + 36 - dl y 6)) (LA (c - 6)) (c + 1)

theorem EqLA_left (y : Nat) (c : Int) (h : c ≤ -37) : EqLA y c = true := by
  have := alpha_eq1 (c - 9)
  unfold EqLA Eq9
  unfold Eq1 Eq9 at this
  have e1 : (c + 1) % 5 = (c - 9) % 5 := by omega
  have l0 : LA c = alpha (c - 9) := LA_neg c (by omega)
  have l1 : LA (c + 6 - dl y 1) = alpha (c - 9 + 6) := by
    rw [LA_a (c + 6) _ (dl_cases y 1) (by omega)]; exact alpha_congr _ _ (by omega)
  have l2 : LA (c - 1) = alpha (c - 9 - 1) := by
    rw [LA_neg _ (by omega)]; exact alpha_congr _ _ (by omega)
  have l3 : LA (c + 12 - dl y 2) = alpha (c - 9 + 12) := by
    rw [LA_a (c + 12) _ (dl_cases y 2) (by omega)]; exact alpha_congr _ _ (by omega)
  have l4 : LA (c - 2) = alpha (c - 9 - 2) := by
    rw [LA_neg _ (by omega)]; exact alpha_congr _ _ (by omega)
  have l5 : LA (c + 30 - dl y 5) = alpha (c - 9 + 30) := by
    rw [LA_a (c + 30) _ (dl_cases y 5) (by omega)]; exact alpha_congr _ _ (by omega)
  have l6 : LA (c - 5) = alpha (c - 9 - 5) := by
    rw [LA_neg _ (by omega)]; exact alpha_congr _ _ (by omega)
  have l7 : LA (c + 36 - dl y 6) = alpha (c - 9 + 36) := by
    rw [LA_a (c + 36) _ (dl_cases y 6) (by omega)]; exact alpha_congr _ _ (by omega)
  have l8 : LA (c - 6) = alpha (c - 9 - 6) := by
    rw [LA_neg _ (by omega)]; exact alpha_congr _ _ (by omega)
  rw [l0, l1, l2, l3, l4, l5, l6, l7, l8, e1]
  exact this

theorem EqLA_right (y : Nat) (c : Int) (h : 29 ≤ c) : EqLA y c = true := by
  have := beta_eq1 (c - 9)
  unfold EqLA Eq9
  unfold Eq1 Eq9 at this
  have e1 : (c + 1) % 5 = (c - 9) % 5 := by omega
  have l0 : LA c = beta (c - 9) := LA_pos c (by omega)
  have l1 : LA (c + 6 - dl y 1) = beta (c - 9 + 6) := by
    rw [LA_b (c + 6) _ (dl_cases y 1) (by omega)]; exact beta_congr _ _ (by omega)
  have l2 : LA (c - 1) = beta (c - 9 - 1) := by
    rw [LA_pos _ (by omega)]; exact beta_congr _ _ (by omega)
  have l3 : LA (c + 12 - dl y 2) = beta (c - 9 + 12) := by
    rw [LA_b (c + 12) _ (dl_cases y 2) (by omega)]; exact beta_congr _ _ (by omega)
  have l4 : LA (c - 2) = beta (c - 9 - 2) := by
    rw [LA_pos _ (by omega)]; exact beta_congr _ _ (by omega)
  have l5 : LA (c + 30 - dl y 5) = beta (c - 9 + 30) := by
    rw [LA_b (c + 30) _ (dl_cases y 5) (by omega)]; exact beta_congr _ _ (by omega)
  have l6 : LA (c - 5) = beta (c - 9 - 5) := by
    rw [LA_pos _ (by omega)]; exact beta_congr _ _ (by omega)
  have l7 : LA (c + 36 - dl y 6) = beta (c - 9 + 36) := by
    rw [LA_b (c + 36) _ (dl_cases y 6) (by omega)]; exact beta_congr _ _ (by omega)
  have l8 : LA (c - 6) = beta (c - 9 - 6) := by
    rw [LA_pos _ (by omega)]; exact beta_congr _ _ (by omega)
  rw [l0, l1, l2, l3, l4, l5, l6, l7, l8, e1]
  exact this

theorem EqLA_mid : ∀ y : Nat, y < 6 → ∀ i : Nat, i < 66 → EqLA y ((i : Int) - 37) = true := by
  decide +kernel

theorem EqLA_all (y : Nat) (hy : y < 6) (c : Int) : EqLA y c = true := by
  by_cases h1 : c ≤ -37
  · exact EqLA_left y c h1
  by_cases h2 : 29 ≤ c
  · exact EqLA_right y c h2
  have := EqLA_mid y hy (c + 37).toNat (by omega)
  have e : (((c + 37).toNat : Nat) : Int) - 37 = c := by omega
  rwa [e] at this

theorem pw_bounds (z : Nat) (hz : z < 7) : 1 ≤ pw z ∧ pw z ≤ 26 := by
  revert z; decide +kernel

theorem Lrow_LA (r : Nat) (e : Int) (h : e < 1) : Lrow r e = fLA r e := by
  unfold Lrow fLA
  have hb := pw_bounds (r % 7) (by omega)
  by_cases h1 : e < p1L r
  · rw [if_pos h1, LA_neg _ (by omega)]
    exact alpha_congr _ _ (by unfold p1L; omega)
  · rw [if_neg h1, if_pos (by omega), LA_pos _ (by omega)]
    exact beta_congr _ _ (by unfold p1L; omega)

theorem EqF_fLA (r : Nat) (hr : 6 ≤ r) (e : Int) : EqF fLA r e = EqLA (r % 6) (e - p1L r) := by
  unfold EqF EqLA Eq9 fLA
  have v1 : LA (e + 1 - p1L (r - 1)) = LA (e - p1L r + 6 - dl (r % 6) 1) := by
    congr 1; unfold p1L dl; split <;> omega
  have v2 : LA (e + 2 - p1L (r - 2)) = LA (e - p1L r + 12 - dl (r % 6) 2) := by
    congr 1; unfold p1L dl; split <;> omega
  have v5 : LA (e + 5 - p1L (r - 5)) = LA (e - p1L r + 30 - dl (r % 6) 5) := by
    congr 1; unfold p1L dl; split <;> omega
  have v6 : LA (e + 6 - p1L (r - 6)) = LA (e - p1L r + 36 - dl (r % 6) 6) := by
    congr 1; unfold p1L dl; split <;> omega
  have w1 : LA (e - 1 - p1L r) = LA (e - p1L r - 1) := by congr 1; omega
  have w2 : LA (e - 2 - p1L r) = LA (e - p1L r - 2) := by congr 1; omega
  have w5 : LA (e - 5 - p1L r) = LA (e - p1L r - 5) := by congr 1; omega
  have w6 : LA (e - 6 - p1L r) = LA (e - p1L r - 6) := by congr 1; omega
  have m : (e - p1L r + 1) % 5 = e % 5 := by unfold p1L; omega
  rw [v1, v2, v5, v6, w1, w2, w5, w6, m]

/-- Zone I of the L phase: left of the wall, the table is alpha | beta with the moving seam. -/
theorem A_left (r : Nat) (hr : 6 ≤ r) (e : Int) (h : e ≤ -6) : EqF Lrow r e = true := by
  have hs : ∀ s : Nat, s ∈ [0, 1, 2, 5, 6] → s ≤ 6 := by
    intro s hs; simp at hs; omega
  rw [EqF_congr Lrow fLA r e (fun s h' => Lrow_LA _ _ (by have := hs s h'; omega))
    (fun s h' => Lrow_LA _ _ (by have := hs s h'; omega))]
  rw [EqF_fLA r hr e]
  exact EqLA_all _ (by omega) _

theorem Lrow_tail (r : Nat) (e : Int) (h : 26 ≤ e) : Lrow r e = ft r e := by
  unfold Lrow ft
  have hb := pw_bounds (r % 7) (by omega)
  have : p1L r ≤ 16 := by unfold p1L; omega
  rw [if_neg (by omega), if_neg (by omega)]

theorem A_tail (r : Nat) (hr : 6 ≤ r) (e : Int) (h : 32 ≤ e) : EqF Lrow r e = true := by
  have hs : ∀ s : Nat, s ∈ [0, 1, 2, 5, 6] → s ≤ 6 := by
    intro s hs; simp at hs; omega
  rw [EqF_congr Lrow ft r e (fun s h' => Lrow_tail _ _ (by have := hs s h'; omega))
    (fun s h' => Lrow_tail _ _ (by have := hs s h'; omega))]
  exact ft_ok r hr e

def Wall (z : Nat) (e : Int) : Bool := if e < pw z then beta (e - 5 * (z : Int)) else tl z e
def wf (r : Nat) (e : Int) : Bool := Wall (r % 7) e

theorem Lrow_wall (r : Nat) (e : Int) (h : p1L r ≤ e) : Lrow r e = wf r e := by
  unfold Lrow wf Wall
  rw [if_neg (by omega)]
  by_cases h2 : e < pw (r % 7)
  · rw [if_pos h2, if_pos h2]; exact beta_congr _ _ (by omega)
  · rw [if_neg h2, if_neg h2]

theorem wf_row7 : ∀ r r' e, r % 7 = r' % 7 → wf r e = wf r' e := by
  intro r r' e h; unfold wf; rw [h]

theorem wf_mid : ∀ z : Nat, z < 7 → ∀ i : Nat, i < 37 → EqF wf (z + 7) ((i : Int) - 5) = true := by
  decide +kernel

theorem wf_ok (r : Nat) (hr : 6 ≤ r) (e : Int) (h1 : -5 ≤ e) (h2 : e ≤ 31) :
    EqF wf r e = true := by
  rw [EqF_row7 wf wf_row7 r hr e]
  have := wf_mid (r % 7) (by omega) (e + 5).toNat (by omega)
  have e' : (((e + 5).toNat : Nat) : Int) - 5 = e := by omega
  rwa [e'] at this

theorem A_win : ∀ r : Nat, r < 36 → ∀ i : Nat, i < 37 →
    EqF Lrow (r + 6) ((i : Int) - 5) = true := by
  decide +kernel

theorem A_ok (r : Nat) (hr : 6 ≤ r) (e : Int) : EqF Lrow r e = true := by
  by_cases h1 : e ≤ -6
  · exact A_left r hr e h1
  by_cases h2 : 32 ≤ e
  · exact A_tail r hr e h2
  by_cases h3 : r < 42
  · have := A_win (r - 6) (by omega) (e + 5).toNat (by omega)
    have e' : (((e + 5).toNat : Nat) : Int) - 5 = e := by omega
    rwa [e', show r - 6 + 6 = r by omega] at this
  · have hs : ∀ s : Nat, s ∈ [0, 1, 2, 5, 6] → s ≤ 6 := by
      intro s hs; simp at hs; omega
    rw [EqF_congr Lrow wf r e
      (fun s h' => Lrow_wall _ _ (by have := hs s h'; unfold p1L; omega))
      (fun s h' => Lrow_wall _ _ (by have := hs s h'; unfold p1L; omega))]
    exact wf_ok r hr e (by omega) (by omega)

/-! ### The R phase: s = rows to go until the next jump (rows are listed backwards in time). -/

def EqR (f : Nat → Int → Bool) (s : Nat) (e : Int) : Bool :=
  f s e == (e % 5 != 0 && !f (s+1) (e+1) && !f s (e-1) && !f (s+2) (e+2) && !f s (e-2)
    && !f (s+5) (e+5) && !f s (e-5) && !f (s+6) (e+6) && !f s (e-6))

theorem EqR_congr (f g : Nat → Int → Bool) (s : Nat) (e : Int)
    (hf : ∀ t : Nat, t ∈ [0, 1, 2, 5, 6] → f (s + t) (e + t) = g (s + t) (e + t))
    (hg : ∀ t : Nat, t ∈ [0, 1, 2, 5, 6] → f s (e - t) = g s (e - t)) :
    EqR f s e = EqR g s e := by
  have h0 : f s e = g s e := by simpa using hf 0 (by simp)
  have a1 : f (s+1) (e+1) = g (s+1) (e+1) := by simpa using hf 1 (by simp)
  have a2 : f (s+2) (e+2) = g (s+2) (e+2) := by simpa using hf 2 (by simp)
  have a5 : f (s+5) (e+5) = g (s+5) (e+5) := by simpa using hf 5 (by simp)
  have a6 : f (s+6) (e+6) = g (s+6) (e+6) := by simpa using hf 6 (by simp)
  have b1 : f s (e-1) = g s (e-1) := by simpa using hg 1 (by simp)
  have b2 : f s (e-2) = g s (e-2) := by simpa using hg 2 (by simp)
  have b5 : f s (e-5) = g s (e-5) := by simpa using hg 5 (by simp)
  have b6 : f s (e-6) = g s (e-6) := by simpa using hg 6 (by simp)
  unfold EqR
  rw [h0, a1, a2, a5, a6, b1, b2, b5, b6]

/-- an R-phase table that agrees with a forward table g at the cells the equation reads -/
theorem EqR_mirror (f g : Nat → Int → Bool) (s N : Nat) (e : Int) (hN : s + 6 ≤ N)
    (hf : ∀ t : Nat, t ∈ [0, 1, 2, 5, 6] → f (s + t) (e + t) = g (N - s - t) (e + t))
    (hg : ∀ t : Nat, t ∈ [0, 1, 2, 5, 6] → f s (e - t) = g (N - s) (e - t)) :
    EqR f s e = EqF g (N - s) e := by
  have h0 : f s e = g (N - s) e := by simpa using hf 0 (by simp)
  have a1 : f (s+1) (e+1) = g (N - s - 1) (e+1) := by simpa using hf 1 (by simp)
  have a2 : f (s+2) (e+2) = g (N - s - 2) (e+2) := by simpa using hf 2 (by simp)
  have a5 : f (s+5) (e+5) = g (N - s - 5) (e+5) := by simpa using hf 5 (by simp)
  have a6 : f (s+6) (e+6) = g (N - s - 6) (e+6) := by simpa using hf 6 (by simp)
  have b1 : f s (e-1) = g (N - s) (e-1) := by simpa using hg 1 (by simp)
  have b2 : f s (e-2) = g (N - s) (e-2) := by simpa using hg 2 (by simp)
  have b5 : f s (e-5) = g (N - s) (e-5) := by simpa using hg 5 (by simp)
  have b6 : f s (e-6) = g (N - s) (e-6) := by simpa using hg 6 (by simp)
  unfold EqR EqF
  rw [h0, a1, a2, a5, a6, b1, b2, b5, b6]

/-- the gamma | glider word | beta picture of the R phase in the coordinate c = e - p1R s -/
def RA (c : Int) : Bool :=
  if c < 0 then gamma (c + 6) else if c < 14 then gword c.toNat else beta (c + 6)
def fRA (s : Nat) (e : Int) : Bool := RA (e - p1R s)

theorem RA_neg (x : Int) (h : x < 0) : RA x = gamma (x + 6) := by unfold RA; simp [h]
theorem RA_pos (x : Int) (h : 14 ≤ x) : RA x = beta (x + 6) := by
  unfold RA; simp [Int.not_lt.2 (by omega : 0 ≤ x), Int.not_lt.2 h]

def EqRA (c : Int) : Bool :=
  Eq9 (RA c) (RA (c + 6)) (RA (c - 1)) (RA (c + 12)) (RA (c - 2)) (RA (c + 30)) (RA (c - 5))
    (RA (c + 36)) (RA (c - 6)) (c + 1)

theorem gamma_eq1 (u : Int) : Eq1 gamma u = true := by
  have := alpha_eq1 (u - 10)
  unfold Eq1 Eq9 at this ⊢
  unfold gamma
  rw [show u + 6 - 10 = u - 10 + 6 by omega, show u - 1 - 10 = u - 10 - 1 by omega,
    show u + 12 - 10 = u - 10 + 12 by omega, show u - 2 - 10 = u - 10 - 2 by omega,
    show u + 30 - 10 = u - 10 + 30 by omega, show u - 5 - 10 = u - 10 - 5 by omega,
    show u + 36 - 10 = u - 10 + 36 by omega, show u - 6 - 10 = u - 10 - 6 by omega,
    show u % 5 = (u - 10) % 5 by omega]
  exact this

theorem EqRA_left (c : Int) (h : c ≤ -37) : EqRA c = true := by
  have := gamma_eq1 (c + 6)
  unfold EqRA Eq9
  unfold Eq1 Eq9 at this
  rw [RA_neg c (by omega), RA_neg (c + 6) (by omega), RA_neg (c - 1) (by omega),
    RA_neg (c + 12) (by omega), RA_neg (c - 2) (by omega), RA_neg (c + 30) (by omega),
    RA_neg (c - 5) (by omega), RA_neg (c + 36) (by omega), RA_neg (c - 6) (by omega),
    show (c + 1) % 5 = (c + 6) % 5 by omega]
  rw [show c - 1 + 6 = c + 6 - 1 by omega, show c + 12 + 6 = c + 6 + 12 by omega,
    show c - 2 + 6 = c + 6 - 2 by omega, show c + 30 + 6 = c + 6 + 30 by omega,
    show c - 5 + 6 = c + 6 - 5 by omega, show c + 36 + 6 = c + 6 + 36 by omega, show c - 6 + 6 = c + 6 - 6 by omega]
  exact this

theorem EqRA_right (c : Int) (h : 20 ≤ c) : EqRA c = true := by
  have := beta_eq1 (c + 6)
  unfold EqRA Eq9
  unfold Eq1 Eq9 at this
  rw [RA_pos c (by omega), RA_pos (c + 6) (by omega), RA_pos (c - 1) (by omega),
    RA_pos (c + 12) (by omega), RA_pos (c - 2) (by omega), RA_pos (c + 30) (by omega),
    RA_pos (c - 5) (by omega), RA_pos (c + 36) (by omega), RA_pos (c - 6) (by omega),
    show (c + 1) % 5 = (c + 6) % 5 by omega]
  rw [show c - 1 + 6 = c + 6 - 1 by omega, show c + 12 + 6 = c + 6 + 12 by omega,
    show c - 2 + 6 = c + 6 - 2 by omega, show c + 30 + 6 = c + 6 + 30 by omega,
    show c - 5 + 6 = c + 6 - 5 by omega, show c + 36 + 6 = c + 6 + 36 by omega, show c - 6 + 6 = c + 6 - 6 by omega]
  exact this

theorem EqRA_mid : ∀ i : Nat, i < 57 → EqRA ((i : Int) - 37) = true := by
  decide +kernel

theorem EqRA_all (c : Int) : EqRA c = true := by
  by_cases h1 : c ≤ -37
  · exact EqRA_left c h1
  by_cases h2 : 20 ≤ c
  · exact EqRA_right c h2
  have := EqRA_mid (c + 37).toNat (by omega)
  have e : (((c + 37).toNat : Nat) : Int) - 37 = c := by omega
  rwa [e] at this

end SqrtM
