module

public import ArtGallery.Orthogonal.Hard.Cert

/-!
# Coverage certificates: convex items and cut trees

The completeness of the orthogonal construction (every point of the region is seen by a canonical
guard) is certified per template group (computed during development).  An *item* is a
convex set `C` given by oriented lines through frame points (`linesSet`: the intersection of the
half-planes `0 ≤ det(u, v, z)`); it contains the position range of one guard and lies in the
region, so that guard sees all of `C`.  A rectangle of the region is cut into *leaves* by a tree of
vertical and horizontal cuts, a leaf being a rectangle or a rectangle cut once by a line; every
leaf lies in an item.

This file: the leaf test (`leafB`, `leafB_sound`) and the tree test (`treeB`, `treeB_sound`).  A
leaf cut by a non-vertical line `c` is the trapezoid between the chord of `c` (from the left to
the right side of the rectangle) and the top or bottom side; an affine function nonnegative at its
four corners is nonnegative on it (`trap_nonneg`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade Set

/-! ### Affine functions on intervals and trapezoids -/

theorem affine_interval_nonneg {p q a b x : ℝ} (ha : 0 ≤ p * a + q) (hb : 0 ≤ p * b + q)
    (h1 : a ≤ x) (h2 : x ≤ b) : 0 ≤ p * x + q := by
  rcases le_total 0 p with hp | hp
  · nlinarith [mul_le_mul_of_nonneg_left h1 hp]
  · nlinarith [mul_le_mul_of_nonpos_left h2 hp]

/-- **Trapezoid above a chord.**  For `c(x, y) = α x + γ y + δ` with `γ > 0`, the region
`{X₀ ≤ x ≤ X₁, c ≥ 0, y ≤ y₁}` lies above the line `c = 0`; an affine function nonnegative at the
two points of the line over `X₀`, `X₁` and at `(X₀, y₁)`, `(X₁, y₁)` is nonnegative there. -/
theorem trap_nonneg {A B G α γ δ X0 X1 y1 zx zy : ℝ} (hγ : 0 < γ)
    (hx0 : X0 ≤ zx) (hx1 : zx ≤ X1) (hzy : zy ≤ y1) (hc : 0 ≤ α * zx + γ * zy + δ)
    (hP0 : 0 ≤ A * X0 + B * (-(α * X0 + δ) / γ) + G)
    (hP1 : 0 ≤ A * X1 + B * (-(α * X1 + δ) / γ) + G)
    (hT0 : 0 ≤ A * X0 + B * y1 + G) (hT1 : 0 ≤ A * X1 + B * y1 + G) :
    0 ≤ A * zx + B * zy + G := by
  have hne : γ ≠ 0 := hγ.ne'
  set ℓ := -(α * zx + δ) / γ with hℓ
  have hzℓ : ℓ ≤ zy := by
    rw [hℓ, div_le_iff₀ hγ]; linarith
  -- the value on the chord over zx
  have g1 : 0 ≤ A * zx + B * ℓ + G := by
    have e : ∀ x, A * x + B * (-(α * x + δ) / γ) + G = (A - B * α / γ) * x + (G - B * δ / γ) := by
      intro x; field_simp; ring
    have := affine_interval_nonneg (p := A - B * α / γ) (q := G - B * δ / γ)
      (by rw [← e]; exact hP0) (by rw [← e]; exact hP1) hx0 hx1
    rw [hℓ, e]; exact this
  have g2 : 0 ≤ A * zx + B * y1 + G := by
    have := affine_interval_nonneg (p := A) (q := B * y1 + G) (by linarith) (by linarith) hx0 hx1
    linarith
  have := affine_interval_nonneg (p := B) (q := A * zx + G) (by linarith) (by linarith) hzℓ hzy
  linarith

/-- **Trapezoid below a chord** (`γ < 0`). -/
theorem trap_nonneg' {A B G α γ δ X0 X1 y0 zx zy : ℝ} (hγ : γ < 0)
    (hx0 : X0 ≤ zx) (hx1 : zx ≤ X1) (hzy : y0 ≤ zy) (hc : 0 ≤ α * zx + γ * zy + δ)
    (hP0 : 0 ≤ A * X0 + B * (-(α * X0 + δ) / γ) + G)
    (hP1 : 0 ≤ A * X1 + B * (-(α * X1 + δ) / γ) + G)
    (hT0 : 0 ≤ A * X0 + B * y0 + G) (hT1 : 0 ≤ A * X1 + B * y0 + G) :
    0 ≤ A * zx + B * zy + G := by
  have := trap_nonneg (A := A) (B := -B) (G := G) (α := α) (γ := -γ) (δ := δ) (X0 := X0) (X1 := X1)
    (y1 := -y0) (zx := zx) (zy := -zy) (by linarith) hx0 hx1 (by linarith) (by linarith)
    (by rw [div_neg]; linarith) (by rw [div_neg]; linarith)
    (by linarith) (by linarith)
  linarith

/-! ### Lines, items -/

/-- An oriented line through two frame points; its half-plane is `0 ≤ det(u, v, z)`. -/
abbrev LLine := LP × LP

/-- The real half-plane of an oriented line. -/
def LLine.set (ox H : ℝ) (l : LLine) : Set Point := {z | 0 ≤ det (l.1.real ox H) (l.2.real ox H) z}

/-- The intersection of the half-planes of a list of lines. -/
def linesSet (ox H : ℝ) (ls : List LLine) : Set Point := {z | ∀ l ∈ ls, z ∈ l.set ox H}

theorem convex_lineSet (ox H : ℝ) (l : LLine) : Convex ℝ (l.set ox H) := by
  intro x hx y hy a b ha hb hab
  simp only [LLine.set, mem_ofPred_eq, det_affine] at hx hy ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have e : b = 1 - a := by linarith
  subst e
  nlinarith [mul_nonneg ha hx, mul_nonneg hb hy]

theorem convex_linesSet (ox H : ℝ) (ls : List LLine) : Convex ℝ (linesSet ox H ls) := by
  have : linesSet ox H ls = ⋂ l ∈ ls, l.set ox H := by
    ext z; simp [linesSet]
  rw [this]
  exact convex_iInter₂ fun l _ => convex_lineSet ox H l

theorem isClosed_lineSet (ox H : ℝ) (l : LLine) : IsClosed (l.set ox H) := by
  have : l.set ox H = (fun z : Point => det (l.1.real ox H) (l.2.real ox H) z) ⁻¹' Ici 0 := rfl
  rw [this]
  exact isClosed_Ici.preimage (by simp only [det]; fun_prop)

theorem isClosed_linesSet (ox H : ℝ) (ls : List LLine) : IsClosed (linesSet ox H ls) := by
  have : linesSet ox H ls = ⋂ l ∈ ls, l.set ox H := by
    ext z; simp [linesSet]
  rw [this]
  exact isClosed_biInter fun l _ => isClosed_lineSet ox H l

/-- The frame point `p` lies in every half-plane (for all `H ≥ 1000`). -/
def inLinesB (ls : List LLine) (p : LP) : Bool := ls.all fun l => (hpv l.1 l.2 p).nn

theorem inLinesB_sound {ls : List LLine} {p : LP} (h : inLinesB ls p = true) {H : ℝ}
    (hH : 1000 ≤ H) (ox : ℝ) : p.real ox H ∈ linesSet ox H ls := by
  intro l hl
  have := List.all_eq_true.1 h l hl
  simp only [LLine.set, mem_ofPred_eq]
  rw [hpv_ev]; exact AH.nn_sound this hH

/-! ### Leaves -/

/-- The ordinate of the line `c` at the abscissa `x` (`c` not vertical). -/
def chordY (c : LLine) (x : ℚ) : AH :=
  let t := (x - c.1.1) / (c.2.1 - c.1.1)
  (c.1.2.1 + t * (c.2.2.1 - c.1.2.1), c.1.2.2 + t * (c.2.2.2 - c.1.2.2))

/-- The test points of a leaf: the corners of the rectangle, or for a leaf cut by a non-vertical
line, the chord (meeting both vertical sides within the rectangle) and the two corners on the kept
side; `none` if the cut is vertical or leaves through a horizontal side. -/
def leafPts (r : LR) : Option LLine → Option (List LP)
  | none => some r.corners
  | some c =>
    if c.2.1 - c.1.1 = 0 then none
    else if AH.le r.y0 (chordY c r.x0) && AH.le (chordY c r.x0) r.y1 &&
        AH.le r.y0 (chordY c r.x1) && AH.le (chordY c r.x1) r.y1 then
      some ([(r.x0, chordY c r.x0), (r.x1, chordY c r.x1)] ++
        if 0 < c.2.1 - c.1.1 then [(r.x0, r.y1), (r.x1, r.y1)] else [(r.x0, r.y0), (r.x1, r.y0)])
    else none

/-- **Leaf test**: the leaf lies in the item of lines `ls`. -/
def leafB (ls : List LLine) (r : LR) (cut : Option LLine) : Bool :=
  match leafPts r cut with
  | none => false
  | some ps => ps.all (inLinesB ls)

theorem chordY_ev (c : LLine) (x : ℚ) (H : ℝ) (hc : c.2.1 - c.1.1 ≠ 0) :
    (chordY c x).ev H = c.1.2.ev H + ((x - c.1.1 : ℚ) : ℝ) / ((c.2.1 - c.1.1 : ℚ) : ℝ) *
      (c.2.2.ev H - c.1.2.ev H) := by
  have hc' : ((c.2.1 - c.1.1 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hc
  simp only [chordY, AH.ev]; push_cast; field_simp; ring

/-- The affine form of the half-plane function of a line. -/
theorem det_lp_affine (ox H : ℝ) (u v : LP) (z : Point) :
    det (u.real ox H) (v.real ox H) z =
      (-(v.2.ev H - u.2.ev H)) * z.1 + ((v.1 - u.1 : ℚ) : ℝ) * z.2 +
        ((v.2.ev H - u.2.ev H) * (ox + u.1) - ((v.1 - u.1 : ℚ) : ℝ) * u.2.ev H) := by
  rw [det_affine]; simp only [LP.real]; push_cast; ring

theorem leafB_pts {ls : List LLine} {r : LR} {cut : Option LLine} (h : leafB ls r cut = true) :
    ∃ ps, leafPts r cut = some ps ∧ ∀ p ∈ ps, inLinesB ls p = true := by
  unfold leafB at h
  cases hp : leafPts r cut with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some ps => rw [hp] at h; exact ⟨ps, rfl, List.all_eq_true.1 h⟩

theorem leafB_sound {ls : List LLine} {r : LR} {cut : Option LLine} (h : leafB ls r cut = true)
    {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ) {z : Point} (hz : z ∈ (r.real ox H).set)
    (hc : ∀ c, cut = some c → z ∈ c.set ox H) : z ∈ linesSet ox H ls := by
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  simp only [LR.real] at hz1 hz2 hz3 hz4
  obtain ⟨ps, hps, hall⟩ := leafB_pts h
  intro l hl
  have f : ∀ p ∈ ps, 0 ≤ det (l.1.real ox H) (l.2.real ox H) (p.real ox H) :=
    fun p hp => inLinesB_sound (hall p hp) hH ox l hl
  simp only [LLine.set, mem_ofPred_eq]
  rw [det_lp_affine]
  cases cut with
  | none =>
    simp only [leafPts, Option.some.injEq] at hps
    subst hps
    simp only [LR.corners, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at f
    obtain ⟨e00, e10, e01, e11⟩ := f
    rw [det_lp_affine] at e00 e10 e01 e11
    simp only [LP.real] at e00 e10 e01 e11
    exact affine_nonneg_rect (by linarith) (by linarith) (by linarith) (by linarith) hz1 hz2 hz3 hz4
  | some c =>
    have hcz := hc c rfl
    simp only [LLine.set, mem_ofPred_eq] at hcz
    rw [det_lp_affine] at hcz
    simp only [leafPts] at hps
    by_cases hd : c.2.1 - c.1.1 = 0
    · simp [hd] at hps
    simp only [hd, ↓reduceIte] at hps
    split_ifs at hps with hy hg
    · simp only [Option.some.injEq] at hps
      subst hps
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at f
      obtain ⟨e0, e1, eT0, eT1⟩ := f
      rw [det_lp_affine] at e0 e1 eT0 eT1
      simp only [LP.real] at e0 e1 eT0 eT1
      rw [chordY_ev c _ H hd] at e0 e1
      have hγ : (0 : ℝ) < ((c.2.1 - c.1.1 : ℚ) : ℝ) := by exact_mod_cast hg
      refine trap_nonneg (γ := ((c.2.1 - c.1.1 : ℚ) : ℝ)) (α := -(c.2.2.ev H - c.1.2.ev H))
        (δ := (c.2.2.ev H - c.1.2.ev H) * (ox + c.1.1) - ((c.2.1 - c.1.1 : ℚ) : ℝ) * c.1.2.ev H)
        (X0 := ox + r.x0) (X1 := ox + r.x1) (y1 := r.y1.ev H) hγ hz1 hz2 hz4 hcz ?_ ?_ eT0 eT1
      · convert e0 using 3
        have hne := hγ.ne'
        field_simp; push_cast; ring
      · convert e1 using 3
        have hne := hγ.ne'
        field_simp; push_cast; ring
    · simp only [Option.some.injEq] at hps
      subst hps
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at f
      obtain ⟨e0, e1, eT0, eT1⟩ := f
      rw [det_lp_affine] at e0 e1 eT0 eT1
      simp only [LP.real] at e0 e1 eT0 eT1
      rw [chordY_ev c _ H hd] at e0 e1
      have hγ : ((c.2.1 - c.1.1 : ℚ) : ℝ) < 0 := by
        have : c.2.1 - c.1.1 < 0 := lt_of_le_of_ne (not_lt.1 hg) hd
        exact_mod_cast this
      refine trap_nonneg' (γ := ((c.2.1 - c.1.1 : ℚ) : ℝ)) (α := -(c.2.2.ev H - c.1.2.ev H))
        (δ := (c.2.2.ev H - c.1.2.ev H) * (ox + c.1.1) - ((c.2.1 - c.1.1 : ℚ) : ℝ) * c.1.2.ev H)
        (X0 := ox + r.x0) (X1 := ox + r.x1) (y0 := r.y0.ev H) hγ hz1 hz2 hz3 hcz ?_ ?_ eT0 eT1
      · convert e0 using 3
        have hne := hγ.ne
        field_simp; push_cast; ring
      · convert e1 using 3
        have hne := hγ.ne
        field_simp; push_cast; ring

/-! ### Trees -/

/-- A cut tree of a rectangle: vertical and horizontal cuts, and leaves (an item index), possibly
after a cut by a line (left side: the half-plane of the line, right side: the opposite one). -/
inductive CTree where
  | leaf (k : ℕ)
  | lin (c : LLine) (a b : ℕ)
  | xcut (x : ℚ) (l r : CTree)
  | ycut (y : AH) (l r : CTree)

/-- **Tree test.** -/
def treeB (items : List (List LLine)) : LR → CTree → Bool
  | r, .leaf k => decide (k < items.length) && leafB (items.getD k []) r none
  | r, .lin c a b => decide (a < items.length) && decide (b < items.length) &&
      leafB (items.getD a []) r (some c) && leafB (items.getD b []) r (some (c.2, c.1))
  | r, .xcut x t1 t2 => decide (r.x0 < x) && decide (x < r.x1) &&
      treeB items ⟨r.x0, x, r.y0, r.y1⟩ t1 && treeB items ⟨x, r.x1, r.y0, r.y1⟩ t2
  | r, .ycut y t1 t2 => AH.lt r.y0 y && AH.lt y r.y1 &&
      treeB items ⟨r.x0, r.x1, r.y0, y⟩ t1 && treeB items ⟨r.x0, r.x1, y, r.y1⟩ t2

/-- The two sides of an oriented line cover the plane. -/
theorem lineSet_or (ox H : ℝ) (c : LLine) (z : Point) :
    z ∈ c.set ox H ∨ z ∈ LLine.set ox H (c.2, c.1) := by
  simp only [LLine.set, mem_ofPred_eq]
  rcases le_total 0 (det (c.1.real ox H) (c.2.real ox H) z) with h | h
  · exact Or.inl h
  · right
    have : det (c.2.real ox H) (c.1.real ox H) z = -det (c.1.real ox H) (c.2.real ox H) z := by
      simp only [det]; ring
    linarith

theorem treeB_sound {items : List (List LLine)} {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ) :
    ∀ (t : CTree) (r : LR), treeB items r t = true → ∀ z ∈ (r.real ox H).set,
      ∃ k < items.length, z ∈ linesSet ox H (items.getD k [])
  | .leaf k, r, h, z, hz => by
    simp only [treeB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨k, h.1, leafB_sound h.2 hH ox hz (fun c hc => by cases hc)⟩
  | .lin c a b, r, h, z, hz => by
    simp only [treeB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨ha, hb⟩, h1⟩, h2⟩ := h
    rcases lineSet_or ox H c z with hc | hc
    · exact ⟨a, ha, leafB_sound h1 hH ox hz (fun c' e => by cases e; exact hc)⟩
    · exact ⟨b, hb, leafB_sound h2 hH ox hz (fun c' e => by cases e; exact hc)⟩
  | .xcut x t1 t2, r, h, z, hz => by
    simp only [treeB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨-, -⟩, h1⟩, h2⟩ := h
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    simp only [LR.real] at hz1 hz2 hz3 hz4
    rcases le_total z.1 (ox + x) with hx | hx
    · exact treeB_sound hH ox t1 _ h1 z ⟨hz1, hx, hz3, hz4⟩
    · exact treeB_sound hH ox t2 _ h2 z ⟨hx, hz2, hz3, hz4⟩
  | .ycut y t1 t2, r, h, z, hz => by
    simp only [treeB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨-, -⟩, h1⟩, h2⟩ := h
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    simp only [LR.real] at hz1 hz2 hz3 hz4
    rcases le_total z.2 (y.ev H) with hy | hy
    · exact treeB_sound hH ox t1 _ h1 z ⟨hz1, hz2, hz3, hy⟩
    · exact treeB_sound hH ox t2 _ h2 z ⟨hz1, hz2, hy, hz4⟩


/-! ### Items: containment in the region -/

/-- An item: oriented lines, a bounding box and a point strictly inside. -/
structure CItem where
  lines : List LLine
  box : LR
  inner : LP

/-- The convex set of an item. -/
def CItem.set (ox H : ℝ) (it : CItem) : Set Point := linesSet ox H it.lines ∩ (it.box.real ox H).set

/-- The strict part of an item: strictly inside every line and the open box. -/
def CItem.strict (ox H : ℝ) (it : CItem) : Set Point :=
  {z | (∀ l ∈ it.lines, 0 < det (l.1.real ox H) (l.2.real ox H) z) ∧
    ox + it.box.x0 < z.1 ∧ z.1 < ox + it.box.x1 ∧ it.box.y0.ev H < z.2 ∧ z.2 < it.box.y1.ev H}

theorem rect_set_convex (r : Rect) : Convex ℝ r.set := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  simp only [Rect.set, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  have e : b = 1 - a := by linarith
  subst e
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_le_mul_of_nonneg_left x1 ha, mul_le_mul_of_nonneg_left y1 hb,
    mul_le_mul_of_nonneg_left x2 ha, mul_le_mul_of_nonneg_left y2 hb,
    mul_le_mul_of_nonneg_left x3 ha, mul_le_mul_of_nonneg_left y3 hb,
    mul_le_mul_of_nonneg_left x4 ha, mul_le_mul_of_nonneg_left y4 hb]

theorem CItem.convex (ox H : ℝ) (it : CItem) : Convex ℝ (it.set ox H) :=
  (convex_linesSet ox H it.lines).inter (rect_set_convex _)

/-- The inner point is strictly inside (for all `H ≥ 1000`). -/
def CItem.innerB (it : CItem) : Bool :=
  it.lines.all (fun l => (hpv l.1 l.2 it.inner).pos) && decide (it.box.x0 < it.inner.1) &&
    decide (it.inner.1 < it.box.x1) && AH.lt it.box.y0 it.inner.2 && AH.lt it.inner.2 it.box.y1

theorem CItem.innerB_sound {it : CItem} (h : it.innerB = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ) :
    it.inner.real ox H ∈ it.strict ox H := by
  simp only [CItem.innerB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun l hl => ?_, ?_, ?_, AH.lt_sound h4 hH, AH.lt_sound h5 hH⟩
  · rw [hpv_ev]; exact AH.pos_sound (h1 l hl) hH
  · simp only [LP.real]; have : (it.box.x0 : ℝ) < it.inner.1 := by exact_mod_cast h2
    linarith
  · simp only [LP.real]; have : (it.inner.1 : ℝ) < it.box.x1 := by exact_mod_cast h3
    linarith

/-- Moving a point of the item towards a strict point gives strict points. -/
theorem CItem.strict_of_set {it : CItem} {ox H : ℝ} {z p : Point} (hz : z ∈ it.set ox H)
    (hp : p ∈ it.strict ox H) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    z + t • (p - z) ∈ it.strict ox H := by
  obtain ⟨hzl, hz1, hz2, hz3, hz4⟩ := hz
  simp only [LR.real] at hz1 hz2 hz3 hz4
  obtain ⟨hpl, hp1, hp2, hp3, hp4⟩ := hp
  have e1 : (z + t • (p - z)).1 = (1 - t) * z.1 + t * p.1 := by
    simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; ring
  have e2 : (z + t • (p - z)).2 = (1 - t) * z.2 + t * p.2 := by
    simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; ring
  have h1t : 0 ≤ 1 - t := by linarith
  refine ⟨fun l hl => ?_, ?_, ?_, ?_, ?_⟩
  · have a := hzl l hl
    have b := hpl l hl
    simp only [LLine.set, mem_ofPred_eq] at a
    rw [det_affine] at a b ⊢
    rw [e1, e2]
    nlinarith [mul_nonneg h1t a, mul_pos ht0 b]
  · rw [e1]; nlinarith [mul_le_mul_of_nonneg_left hz1 h1t]
  · rw [e1]; nlinarith [mul_le_mul_of_nonneg_left hz2 h1t]
  · rw [e2]; nlinarith [mul_le_mul_of_nonneg_left hz3 h1t]
  · rw [e2]; nlinarith [mul_le_mul_of_nonneg_left hz4 h1t]

/-- **Closure argument**: an item whose strict part lies in a closed set `K` lies in `K`. -/
theorem CItem.set_subset_of_strict {it : CItem} {ox H : ℝ} {p : Point} (hp : p ∈ it.strict ox H)
    {K : Set Point} (hK : IsClosed K) (hsK : it.strict ox H ⊆ K) : it.set ox H ⊆ K := by
  intro z hz
  have ht : Filter.Tendsto (fun n : ℕ => z + (1 / ((n : ℝ) + 1)) • (p - z)) Filter.atTop
      (nhds (z + (0 : ℝ) • (p - z))) :=
    tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const _)
  rw [zero_smul, add_zero] at ht
  refine hK.mem_of_tendsto ht (Filter.Eventually.of_forall fun n => hsK ?_)
  exact CItem.strict_of_set hz hp (by positivity)
    (by rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])

/-- The item misses the closed rectangle `R`: a line of the item is `≤ 0` at the corners of
`R`, or `R` lies beyond a side of the box (tested first: it decides most pairs cheaply). -/
def CItem.offB (it : CItem) (R : LR) : Bool :=
  decide (it.box.x1 ≤ R.x0) || decide (R.x1 ≤ it.box.x0) || AH.le it.box.y1 R.y0 ||
    AH.le R.y1 it.box.y0 || it.lines.any (fun l => R.corners.all fun c => (hpv l.2 l.1 c).nn)

theorem CItem.offB_sound {it : CItem} {R : LR} (h : it.offB R = true) {H : ℝ} (hH : 1000 ≤ H)
    (ox : ℝ) {z : Point} (hz : z ∈ it.strict ox H) : z ∉ (R.real ox H).set := by
  intro hR
  obtain ⟨hzl, hz1, hz2, hz3, hz4⟩ := hz
  obtain ⟨r1, r2, r3, r4⟩ := hR
  simp only [LR.real] at r1 r2 r3 r4
  simp only [CItem.offB, Bool.or_eq_true, List.any_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  rcases h with ((((h | h) | h) | h) | ⟨l, hl, hc⟩)
  rotate_right
  · have hpos := hzl l hl
    obtain ⟨c00, c10, c01, c11⟩ := corners_mem (P := fun c => (hpv l.2 l.1 c).nn = true) hc
    have f := fun (c : LP) (hc : (hpv l.2 l.1 c).nn = true) => by
      have := AH.nn_sound hc hH
      rw [← hpv_ev ox H] at this
      exact this
    have e00 := f _ c00; have e10 := f _ c10; have e01 := f _ c01; have e11 := f _ c11
    rw [det_lp_affine] at e00 e10 e01 e11
    simp only [LP.real] at e00 e10 e01 e11
    have := affine_nonneg_rect (x := z.1) (y := z.2) e00 e10 e01 e11 r1 r2 r3 r4
    rw [det_lp_affine] at hpos
    have hsw : ∀ w : Point, det (l.2.real ox H) (l.1.real ox H) w =
        -det (l.1.real ox H) (l.2.real ox H) w := fun w => by simp only [det]; ring
    have := hsw z
    rw [det_lp_affine, det_lp_affine] at this
    linarith
  · have : (it.box.x1 : ℝ) ≤ R.x0 := by exact_mod_cast h
    linarith
  · have : (R.x1 : ℝ) ≤ it.box.x0 := by exact_mod_cast h
    linarith
  · have := AH.le_sound h hH; linarith
  · have := AH.le_sound h hH; linarith

/-- **An item lies in the good part of the frame.**  If the frame box `F` is covered by good
closed rectangles and forbidden rectangles, the item's box lies in `F`, and the item misses every
forbidden rectangle, then the item lies in the union of the good rectangles. -/
theorem CItem.subset_good {it : CItem} (hin : it.innerB = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {F : LR} (hF : AH.le F.y0 it.box.y0 && AH.le it.box.y1 F.y1 &&
      decide (F.x0 ≤ it.box.x0) && decide (it.box.x1 ≤ F.x1) = true)
    {good : List Rect} {forb : List LR}
    (hcov : ∀ z ∈ (F.real ox H).set, (∃ R ∈ good, z ∈ R.set) ∨ ∃ R ∈ forb, z ∈ (R.real ox H).set)
    (hoff : forb.all it.offB = true) : it.set ox H ⊆ ⋃₀ {A | ∃ R ∈ good, A = R.set} := by
  have hK : IsClosed (⋃₀ {A | ∃ R ∈ good, A = R.set}) := by
    refine Set.Finite.isClosed_sUnion ?_ ?_
    · refine (good.map Rect.set).finite_toSet.subset ?_
      rintro A ⟨R, hR, rfl⟩; exact List.mem_map.2 ⟨R, hR, rfl⟩
    · rintro A ⟨R, -, rfl⟩; exact isClosed_rect_set R
  refine CItem.set_subset_of_strict (CItem.innerB_sound hin hH ox) hK (fun z hz => ?_)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hF
  obtain ⟨⟨⟨f1, f2⟩, f3⟩, f4⟩ := hF
  have hzF : z ∈ (F.real ox H).set := by
    obtain ⟨-, h1, h2, h3, h4⟩ := hz
    have g1 := AH.le_sound f1 hH; have g2 := AH.le_sound f2 hH
    have g3 : (F.x0 : ℝ) ≤ it.box.x0 := by exact_mod_cast f3
    have g4 : (it.box.x1 : ℝ) ≤ F.x1 := by exact_mod_cast f4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [LR.real] <;> linarith
  rcases hcov z hzF with ⟨R, hR, hzR⟩ | ⟨R, hR, hzR⟩
  · exact ⟨R.set, ⟨R, hR, rfl⟩, hzR⟩
  · exact absurd hzR (CItem.offB_sound (List.all_eq_true.1 hoff R hR) hH ox hz)

end

end ArtGallery.Orthogonal.Hard
