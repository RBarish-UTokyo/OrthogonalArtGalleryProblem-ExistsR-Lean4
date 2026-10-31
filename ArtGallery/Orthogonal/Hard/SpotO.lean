module

public import ArtGallery.Orthogonal.Hard.QuadO

/-!
# Exterior boxes

An open box `E` of a group frame inside a box of the group and avoided by all rectangles of the
group contains no point of the region (`extB_sound`).  If `E` lies along a wall `x = c` (its right
or left side), then no point strictly on the side of `E` sees a point of the wall at a height
strictly inside `E` (`not_sees_of_ext_right`, `not_sees_of_ext_left`): the segment would pass
through `E` just before reaching the wall.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-- A finite open box of a frame. -/
structure FBox where
  x0 : ℚ
  x1 : ℚ
  y0 : AH
  y1 : AH

/-- The real open box. -/
def FBox.set (ox H : ℝ) (E : FBox) : Set Point :=
  {z | ox + E.x0 < z.1 ∧ z.1 < ox + E.x1 ∧ E.y0.ev H < z.2 ∧ z.2 < E.y1.ev H}

/-- The finite box lies in the open box `U` (robustly). -/
def FBox.inB (E : FBox) (U : LBox) : Bool :=
  (U.x0.all fun a => decide (a ≤ E.x0)) && (U.x1.all fun a => decide (E.x1 ≤ a)) &&
  (U.y0.all fun a => AH.le a E.y0) && (U.y1.all fun a => AH.le E.y1 a)

/-- The closed rectangle `r` robustly avoids the open box `E`. -/
def LR.avoidB (r : LR) (E : FBox) : Bool :=
  decide (r.x1 ≤ E.x0) || decide (E.x1 ≤ r.x0) || AH.le r.y1 E.y0 || AH.le E.y1 r.y0

/-- **The exterior check**: `E` lies in a box of the group and every rectangle of the group
avoids it. -/
def extB (gs : List GZ) (E : FBox) : Bool :=
  (gs.map GZ.box).any E.inB && (groupLR gs).all fun rk => rk.1.avoidB E

theorem FBox.inB_sound {E : FBox} {U : LBox} (h : E.inB U = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {z : Point} (hz : z ∈ E.set ox H) : z ∈ U.set ox H := by
  simp only [FBox.inB, Bool.and_eq_true, Option.all_eq_true_iff_get, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨z1, z2, z3, z4⟩ := hz
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have := h1 (by rw [ha]; rfl); simp only [ha, Option.get_some] at this
    have : (a : ℝ) ≤ E.x0 := by exact_mod_cast this
    linarith
  · have := h2 (by rw [ha]; rfl); simp only [ha, Option.get_some] at this
    have : (E.x1 : ℝ) ≤ a := by exact_mod_cast this
    linarith
  · have := h3 (by rw [ha]; rfl); simp only [ha, Option.get_some] at this
    have := AH.le_sound this hH; linarith
  · have := h4 (by rw [ha]; rfl); simp only [ha, Option.get_some] at this
    have := AH.le_sound this hH; linarith

theorem LR.avoidB_sound {r : LR} {E : FBox} (h : r.avoidB E = true) {H : ℝ} (hH : 1000 ≤ H)
    (ox : ℝ) {z : Point} (hz : z ∈ E.set ox H) (hr : z ∈ (r.real ox H).set) : False := by
  obtain ⟨z1, z2, z3, z4⟩ := hz
  obtain ⟨r1, r2, r3, r4⟩ := hr
  simp only [LR.real] at r1 r2 r3 r4
  simp only [LR.avoidB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((h | h) | h) | h
  · have : (r.x1 : ℝ) ≤ E.x0 := by exact_mod_cast h
    linarith
  · have : (E.x1 : ℝ) ≤ r.x0 := by exact_mod_cast h
    linarith
  · have := AH.le_sound h hH; linarith
  · have := AH.le_sound h hH; linarith

variable {n : ℕ} {Φ : List Constraint}

/-- **An exterior box contains no point of the region.** -/
theorem extB_sound {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) {E : FBox}
    (h : extB gs E = true) {z : Point} (hz : z ∈ E.set ox (Hr n Φ))
    (hf : z ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled) : False := by
  have hH := Hr_ge n Φ
  simp only [extB, Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨U, hU, hin⟩, hav⟩ := h
  obtain ⟨Rest, -, hRU, hcov⟩ := group_rest hgs
  rw [filledO] at hf
  rcases hcov z hf with ⟨rk, hrk, hzr⟩ | ⟨r, hr, hzr⟩
  · exact LR.avoidB_sound (hav rk hrk) hH ox hz hzr
  · exact hRU r hr z hzr U hU (FBox.inB_sound hin hH ox hz)

/-- **A wall seen only from its inner side** (exterior box on the left of the wall `x = E.x1`). -/
theorem not_sees_of_ext_right {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox)
    {E : FBox} (h : extB gs E = true) (hE : E.x0 < E.x1) {w z : Point}
    (hw1 : w.1 = (ox : ℝ) + E.x1) (hw2 : E.y0.ev (Hr n Φ) < w.2) (hw3 : w.2 < E.y1.ev (Hr n Φ))
    (hz : z.1 < (ox : ℝ) + E.x1) (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees z w) :
    False := by
  have hE' : (E.x0 : ℝ) < E.x1 := by exact_mod_cast hE
  -- a point of the segment close to `w`
  set d := w.1 - z.1 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set a := min ((E.x1 - E.x0 : ℝ) / (2 * d)) (1 / 2) with ha
  set b := min ((w.2 - E.y0.ev (Hr n Φ)) / (2 * (|z.2 - w.2| + 1)))
    ((E.y1.ev (Hr n Φ) - w.2) / (2 * (|z.2 - w.2| + 1))) with hb
  set s := min a b with hs_def
  have ha0 : 0 < a := lt_min (div_pos (by linarith) (by linarith)) (by norm_num)
  have hb0 : 0 < b := lt_min (div_pos (by linarith) (by positivity))
    (div_pos (by linarith) (by positivity))
  have hs0 : 0 < s := lt_min ha0 hb0
  have hs1 : s ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hsa : s * d ≤ (E.x1 - E.x0 : ℝ) / 2 := by
    have : s ≤ (E.x1 - E.x0 : ℝ) / (2 * d) := (min_le_left _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hab : |z.2 - w.2| ≤ |z.2 - w.2| + 1 := by linarith
  have hsb1 : s * |z.2 - w.2| < w.2 - E.y0.ev (Hr n Φ) := by
    have h1 : s ≤ (w.2 - E.y0.ev (Hr n Φ)) / (2 * (|z.2 - w.2| + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg (z.2 - w.2)]
  have hsb2 : s * |z.2 - w.2| < E.y1.ev (Hr n Φ) - w.2 := by
    have h1 : s ≤ (E.y1.ev (Hr n Φ) - w.2) / (2 * (|z.2 - w.2| + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg (z.2 - w.2)]
  set t := 1 - s
  have hm : lerp z w t ∈ ArtGallery.segment z w := ⟨t, by linarith, by linarith, rfl⟩
  refine extB_sound hgs h (z := lerp z w t) ⟨?_, ?_, ?_, ?_⟩ (hs hm)
  · simp only [lerp, t]; nlinarith
  · simp only [lerp, t]; nlinarith
  · simp only [lerp, t]
    have := neg_abs_le (z.2 - w.2)
    nlinarith [abs_nonneg (z.2 - w.2), mul_le_mul_of_nonneg_left (neg_abs_le (z.2 - w.2)) hs0.le]
  · simp only [lerp, t]
    have := le_abs_self (z.2 - w.2)
    nlinarith [abs_nonneg (z.2 - w.2), mul_le_mul_of_nonneg_left (le_abs_self (z.2 - w.2)) hs0.le]

/-- **A wall seen only from its inner side** (exterior box on the right of the wall `x = E.x0`). -/
theorem not_sees_of_ext_left {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox)
    {E : FBox} (h : extB gs E = true) (hE : E.x0 < E.x1) {w z : Point}
    (hw1 : w.1 = (ox : ℝ) + E.x0) (hw2 : E.y0.ev (Hr n Φ) < w.2) (hw3 : w.2 < E.y1.ev (Hr n Φ))
    (hz : (ox : ℝ) + E.x0 < z.1) (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees z w) :
    False := by
  have hE' : (E.x0 : ℝ) < E.x1 := by exact_mod_cast hE
  set d := z.1 - w.1 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set a := min ((E.x1 - E.x0 : ℝ) / (2 * d)) (1 / 2) with ha
  set b := min ((w.2 - E.y0.ev (Hr n Φ)) / (2 * (|z.2 - w.2| + 1)))
    ((E.y1.ev (Hr n Φ) - w.2) / (2 * (|z.2 - w.2| + 1))) with hb
  set s := min a b with hs_def
  have ha0 : 0 < a := lt_min (div_pos (by linarith) (by linarith)) (by norm_num)
  have hb0 : 0 < b := lt_min (div_pos (by linarith) (by positivity))
    (div_pos (by linarith) (by positivity))
  have hs0 : 0 < s := lt_min ha0 hb0
  have hs1 : s ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hsa : s * d ≤ (E.x1 - E.x0 : ℝ) / 2 := by
    have : s ≤ (E.x1 - E.x0 : ℝ) / (2 * d) := (min_le_left _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hsb1 : s * |z.2 - w.2| < w.2 - E.y0.ev (Hr n Φ) := by
    have h1 : s ≤ (w.2 - E.y0.ev (Hr n Φ)) / (2 * (|z.2 - w.2| + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg (z.2 - w.2)]
  have hsb2 : s * |z.2 - w.2| < E.y1.ev (Hr n Φ) - w.2 := by
    have h1 : s ≤ (E.y1.ev (Hr n Φ) - w.2) / (2 * (|z.2 - w.2| + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg (z.2 - w.2)]
  set t := 1 - s
  have hm : lerp z w t ∈ ArtGallery.segment z w := ⟨t, by linarith, by linarith, rfl⟩
  refine extB_sound hgs h (z := lerp z w t) ⟨?_, ?_, ?_, ?_⟩ (hs hm)
  · simp only [lerp, t]; nlinarith
  · simp only [lerp, t]; nlinarith
  · simp only [lerp, t]
    nlinarith [abs_nonneg (z.2 - w.2), mul_le_mul_of_nonneg_left (neg_abs_le (z.2 - w.2)) hs0.le]
  · simp only [lerp, t]
    nlinarith [abs_nonneg (z.2 - w.2), mul_le_mul_of_nonneg_left (le_abs_self (z.2 - w.2)) hs0.le]

end

end ArtGallery.Orthogonal.Hard
