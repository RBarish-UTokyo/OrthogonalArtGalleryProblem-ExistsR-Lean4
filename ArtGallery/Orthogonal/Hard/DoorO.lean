module

public import ArtGallery.Orthogonal.Hard.RatEq
public import ArtGallery.Stade.NookAlg
public import ArtGallery.Stade.Copy

/-!
# Sight lines through a vertical door

A guard `g` right of a vertical door `x = e` that sees a point `(c, h)` of a vertical nook line
`x = c < e` through a door point `d = (e, d₂)` sees it along the line through `d`: `h` is the
projection of `g` through `d` onto the nook line, which is increasing in `d₂`.  Hence a lower
(upper) bound on `d₂` gives a lower (upper) bound on `h` in terms of the projection through the
corresponding door corner (`door_lower`, `door_upper`), and the guard lies on the ray from the
nook point through the door point (`door_ray`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.Stade

/-- The door point of a sight line, as an affine combination: the guard lies on the ray from the
nook point through the door point, beyond it. -/
theorem door_ray {g d : Point} {c h e : ℝ} (hd1 : d.1 = e) (hc : c < e) (hg : e < g.1)
    (hseg : d ∈ segment g (c, h)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ e = g.1 + t * (c - g.1) ∧ d.2 = g.2 + t * (h - g.2) := by
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hseg
  simp only [lerp] at hd1 ⊢
  refine ⟨t, ?_, ?_, ?_, rfl⟩
  · by_contra h0
    have : t = 0 := le_antisymm (not_lt.1 h0) ht0
    subst this
    linarith
  · by_contra h1
    have : t = 1 := le_antisymm ht1 (not_lt.1 h1)
    subst this
    linarith
  · linarith

/-- **Lower bound through a door corner.** -/
theorem door_lower {g d : Point} {c h e o : ℝ} (hd1 : d.1 = e) (hlo : o ≤ d.2) (hc : c < e)
    (hg : e < g.1) (hseg : d ∈ segment g (c, h)) : vproj g (e, o) c ≤ h := by
  obtain ⟨t, ht0, ht1, he, hd2⟩ := door_ray hd1 hc hg hseg
  have hne : e - g.1 ≠ 0 := by linarith
  have hct : c - g.1 = (e - g.1) / t := by field_simp; linarith
  unfold vproj
  simp only
  rw [hct]
  have : (o - g.2) * ((e - g.1) / t) / (e - g.1) = (o - g.2) / t := by field_simp
  rw [this]
  have : (o - g.2) / t ≤ (d.2 - g.2) / t := div_le_div_of_nonneg_right (by linarith) ht0.le
  rw [hd2] at this
  have e2 : (g.2 + t * (h - g.2) - g.2) / t = h - g.2 := by field_simp; ring
  linarith

/-- **Upper bound through a door corner.** -/
theorem door_upper {g d : Point} {c h e o : ℝ} (hd1 : d.1 = e) (hhi : d.2 ≤ o) (hc : c < e)
    (hg : e < g.1) (hseg : d ∈ segment g (c, h)) : h ≤ vproj g (e, o) c := by
  obtain ⟨t, ht0, ht1, he, hd2⟩ := door_ray hd1 hc hg hseg
  have hne : e - g.1 ≠ 0 := by linarith
  have hct : c - g.1 = (e - g.1) / t := by field_simp; linarith
  unfold vproj
  simp only
  rw [hct]
  have : (o - g.2) * ((e - g.1) / t) / (e - g.1) = (o - g.2) / t := by field_simp
  rw [this]
  have : (d.2 - g.2) / t ≤ (o - g.2) / t := div_le_div_of_nonneg_right (by linarith) ht0.le
  rw [hd2] at this
  have e2 : (g.2 + t * (h - g.2) - g.2) / t = h - g.2 := by field_simp; ring
  linarith

/-- **Collinearity through a vertical door.** -/
theorem door_collinear {g d : Point} {c h e : ℝ} (hd1 : d.1 = e) (hc : c < e) (hg : e < g.1)
    (hseg : d ∈ segment g (c, h)) : (d.2 - h) * (g.1 - c) = (g.2 - h) * (e - c) := by
  obtain ⟨t, -, -, he, hd2⟩ := door_ray hd1 hc hg hseg
  rw [hd2, he]; ring

/-- **Viewers outside a room with a vertical door.**  A point outside the room seeing a point of
the room on the line `x = c` left of the door lies on the door or strictly right of it, and then
it is collinear with the nook point and a point of the door. -/
theorem door_viewer {P : Polygon} {R : Set Point} {c e lo hi : ℝ}
    (hR : P.IsRoom R (segment (e, lo) (e, hi))) (hlo : lo ≤ hi) (hc : c < e) {s p : Point}
    (hsR : s ∈ R) (hs1 : s.1 = c) (hpR : p ∉ R) (hsees : P.Sees p s) :
    p ∈ segment (e, lo) (e, hi) ∨ (e < p.1 ∧ ∃ y, lo ≤ y ∧ y ≤ hi ∧
      (y - s.2) * (p.1 - c) = (p.2 - s.2) * (e - c)) := by
  obtain ⟨q, hqD, hq⟩ := cross_of_sees_room hR hsR hpR hsees
  obtain ⟨hq1, hq2, hq3⟩ := (mem_segment_vert_iff hlo).1 hqD
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hq
  simp only [lerp] at hq1 hq2 hq3
  rcases lt_or_ge e p.1 with hp | hp
  · right
    refine ⟨hp, _, hq2, hq3, ?_⟩
    have e2 : s = (c, s.2) := Prod.ext hs1 rfl
    have hm : lerp p s t ∈ segment p (c, s.2) := by
      rw [← e2]; exact mem_segment_iff_lerp.2 ⟨t, ht0, ht1, rfl⟩
    have := door_collinear (g := p) (d := lerp p s t) (c := c) (h := s.2) (e := e)
      (by simp only [lerp]; linarith) hc hp hm
    simpa [lerp] using this
  · left
    -- the segment from `p` to `s` stays left of `x = e` except at `p`
    have ht : t = 0 := by
      by_contra h0
      have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0)
      have : p.1 + t * (s.1 - p.1) < e := by rw [hs1]; nlinarith
      linarith
    subst ht
    simp only [zero_mul, add_zero] at hq1 hq2 hq3
    have e1 : p = (e, p.2) := Prod.ext (by linarith) rfl
    rw [e1]
    exact (mem_segment_vert_iff hlo).2 ⟨rfl, hq2, hq3⟩

/-- **Lower bound from collinearity through a door point.** -/
theorem door_lower_col {a : Point} {c h e o y : ℝ} (hc : c < e) (ha : e < a.1) (hy : o ≤ y)
    (heq : (y - h) * (a.1 - c) = (a.2 - h) * (e - c)) : vproj a (e, o) c ≤ h := by
  unfold vproj
  simp only
  have hL : 0 < a.1 - c := by linarith
  have hLM : 0 < a.1 - e := by linarith
  have key : (o - a.2) * (c - a.1) / (e - a.1) = (o - a.2) * (a.1 - c) / (a.1 - e) := by
    have : e - a.1 ≠ 0 := by linarith
    field_simp
    ring
  rw [key, ← sub_nonneg]
  have : h - (a.2 + (o - a.2) * (a.1 - c) / (a.1 - e)) =
      ((h - a.2) * (a.1 - e) - (o - a.2) * (a.1 - c)) / (a.1 - e) := by field_simp; ring
  rw [this]
  apply div_nonneg _ hLM.le
  nlinarith

/-- **Upper bound from collinearity through a door point.** -/
theorem door_upper_col {a : Point} {c h e o y : ℝ} (hc : c < e) (ha : e < a.1) (hy : y ≤ o)
    (heq : (y - h) * (a.1 - c) = (a.2 - h) * (e - c)) : h ≤ vproj a (e, o) c := by
  unfold vproj
  simp only
  have hL : 0 < a.1 - c := by linarith
  have hLM : 0 < a.1 - e := by linarith
  have key : (o - a.2) * (c - a.1) / (e - a.1) = (o - a.2) * (a.1 - c) / (a.1 - e) := by
    have : e - a.1 ≠ 0 := by linarith
    field_simp
    ring
  rw [key, ← sub_nonneg]
  have : a.2 + (o - a.2) * (a.1 - c) / (a.1 - e) - h =
      ((o - a.2) * (a.1 - c) - (h - a.2) * (a.1 - e)) / (a.1 - e) := by field_simp; ring
  rw [this]
  apply div_nonneg _ hLM.le
  nlinarith

/-- **Both door bounds for a viewer right of the door.** -/
theorem door_bounds_of_sees {P : Polygon} {R : Set Point} {c e lo hi : ℝ} (hlo : lo ≤ hi)
    (hc : c < e) (hR : P.IsRoom R (segment (e, lo) (e, hi))) {s : Point} (hsR : s ∈ R)
    (hs1 : s.1 = c) {z : Point} (hzR : z ∉ R) (hz1 : e < z.1) (hz : P.Sees z s) :
    vproj z (e, lo) c ≤ s.2 ∧ s.2 ≤ vproj z (e, hi) c := by
  rcases door_viewer hR hlo hc hsR hs1 hzR hz with h | ⟨-, y, hy1, hy2, heq⟩
  · obtain ⟨h1, -, -⟩ := (mem_segment_vert_iff hlo).1 h; linarith
  · exact ⟨door_lower_col hc hz1 hy1 heq, door_upper_col hc hz1 hy2 heq⟩

end

end ArtGallery.Orthogonal.Hard
