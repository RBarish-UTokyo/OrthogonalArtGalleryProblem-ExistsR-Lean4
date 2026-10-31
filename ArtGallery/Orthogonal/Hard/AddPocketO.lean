module

public import ArtGallery.Orthogonal.Hard.CanonAddO
public import ArtGallery.Orthogonal.Hard.PocketCov

/-!
# The nook conditions of the orthogonal addition rooms

Each of the three nooks of an addition room (`addLe`, `addGe`) has a mouth on the line
`x = G + 50` (for `addGe`'s z-nook: the segment `N₂ Q`) and two guards: the canonical aux guard
`I(v_x, v_y)` and the input guard of the nook.  Every point of the nook segment is reached
through the mouth by one of them (`alO_nook_x`, …): the shadows of the two guards through the
common mouth end coincide (`alOI_P`, `alO_shadow_x`, …, and for the z-nook the projection
identity together with the constraint), and the shadows through the other mouth end lie beyond
the nook (explicit bounds).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.Stade

/-- Crossing a vertical mouth `x = G + 50`, `a ≤ y ≤ b`, towards the nook line `x = G + 30`. -/
theorem mouth_cross {G a b : ℝ} (hab : a < b) {g : Point} (hg : G + 50 < g.1) {h : ℝ}
    (h1 : vproj g (G + 50, a) (G + 30) ≤ h) (h2 : h ≤ vproj g (G + 50, b) (G + 30)) :
    ∃ q ∈ segment ((G + 50, a) : Point) (G + 50, b), q ∈ segment g (G + 30, h) := by
  refine nook_cross hg hg ?_ ?_ h1 h2
  · simp only [det]; nlinarith
  · simp only [det]; nlinarith

/-- The point of the nook line. -/
theorem nook_pt {G lo hi : ℝ} (hlh : lo ≤ hi) {s : Point}
    (hs : s ∈ segment ((G + 30, lo) : Point) (G + 30, hi)) :
    s = (G + 30, s.2) ∧ lo ≤ s.2 ∧ s.2 ≤ hi :=
  nook_side_mem (lo := (G + 30, lo)) (hi := (G + 30, hi)) rfl rfl hlh hs

/-! ### `addLe` -/

section addLe

variable {G vx vy : ℝ}

theorem alOs_ge (hy1 : 1 / 2 ≤ vy) (hxy : vx + vy ≤ 2) :
    20 / 197 ≤ alOs vx vy - 1 := by
  unfold alOs alOSx alOSy; linarith

/-- The shadow of `I` through `N₁` (in terms of `s = alOs`). -/
theorem alOI_N1 (hs : 1 < alOs vx vy) :
    vproj (alOI G vx vy) (alON1 G) (G + 30) = -195 / 2 + 3 / 2 * (alOs vx vy - 1) + 99 + alOSx vx := by
  have hne : alOs vx vy - 1 ≠ 0 := by linarith
  unfold vproj alOI alON1
  simp only
  have h20 : G + 50 - (G + 30 + alOs vx vy * 20 / (alOs vx vy - 1)) = -20 / (alOs vx vy - 1) := by
    field_simp; ring
  rw [h20]
  have : (-20 : ℝ) / (alOs vx vy - 1) ≠ 0 := div_ne_zero (by norm_num) hne
  field_simp
  ring

/-- The shadow of `I` through `N₃`. -/
theorem alOI_N3 (hs : 1 < alOs vx vy) :
    vproj (alOI G vx vy) (alON3 G) (G + 30) = -154 + 8 * (alOs vx vy - 1) + 162 + alOSy vy := by
  have hne : alOs vx vy - 1 ≠ 0 := by linarith
  have e : alOs vx vy * 63 = alOSx vx - alOSy vy := by unfold alOs; ring
  unfold vproj alOI alON3
  simp only
  have h20 : G + 50 - (G + 30 + alOs vx vy * 20 / (alOs vx vy - 1)) = -20 / (alOs vx vy - 1) := by
    field_simp; ring
  rw [h20]
  have : (-20 : ℝ) / (alOs vx vy - 1) ≠ 0 := div_ne_zero (by norm_num) hne
  field_simp
  linear_combination (-(alOs vx vy - 1) * 20) * e

/-- The shadow of `I` through `N₂`. -/
theorem alOI_N2 (hs : 1 < alOs vx vy) :
    vproj (alOI G vx vy) (alON2 G) (G + 30) =
      -6083 / 50 - 1133 / 50 * (alOs vx vy - 1) + 99 + alOSx vx := by
  have hne : alOs vx vy - 1 ≠ 0 := by linarith
  unfold vproj alOI alON2
  simp only
  have h20 : G + 50 - (G + 30 + alOs vx vy * 20 / (alOs vx vy - 1)) = -20 / (alOs vx vy - 1) := by
    field_simp; ring
  rw [h20]
  have : (-20 : ℝ) / (alOs vx vy - 1) ≠ 0 := div_ne_zero (by norm_num) hne
  field_simp
  ring

variable (hx1 : 1 / 2 ≤ vx) (hy1 : 1 / 2 ≤ vy) (hxy : vx + vy ≤ 2)
include hx1 hy1 hxy

theorem alOI_right : G + 50 < (alOI G vx vy).1 := by
  have := (alOI_box (G := G) hx1 (by linarith) hy1 hxy).1; linarith

/-- **The x-nook of `addLe`**: reached through `P N₁` by `I` or by the x-input. -/
theorem alO_nook_x {s : Point}
    (hs : s ∈ segment ((G + 30, -3327 / 32) : Point) (G + 30, -3313 / 32)) :
    (∃ q ∈ segment (alOP G) (alON1 G), q ∈ segment (alOI G vx vy) s) ∨
      ∃ q ∈ segment (alOP G) (alON1 G), q ∈ segment (inPt (G + 370) vx) s := by
  obtain ⟨e, h1, h2⟩ := nook_pt (by norm_num) hs
  have hsg := alOs_gt (by linarith : vx ≤ 2) hy1
  rw [e]
  by_cases hS : alOSx vx ≤ s.2
  · left
    refine mouth_cross (by norm_num) (alOI_right hx1 hy1 hxy) ?_ ?_
    · have := alOI_P (G := G) (by linarith : vx ≤ 2) hy1; unfold alOP at this; rw [this]; exact hS
    · have := alOI_N1 (G := G) hsg; unfold alON1 at this; rw [this]; unfold alOSx; linarith
  · right
    push Not at hS
    refine mouth_cross (by norm_num) (by simp only [inPt_fst]; linarith) ?_ ?_
    · unfold vproj; simp only [inPt]; norm_num; nlinarith
    · have := alO_shadow_x (G := G) vx; unfold alON1 at this; rw [this]; exact hS.le

/-- **The y-nook of `addLe`**: reached through `R N₃` by `I` or by the y-input. -/
theorem alO_nook_y {s : Point}
    (hs : s ∈ segment ((G + 30, -174) : Point) (G + 30, -2771 / 16)) :
    (∃ q ∈ segment (alOR G) (alON3 G), q ∈ segment (alOI G vx vy) s) ∨
      ∃ q ∈ segment (alOR G) (alON3 G), q ∈ segment (inPt (G + 210) vy) s := by
  obtain ⟨e, h1, h2⟩ := nook_pt (by norm_num) hs
  have hsg := alOs_gt (by linarith : vx ≤ 2) hy1
  rw [e]
  by_cases hS : alOSy vy ≤ s.2
  · left
    refine mouth_cross (by norm_num) (alOI_right hx1 hy1 hxy) ?_ ?_
    · have := alOI_R (G := G) (by linarith : vx ≤ 2) hy1; unfold alOR at this; rw [this]; exact hS
    · have := alOI_N3 (G := G) hsg; unfold alON3 at this; rw [this]; unfold alOSy; linarith
  · right
    push Not at hS
    refine mouth_cross (by norm_num) (by simp only [inPt_fst]; linarith) ?_ ?_
    · unfold vproj; simp only [inPt]; norm_num; nlinarith
    · have := alO_shadow_y (G := G) vy; unfold alON3 at this; rw [this]; exact hS.le

/-- **The z-nook of `addLe`** (`v_x + v_y ≤ v_z`): reached through `N₂ Q` by `I` or by the
z-input. -/
theorem alO_nook_z {vz : ℝ} (hz : vx + vy ≤ vz) (hz2 : vz ≤ 2) {s : Point}
    (hs : s ∈ segment ((G + 30, -3049 / 24) : Point) (G + 30, -6083 / 48)) :
    (∃ q ∈ segment (alON2 G) (alOQ G), q ∈ segment (alOI G vx vy) s) ∨
      ∃ q ∈ segment (alON2 G) (alOQ G), q ∈ segment (inPt (G + 530) vz) s := by
  obtain ⟨e, h1, h2⟩ := nook_pt (by norm_num) hs
  have hsg := alOs_gt (by linarith : vx ≤ 2) hy1
  have hs20 := alOs_ge hy1 hxy
  rw [e]
  by_cases hS : s.2 ≤ 2 / 3 * alOSx vx + 1 / 3 * alOSy vy
  · left
    refine mouth_cross (by norm_num) (alOI_right hx1 hy1 hxy) ?_ ?_
    · have := alOI_N2 (G := G) hsg; unfold alON2 at this; rw [this]; unfold alOSx; nlinarith
    · have hQ := alO_proj_Q (G := G) (alOI G vx vy)
      rw [alOI_P (by linarith : vx ≤ 2) hy1, alOI_R (by linarith : vx ≤ 2) hy1] at hQ
      unfold alOQ at hQ; rw [hQ]; exact hS
  · right
    push Not at hS
    refine mouth_cross (by norm_num) (by simp only [inPt_fst]; linarith) ?_ ?_
    · have := alO_shadow_z (G := G) vz; unfold alON2 at this; rw [this]
      unfold alOSx alOSy at hS; unfold alOSz; linarith
    · unfold vproj; simp only [inPt]; norm_num; nlinarith

end addLe


/-! ### `addGe` -/

section addGe

variable {G vx vy : ℝ}

theorem agOs_bounds (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) :
    3 / 5 ≤ agOs vx vy - 1 ∧ agOs vx vy - 1 ≤ 2 / 3 := by
  unfold agOs agOSx agOSy; constructor <;> linarith

/-- The shadow of a point given in the parameter `u = 1/t`. -/
theorem vproj_u {g O : Point} {c a b p q ox oy cx t : ℝ}
    (hg : g = (a + p * (1 / t), b + q * (1 / t))) (hO : O = (a + ox, b + oy)) (hc : c = a + cx)
    (ht : t ≠ 0) :
    vproj g O c = b + q / t + (oy - q / t) * ((p - cx * t) / (p - ox * t)) := by
  subst hg hO hc
  unfold vproj
  simp only
  have h1 : a + cx - (a + p * (1 / t)) = (cx * t - p) / t := by field_simp; ring
  have h2 : a + ox - (a + p * (1 / t)) = (ox * t - p) / t := by field_simp; ring
  have h3 : (p - cx * t) / (p - ox * t) = (cx * t - p) / (ox * t - p) := by
    rw [← neg_div_neg_eq, neg_sub, neg_sub]
  rw [h3, h1, h2, mul_div_assoc, div_div_div_cancel_right₀ ht]
  ring

/-- The shadow of `I` through `N₁`. -/
theorem agOI_N1 (hs : 1 < agOs vx vy) :
    vproj (agOI G vx vy) (agON1 G) (G + 30) =
      (-136 * (agOs vx vy - 1) - 765 + 17 * (37 + agOSx vx)) / (3 * (agOs vx vy - 1) + 20) := by
  have hne : agOs vx vy - 1 ≠ 0 := by linarith
  have hd' : 3 * (agOs vx vy - 1) + 20 ≠ 0 := by linarith
  rw [vproj_u (ox := -3) (oy := -5 / 4) (cx := -20) (agOI_eq_P G vx vy hs) (by unfold agON1; ext <;> simp only <;> ring) (by ring) hne]
  generalize agOs vx vy - 1 = t at hne hd' ⊢
  rw [show (20 : ℝ) - -3 * t = 3 * t + 20 by ring]
  obtain ⟨D, hDt⟩ : ∃ D, D = 3 * t + 20 := ⟨_, rfl⟩
  rw [← hDt]
  have hD : D ≠ 0 := hDt ▸ hd'
  field_simp
  subst hDt
  ring

/-- The shadow of `I` through `N₃`. -/
theorem agOI_N3 (hs : 1 < agOs vx vy) :
    vproj (agOI G vx vy) (agON3 G) (G + 30) =
      -17 * (agOs vx vy - 1) - 94 + (77 + agOSy vy) := by
  have hne : agOs vx vy - 1 ≠ 0 := by linarith
  rw [vproj_u (ox := 0) (oy := -17) (cx := -20) (agOI_eq_R G vx vy hs) (by unfold agON3; ext <;> simp only <;> ring) (by ring) hne]
  generalize agOs vx vy - 1 = t at hne ⊢
  field_simp
  ring

/-- The shadow of `I` through `N₂`. -/
theorem agOI_N2 (hs : 1 < agOs vx vy) :
    vproj (agOI G vx vy) (agON2 G) (G + 30) =
      (-11029 / 10 * (agOs vx vy - 1) - 5977 / 5 + 5 / 2 * (37 + agOSx vx)) /
        (35 / 2 * (agOs vx vy - 1) + 20) := by
  have hne : agOs vx vy - 1 ≠ 0 := by linarith
  have hd' : 35 / 2 * (agOs vx vy - 1) + 20 ≠ 0 := by linarith
  rw [vproj_u (ox := -35 / 2) (oy := -2277 / 100) (cx := -20) (agOI_eq_P G vx vy hs) (by unfold agON2; ext <;> simp only <;> ring) (by ring) hne]
  generalize agOs vx vy - 1 = t at hne hd' ⊢
  rw [show (20 : ℝ) - -35 / 2 * t = 35 / 2 * t + 20 by ring]
  obtain ⟨D, hDt⟩ : ∃ D, D = 35 / 2 * t + 20 := ⟨_, rfl⟩
  rw [← hDt]
  have hD : D ≠ 0 := hDt ▸ hd'
  field_simp
  subst hDt
  ring

/-- A guard right of the mouth line `N₁ P` of the x-nook. -/
theorem agO_side_x {g : Point} (hg : 3 * (g.2 + 153 / 4) < 5 / 4 * (g.1 - (G + 47))) {h : ℝ}
    (hh : -45 < h) :
    det (agON1 G) (agOP G) g < 0 ∧ 0 < det (agON1 G) (agOP G) (G + 30, h) := by
  unfold agON1 agOP det; simp only; constructor <;> nlinarith

/-- A guard right of the mouth line `Q N₂` of the z-nook. -/
theorem agO_side_z {g : Point}
    (hg : -35 / 2 * (g.2 + 151 / 3) + (5977 / 100 - 151 / 3) * (g.1 - (G + 50)) < 0) {h : ℝ}
    (hh : h ≤ -5941 / 96) :
    det (agOQ G) (agON2 G) g < 0 ∧ 0 < det (agOQ G) (agON2 G) (G + 30, h) := by
  unfold agOQ agON2 det; simp only; constructor <;> nlinarith

variable (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2)
include hx1 hx2 hy1 hy2

omit hx1 hy2 in
theorem agOI_right : G + 50 < (agOI G vx vy).1 := by
  have hs := agOs_gt hx2 hy1
  rw [agOI_eq_P G vx vy hs]
  simp only
  have : 0 < 1 / (agOs vx vy - 1) := by apply div_pos one_pos; linarith
  linarith

/-- **The x-nook of `addGe`**: reached through `N₁ P` by `I` or by the x-input. -/
theorem agO_nook_x {s : Point}
    (hs : s ∈ segment ((G + 30, -2649 / 64) : Point) (G + 30, -2589 / 64)) :
    (∃ q ∈ segment (agON1 G) (agOP G), q ∈ segment (agOI G vx vy) s) ∨
      ∃ q ∈ segment (agON1 G) (agOP G), q ∈ segment (inPt (G + 319) vx) s := by
  obtain ⟨e, h1, h2⟩ := nook_pt (by norm_num) hs
  have hsg := agOs_gt hx2 hy1
  obtain ⟨t1, t2⟩ := agOs_bounds hx1 hx2 hy1 hy2
  rw [e]
  by_cases hS : s.2 ≤ agOSx vx
  · left
    have hI := agOI_right (G := G) hx2 hy1
    have hIy : 3 * ((agOI G vx vy).2 + 153 / 4) < 5 / 4 * ((agOI G vx vy).1 - (G + 47)) := by
      rw [agOI_eq_P G vx vy hsg]; simp only
      have hu : 3 / 2 ≤ 1 / (agOs vx vy - 1) := by
        rw [le_div_iff₀ (by linarith)]; nlinarith
      unfold agOSx; nlinarith
    obtain ⟨d1, d2⟩ := agO_side_x (G := G) hIy (h := s.2) (by linarith)
    refine nook_cross (by unfold agON1; linarith) (by unfold agOP; linarith) d1 d2 ?_ ?_
    · rw [agOI_N1 hsg, div_le_iff₀ (by linarith)]; unfold agOSx; nlinarith
    · rw [agOI_P hx2 hy1]; exact hS
  · right
    push Not at hS
    have hg : 3 * ((inPt (G + 319) vx).2 + 153 / 4) < 5 / 4 * ((inPt (G + 319) vx).1 - (G + 47)) := by
      simp only [inPt]; nlinarith
    obtain ⟨d1, d2⟩ := agO_side_x (G := G) hg (h := s.2) (by linarith)
    refine nook_cross (by unfold agON1; simp only [inPt]; linarith)
      (by unfold agOP; simp only [inPt]; linarith) d1 d2 ?_ ?_
    · rw [agO_shadow_x]; exact hS.le
    · unfold vproj agOP; simp only [inPt]; norm_num; nlinarith

/-- **The y-nook of `addGe`**: reached through `N₃ R` by `I` or by the y-input. -/
theorem agO_nook_y {s : Point}
    (hs : s ∈ segment ((G + 30, -855 / 8) : Point) (G + 30, -1689 / 16)) :
    (∃ q ∈ segment (agON3 G) (agOR G), q ∈ segment (agOI G vx vy) s) ∨
      ∃ q ∈ segment (agON3 G) (agOR G), q ∈ segment (inPt (G + 210) vy) s := by
  obtain ⟨e, h1, h2⟩ := nook_pt (by norm_num) hs
  have hsg := agOs_gt hx2 hy1
  obtain ⟨t1, t2⟩ := agOs_bounds hx1 hx2 hy1 hy2
  rw [e]
  by_cases hS : s.2 ≤ agOSy vy
  · left
    refine mouth_cross (by norm_num) (agOI_right hx2 hy1) ?_ ?_
    · have := agOI_N3 (G := G) hsg; unfold agON3 at this; rw [this]; unfold agOSy; nlinarith
    · have := agOI_R (G := G) hx2 hy1; unfold agOR at this; rw [this]; exact hS
  · right
    push Not at hS
    refine mouth_cross (by norm_num) (by simp only [inPt_fst]; linarith) ?_ ?_
    · have := agO_shadow_y (G := G) vy; unfold agON3 at this; rw [this]; exact hS.le
    · unfold vproj; simp only [inPt]; norm_num; nlinarith

/-- **The z-nook of `addGe`** (`v_z ≤ v_x + v_y`): reached through `Q N₂` by `I` or by the
z-input. -/
theorem agO_nook_z {vz : ℝ} (hz : vz ≤ vx + vy) (hz1 : 1 / 2 ≤ vz) {s : Point}
    (hs : s ∈ segment ((G + 30, -6001 / 96) : Point) (G + 30, -5941 / 96)) :
    (∃ q ∈ segment (agOQ G) (agON2 G), q ∈ segment (agOI G vx vy) s) ∨
      ∃ q ∈ segment (agOQ G) (agON2 G), q ∈ segment (inPt (G + 185 / 2) vz) s := by
  obtain ⟨e, h1, h2⟩ := nook_pt (by norm_num) hs
  have hsg := agOs_gt hx2 hy1
  obtain ⟨t1, t2⟩ := agOs_bounds hx1 hx2 hy1 hy2
  rw [e]
  by_cases hS : 2 / 3 * agOSx vx + 1 / 3 * agOSy vy ≤ s.2
  · left
    have hI := agOI_right (G := G) hx2 hy1
    have hIy : -35 / 2 * ((agOI G vx vy).2 + 151 / 3) +
        (5977 / 100 - 151 / 3) * ((agOI G vx vy).1 - (G + 50)) < 0 := by
      rw [agOI_eq_P G vx vy hsg]; simp only
      have hu : 3 / 2 ≤ 1 / (agOs vx vy - 1) := by
        rw [le_div_iff₀ (by linarith)]; nlinarith
      have hu' : 1 / (agOs vx vy - 1) ≤ 5 / 3 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      unfold agOSx; nlinarith
    obtain ⟨d1, d2⟩ := agO_side_z (G := G) hIy (h := s.2) (by linarith)
    refine nook_cross (by unfold agOQ; linarith) (by unfold agON2; linarith) d1 d2 ?_ ?_
    · have hQ := agO_proj_Q (G := G) (agOI G vx vy)
      rw [agOI_P hx2 hy1, agOI_R hx2 hy1] at hQ
      rw [hQ]; exact hS
    · rw [agOI_N2 hsg, le_div_iff₀ (by linarith)]; unfold agOSx; nlinarith
  · right
    push Not at hS
    have hg : -35 / 2 * ((inPt (G + 185 / 2) vz).2 + 151 / 3) +
        (5977 / 100 - 151 / 3) * ((inPt (G + 185 / 2) vz).1 - (G + 50)) < 0 := by
      simp only [inPt]; nlinarith
    obtain ⟨d1, d2⟩ := agO_side_z (G := G) hg (h := s.2) (by linarith)
    refine nook_cross (by unfold agOQ; simp only [inPt]; linarith)
      (by unfold agON2; simp only [inPt]; linarith) d1 d2 ?_ ?_
    · unfold vproj agOQ; simp only [inPt]; norm_num; nlinarith
    · rw [agO_shadow_z]; unfold agOSx agOSy at hS; unfold agOSz; linarith

end addGe

end

end ArtGallery.Orthogonal.Hard
