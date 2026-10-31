module

public import ArtGallery.Orthogonal.Hard.RatEq
public import ArtGallery.Stade.AdditionAlg

/-!
# The algebra of the orthogonal addition rooms

The orthogonal addition rooms (computed during development) keep the
scales `k_x, k_y, k_z = 1/16, 1/8, 1/24` and the projection identity `Q = (2/3) P + (1/3) R` of
Stade's gadgets (`ArtGallery/Stade/AdditionAlg.lean`), with new openings (slot origin `G`; nook
line `x = G + 30`):

* `addLe`: `P, Q, R = (G + 50, −99), (G + 50, −120), (G + 50, −162)` (aux), `N1, N2, N3 =
  (G + 50, −195/2), (G + 50, −6083/50), (G + 50, −154)` (inputs `x, z, y` at `G + 370, 530, 210`);
* `addGe`: `P, Q, R = (G + 50, −37), (G + 50, −151/3), (G + 50, −77)`, `N1 = (G + 47, −153/4)`
  (recessed), `N2 = (G + 65/2, −5977/100)` (the bay), `N3 = (G + 50, −94)` (inputs `x, y, z` at
  `G + 319, 210, 185/2`).

The helpers attached at the upper ends of the nook segments take a short piece of each nook
line; the coverage hypotheses below are on the remaining parts of the nook lines.  In `addLe`
the z-nook loses a piece of Stade's segment at its top: a covered remainder still forces the
relation, since an uncovered gap at the top would contradict the x- and y-nooks
(`alO_rel_of_cover_alg`).
-/

@[expose] public section

namespace ArtGallery.Orthogonal.Hard

open ArtGallery.Geometry ArtGallery.Stade

/-! ## `addLe` (`v_x + v_y ≤ v_z`) -/

section addLe

variable (G : ℝ)

/-- `addLe`: aux opening `P` of the x-nook. -/
noncomputable def alOP : Point := (G + 50, -99)
/-- `addLe`: aux opening `Q` of the z-nook. -/
noncomputable def alOQ : Point := (G + 50, -120)
/-- `addLe`: aux opening `R` of the y-nook. -/
noncomputable def alOR : Point := (G + 50, -162)
/-- `addLe`: input opening `N1` of the x-nook. -/
noncomputable def alON1 : Point := (G + 50, -195 / 2)
/-- `addLe`: input opening `N2` of the z-nook. -/
noncomputable def alON2 : Point := (G + 50, -6083 / 50)
/-- `addLe`: input opening `N3` of the y-nook. -/
noncomputable def alON3 : Point := (G + 50, -154)

/-- `addLe`: shadow of the x-input of value `v` through `N1`. -/
noncomputable def alOSx (v : ℝ) : ℝ := -3311 / 32 - v / 4
/-- `addLe`: shadow of the y-input of value `v` through `N3`. -/
noncomputable def alOSy (v : ℝ) : ℝ := -173 - v / 2
/-- `addLe`: shadow of the z-input of value `v` through `N2`. -/
noncomputable def alOSz (v : ℝ) : ℝ := -6079 / 48 - v / 6

variable {G}

/-- **Projection identity for `addLe`**: `π_Q = (2/3) π_P + (1/3) π_R`. -/
theorem alO_proj_Q (a : Point) :
    vproj a (alOQ G) (G + 30) =
      2 / 3 * vproj a (alOP G) (G + 30) + 1 / 3 * vproj a (alOR G) (G + 30) := by
  have e : alOQ G = (G + 50, 2 / 3 * (-99) + (1 - 2 / 3) * (-162)) := by
    unfold alOQ; norm_num
  rw [e, vproj_comb]
  unfold alOP alOR
  norm_num

theorem alO_shadow_x (v : ℝ) : vproj (inPt (G + 370) v) (alON1 G) (G + 30) = alOSx v := by
  have h : (alON1 G).1 - (inPt (G + 370) v).1 = -320 := by simp only [alON1, inPt]; ring
  rw [vproj_eq_of h]; simp only [alON1, inPt, alOSx]; ring

theorem alO_shadow_y (v : ℝ) : vproj (inPt (G + 210) v) (alON3 G) (G + 30) = alOSy v := by
  have h : (alON3 G).1 - (inPt (G + 210) v).1 = -160 := by simp only [alON3, inPt]; ring
  rw [vproj_eq_of h]; simp only [alON3, inPt, alOSy]; ring

theorem alO_shadow_z (v : ℝ) : vproj (inPt (G + 530) v) (alON2 G) (G + 30) = alOSz v := by
  have h : (alON2 G).1 - (inPt (G + 530) v).1 = -480 := by simp only [alON2, inPt]; ring
  rw [vproj_eq_of h]; simp only [alON2, inPt, alOSz]; ring

/-- **`addLe`, coverage ⇒ `v_x + v_y ≤ v_z` (algebraic form)**, on the remaining parts
`[−3327/32, −6627/64]`, `[−174, −11085/64]`, `[−3049/24, −24335/192]` of the three nook lines. -/
theorem alO_rel_of_cover_alg (a : Point) {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2)
    (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (_hz1 : 1 / 2 ≤ vz) (hz2 : vz ≤ 2)
    (hcx : ∀ h, -3327 / 32 ≤ h → h ≤ -6627 / 64 → vproj a (alOP G) (G + 30) ≤ h ∨ h ≤ alOSx vx)
    (hcy : ∀ h, -174 ≤ h → h ≤ -11085 / 64 → vproj a (alOR G) (G + 30) ≤ h ∨ h ≤ alOSy vy)
    (hcz : ∀ h, -3049 / 24 ≤ h → h ≤ -24335 / 192 → h ≤ vproj a (alOQ G) (G + 30) ∨ alOSz vz ≤ h) :
    vx + vy ≤ vz := by
  have h1 := le_of_cover_below (by unfold alOSx; linarith) (by unfold alOSx; linarith) hcx
  have h2 := le_of_cover_below (by unfold alOSy; linarith) (by unfold alOSy; linarith) hcy
  have hQ := alO_proj_Q (G := G) a
  by_cases hz : alOSz vz ≤ -24335 / 192
  · have h3 := le_of_cover_above (by unfold alOSz; linarith) hz hcz
    unfold alOSx alOSy alOSz at *
    linarith
  · rcases hcz (-24335 / 192) (by norm_num) le_rfl with h | h
    · unfold alOSx alOSy at *
      linarith
    · exact absurd h hz

end addLe

/-! ## `addGe` (`v_z ≤ v_x + v_y`) -/

section addGe

variable (G : ℝ)

/-- `addGe`: aux opening `P` of the x-nook. -/
noncomputable def agOP : Point := (G + 50, -37)
/-- `addGe`: aux opening `Q` of the z-nook. -/
noncomputable def agOQ : Point := (G + 50, -151 / 3)
/-- `addGe`: aux opening `R` of the y-nook. -/
noncomputable def agOR : Point := (G + 50, -77)
/-- `addGe`: the recessed input opening `N1` of the x-nook. -/
noncomputable def agON1 : Point := (G + 47, -153 / 4)
/-- `addGe`: the input opening `N2` of the z-nook (the bay). -/
noncomputable def agON2 : Point := (G + 65 / 2, -5977 / 100)
/-- `addGe`: input opening `N3` of the y-nook. -/
noncomputable def agON3 : Point := (G + 50, -94)

/-- `addGe`: shadow of the x-input of value `v` through `N1`. -/
noncomputable def agOSx (v : ℝ) : ℝ := -2593 / 64 - v / 4
/-- `addGe`: shadow of the y-input of value `v` through `N3`. -/
noncomputable def agOSy (v : ℝ) : ℝ := -211 / 2 - v / 2
/-- `addGe`: shadow of the z-input of value `v` through `N2`. -/
noncomputable def agOSz (v : ℝ) : ℝ := -5969 / 96 - v / 6

variable {G}

/-- **Projection identity for `addGe`**: `π_Q = (2/3) π_P + (1/3) π_R`. -/
theorem agO_proj_Q (a : Point) :
    vproj a (agOQ G) (G + 30) =
      2 / 3 * vproj a (agOP G) (G + 30) + 1 / 3 * vproj a (agOR G) (G + 30) := by
  have e : agOQ G = (G + 50, 2 / 3 * (-37) + (1 - 2 / 3) * (-77)) := by
    unfold agOQ; norm_num
  rw [e, vproj_comb]
  unfold agOP agOR
  norm_num

theorem agO_shadow_x (v : ℝ) : vproj (inPt (G + 319) v) (agON1 G) (G + 30) = agOSx v := by
  have h : (agON1 G).1 - (inPt (G + 319) v).1 = -272 := by simp only [agON1, inPt]; ring
  rw [vproj_eq_of h]; simp only [agON1, inPt, agOSx]; ring

theorem agO_shadow_y (v : ℝ) : vproj (inPt (G + 210) v) (agON3 G) (G + 30) = agOSy v := by
  have h : (agON3 G).1 - (inPt (G + 210) v).1 = -160 := by simp only [agON3, inPt]; ring
  rw [vproj_eq_of h]; simp only [agON3, inPt, agOSy]; ring

theorem agO_shadow_z (v : ℝ) : vproj (inPt (G + 185 / 2) v) (agON2 G) (G + 30) = agOSz v := by
  have h : (agON2 G).1 - (inPt (G + 185 / 2) v).1 = -60 := by simp only [agON2, inPt]; ring
  rw [vproj_eq_of h]; simp only [agON2, inPt, agOSz]; ring

/-- **`addGe`, coverage ⇒ `v_z ≤ v_x + v_y` (algebraic form)**, on the remaining parts
`[−2649/64, −2595/64]`, `[−855/8, −3381/32]`, `[−6001/96, −2975/48]` of the three nook lines. -/
theorem agO_rel_of_cover_alg (a : Point) {vx vy vz : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2)
    (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) (hz1 : 1 / 2 ≤ vz) (hz2 : vz ≤ 2)
    (hcx : ∀ h, -2649 / 64 ≤ h → h ≤ -2595 / 64 → h ≤ vproj a (agOP G) (G + 30) ∨ agOSx vx ≤ h)
    (hcy : ∀ h, -855 / 8 ≤ h → h ≤ -3381 / 32 → h ≤ vproj a (agOR G) (G + 30) ∨ agOSy vy ≤ h)
    (hcz : ∀ h, -6001 / 96 ≤ h → h ≤ -2975 / 48 → vproj a (agOQ G) (G + 30) ≤ h ∨ h ≤ agOSz vz) :
    vz ≤ vx + vy := by
  have h1 := le_of_cover_above (by unfold agOSx; linarith) (by unfold agOSx; linarith) hcx
  have h2 := le_of_cover_above (by unfold agOSy; linarith) (by unfold agOSy; linarith) hcy
  have h3 := le_of_cover_below (by unfold agOSz; linarith) (by unfold agOSz; linarith) hcz
  rw [agO_proj_Q] at h3
  unfold agOSx agOSy agOSz at *
  linarith

end addGe

end ArtGallery.Orthogonal.Hard

end
