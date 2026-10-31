module

public import ArtGallery.Orthogonal.Hard.AddAlgO

/-!
# The canonical aux guards of the orthogonal addition gadgets

For input values `v_x, v_y`, the canonical aux guard `I(v_x, v_y)` is the intersection of the
line through `P` and the x-shadow `S_x(v_x)` with the line through `R` and the y-shadow
`S_y(v_y)` (computed during development): its projections through `P` and `R`
onto the nook line are the shadows (`agOI_P`, `agOI_R`, `alOI_P`, `alOI_R`).

Ranges: for `addGe` the point lies in the convex hull of its values at the four corners
`v_x, v_y ∈ {1/2, 2}` (`agOI_mem_convex`); for `addLe` with `v_x + v_y ≤ 2` it lies in the box
`[G + 226, G + 247] × [−59, −51]` (`alOI_box`) and in the convex hull of its values at
`(1/2, 1/2), (3/2, 1/2), (1/2, 3/2)` (`alOI_mem_convex`: the hypotenuse `v_x + v_y = 2` is mapped
onto a segment).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade ArtGallery.Geometry

/-! ### `addGe` -/

/-- The parameter `s = (S_x − S_y) / (p − r)` of the `addGe` aux point. -/
noncomputable def agOs (vx vy : ℝ) : ℝ := (agOSx vx - agOSy vy) / 40

/-- **The canonical `addGe` aux point.** -/
noncomputable def agOI (G vx vy : ℝ) : Point :=
  (G + 30 + agOs vx vy * 20 / (agOs vx vy - 1), (agOs vx vy * -37 - agOSx vx) / (agOs vx vy - 1))

theorem agOs_gt {vx vy : ℝ} (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) : 1 < agOs vx vy := by
  unfold agOs agOSx agOSy; linarith

theorem agOI_P {G vx vy : ℝ} (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) :
    vproj (agOI G vx vy) (agOP G) (G + 30) = agOSx vx := by
  have hs := agOs_gt hx2 hy1
  have hne : agOs vx vy - 1 ≠ 0 := by linarith
  unfold vproj agOI agOP
  simp only
  have h20 : (G + 50 - (G + 30 + agOs vx vy * 20 / (agOs vx vy - 1))) = -20 / (agOs vx vy - 1) := by
    field_simp; ring
  rw [h20]
  have h20' : (-20 : ℝ) / (agOs vx vy - 1) ≠ 0 := div_ne_zero (by norm_num) hne
  field_simp
  ring

theorem agOI_R {G vx vy : ℝ} (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) :
    vproj (agOI G vx vy) (agOR G) (G + 30) = agOSy vy := by
  have hs := agOs_gt hx2 hy1
  have hne : agOs vx vy - 1 ≠ 0 := by linarith
  unfold vproj agOI agOR
  simp only
  have h20 : (G + 50 - (G + 30 + agOs vx vy * 20 / (agOs vx vy - 1))) = -20 / (agOs vx vy - 1) := by
    field_simp; ring
  rw [h20]
  have e : agOs vx vy * 40 = agOSx vx - agOSy vy := by unfold agOs; ring
  field_simp
  linear_combination (-(agOs vx vy - 1) * 20) * e

/-! ### `addLe` -/

/-- The parameter `s = (S_x − S_y) / (p − r)` of the `addLe` aux point. -/
noncomputable def alOs (vx vy : ℝ) : ℝ := (alOSx vx - alOSy vy) / 63

/-- **The canonical `addLe` aux point.** -/
noncomputable def alOI (G vx vy : ℝ) : Point :=
  (G + 30 + alOs vx vy * 20 / (alOs vx vy - 1), (alOs vx vy * -99 - alOSx vx) / (alOs vx vy - 1))

theorem alOs_gt {vx vy : ℝ} (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) : 1 < alOs vx vy := by
  unfold alOs alOSx alOSy; linarith

theorem alOI_P {G vx vy : ℝ} (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) :
    vproj (alOI G vx vy) (alOP G) (G + 30) = alOSx vx := by
  have hs := alOs_gt hx2 hy1
  have hne : alOs vx vy - 1 ≠ 0 := by linarith
  unfold vproj alOI alOP
  simp only
  have h20 : (G + 50 - (G + 30 + alOs vx vy * 20 / (alOs vx vy - 1))) = -20 / (alOs vx vy - 1) := by
    field_simp; ring
  rw [h20]
  field_simp
  ring

theorem alOI_R {G vx vy : ℝ} (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) :
    vproj (alOI G vx vy) (alOR G) (G + 30) = alOSy vy := by
  have hs := alOs_gt hx2 hy1
  have hne : alOs vx vy - 1 ≠ 0 := by linarith
  unfold vproj alOI alOR
  simp only
  have h20 : (G + 50 - (G + 30 + alOs vx vy * 20 / (alOs vx vy - 1))) = -20 / (alOs vx vy - 1) := by
    field_simp; ring
  rw [h20]
  have e : alOs vx vy * 63 = alOSx vx - alOSy vy := by unfold alOs; ring
  field_simp
  linear_combination (-(alOs vx vy - 1) * 20) * e

/-! ### Ranges -/

/-- A point affine in a parameter between two values lies on the segment of its two values. -/
theorem affine_mem_segment (A B C D u u0 u1 : ℝ) (h : (u0 ≤ u ∧ u ≤ u1) ∨ (u1 ≤ u ∧ u ≤ u0)) :
    ((A + B * u, C + D * u) : Point) ∈
      ArtGallery.segment (A + B * u0, C + D * u0) (A + B * u1, C + D * u1) := by
  rcases eq_or_ne u0 u1 with he | hne
  · subst he
    have : u = u0 := by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    subst this
    exact ⟨0, le_rfl, zero_le_one, by simp⟩
  · have hd : u1 - u0 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    refine ⟨(u - u0) / (u1 - u0), ?_, ?_, ?_⟩
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact div_nonneg (by linarith) (by linarith)
      · exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [div_le_one (lt_of_le_of_ne (by linarith) (Ne.symm hd))]; linarith
      · rw [div_le_one_of_neg (lt_of_le_of_ne (by linarith) hd)]; linarith
    · refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring

/-- The `addGe` aux point in the parameter `u = 1/(s − 1)`, on the line through `P`. -/
theorem agOI_eq_P (G vx vy : ℝ) (hs : 1 < agOs vx vy) :
    agOI G vx vy = (G + 50 + 20 * (1 / (agOs vx vy - 1)),
      -37 + (-(37 + agOSx vx)) * (1 / (agOs vx vy - 1))) := by
  have hne : agOs vx vy - 1 ≠ 0 := by linarith
  unfold agOI
  refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring

/-- The `addGe` aux point in the parameter `u = 1/(s − 1)`, on the line through `R`. -/
theorem agOI_eq_R (G vx vy : ℝ) (hs : 1 < agOs vx vy) :
    agOI G vx vy = (G + 50 + 20 * (1 / (agOs vx vy - 1)),
      -77 + (-(77 + agOSy vy)) * (1 / (agOs vx vy - 1))) := by
  have hne : agOs vx vy - 1 ≠ 0 := by linarith
  have e : agOs vx vy * 40 = agOSx vx - agOSy vy := by unfold agOs; ring
  unfold agOI
  refine Prod.ext ?_ ?_ <;> simp only
  · field_simp; ring
  · field_simp; linear_combination e

/-- **The `addGe` aux point lies in every convex set containing its four corner values.** -/
theorem agOI_mem_convex {G : ℝ} {S : Set Point} (hS : Convex ℝ S)
    (h00 : agOI G (1 / 2) (1 / 2) ∈ S) (h02 : agOI G (1 / 2) 2 ∈ S)
    (h20 : agOI G 2 (1 / 2) ∈ S) (h22 : agOI G 2 2 ∈ S) {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx)
    (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy) (hy2 : vy ≤ 2) : agOI G vx vy ∈ S := by
  have hS' : Convex ℝ S := hS
  have seg : ∀ a b : Point, a ∈ S → b ∈ S → ArtGallery.segment a b ⊆ S := fun a b ha hb => by
    rw [segment_eq]; exact hS'.segment_subset ha hb
  have hs : ∀ a b, a ≤ 2 → 1 / 2 ≤ b → 1 < agOs a b := fun a b ha hb => agOs_gt ha hb
  -- the parameter `u` is increasing in `v_x` and decreasing in `v_y`
  have umono : ∀ a a' b b', a ≤ a' → b' ≤ b → a' ≤ 2 → 1 / 2 ≤ b' →
      1 / (agOs a b - 1) ≤ 1 / (agOs a' b' - 1) := by
    intro a a' b b' haa hbb ha' hb'
    have h1 := hs a' b' ha' hb'
    apply one_div_le_one_div_of_le (by linarith)
    unfold agOs agOSx agOSy; linarith
  -- on the line through `P` (fixed `v_x`): between the values at `v_y = 1/2` and `v_y = 2`
  have side : ∀ a, 1 / 2 ≤ a → a ≤ 2 → agOI G a 2 ∈ S → agOI G a (1 / 2) ∈ S →
      agOI G a vy ∈ S := by
    intro a ha1 ha2 h2 h1
    have hm := affine_mem_segment (G + 50) 20 (-37) (-(37 + agOSx a)) (1 / (agOs a vy - 1))
      (1 / (agOs a 2 - 1)) (1 / (agOs a (1 / 2) - 1))
      (Or.inl ⟨umono a a 2 vy le_rfl hy2 ha2 hy1, umono a a vy (1 / 2) le_rfl hy1 ha2 le_rfl⟩)
    rw [← agOI_eq_P G a vy (hs a vy ha2 hy1), ← agOI_eq_P G a 2 (hs a 2 ha2 (by norm_num)),
      ← agOI_eq_P G a (1 / 2) (hs a (1 / 2) ha2 le_rfl)] at hm
    exact seg _ _ h2 h1 hm
  have hL := side (1 / 2) le_rfl (by norm_num) h02 h00
  have hR := side 2 (by norm_num) le_rfl h22 h20
  -- on the line through `R` (fixed `v_y`): between the values at `v_x = 1/2` and `v_x = 2`
  have hm := affine_mem_segment (G + 50) 20 (-77) (-(77 + agOSy vy)) (1 / (agOs vx vy - 1))
    (1 / (agOs (1 / 2) vy - 1)) (1 / (agOs 2 vy - 1))
    (Or.inl ⟨umono (1 / 2) vx vy vy hx1 le_rfl hx2 hy1, umono vx 2 vy vy hx2 le_rfl le_rfl hy1⟩)
  rw [← agOI_eq_R G vx vy (hs vx vy hx2 hy1), ← agOI_eq_R G (1 / 2) vy (hs _ vy (by norm_num) hy1),
    ← agOI_eq_R G 2 vy (hs 2 vy le_rfl hy1)] at hm
  exact seg _ _ hL hR hm

/-- **The `addLe` aux point** (for `v_x + v_y ≤ 2`) lies in `[G + 226, G + 247] × [−59, −51]`. -/
theorem alOI_box {G vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hx2 : vx ≤ 2) (hy1 : 1 / 2 ≤ vy)
    (hxy : vx + vy ≤ 2) :
    G + 226 ≤ (alOI G vx vy).1 ∧ (alOI G vx vy).1 ≤ G + 247 ∧ -59 ≤ (alOI G vx vy).2 ∧
      (alOI G vx vy).2 ≤ -51 := by
  have hs := alOs_gt hx2 hy1
  have hpos : 0 < alOs vx vy - 1 := by linarith
  have e1 : (alOI G vx vy).1 = G + 50 + 20 / (alOs vx vy - 1) := by
    unfold alOI; simp only; field_simp; ring
  have e2 : (alOI G vx vy).2 = -99 - (99 + alOSx vx) / (alOs vx vy - 1) := by
    unfold alOI; simp only; field_simp; ring
  have hsd : alOs vx vy - 1 = (alOSx vx - alOSy vy - 63) / 63 := by unfold alOs; ring
  rw [e1, e2]
  have h1 : alOs vx vy - 1 ≤ 5 / 44 := by rw [hsd]; unfold alOSx alOSy; linarith
  have h2 : 20 / 197 ≤ alOs vx vy - 1 := by rw [hsd]; unfold alOSx alOSy; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (20 : ℝ) / (alOs vx vy - 1) = 20 * (1 / (alOs vx vy - 1)) by ring]
    have := one_div_le_one_div_of_le hpos h1
    nlinarith
  · rw [show (20 : ℝ) / (alOs vx vy - 1) = 20 * (1 / (alOs vx vy - 1)) by ring]
    have := one_div_le_one_div_of_le (by norm_num) h2
    nlinarith
  · rw [show -99 - (99 + alOSx vx) / (alOs vx vy - 1) =
        -99 + 63 * (vx / 4 + 143 / 32) / (209 / 32 - vx / 4 + vy / 2) by
      rw [hsd]; unfold alOSx alOSy
      have : (209 / 32 - vx / 4 + vy / 2 : ℝ) ≠ 0 := by linarith
      have : ((-3311 / 32 - vx / 4) - (-173 - vy / 2) - 63 : ℝ) ≠ 0 := by linarith
      field_simp; ring]
    have hb : (0 : ℝ) < 209 / 32 - vx / 4 + vy / 2 := by linarith
    have : 40 * (209 / 32 - vx / 4 + vy / 2) ≤ 63 * (vx / 4 + 143 / 32) := by linarith
    have := (le_div_iff₀ hb).2 this
    linarith
  · rw [show -99 - (99 + alOSx vx) / (alOs vx vy - 1) =
        -99 + 63 * (vx / 4 + 143 / 32) / (209 / 32 - vx / 4 + vy / 2) by
      rw [hsd]; unfold alOSx alOSy
      have : (209 / 32 - vx / 4 + vy / 2 : ℝ) ≠ 0 := by linarith
      have : ((-3311 / 32 - vx / 4) - (-173 - vy / 2) - 63 : ℝ) ≠ 0 := by linarith
      field_simp; ring]
    have hb : (0 : ℝ) < 209 / 32 - vx / 4 + vy / 2 := by linarith
    have : 63 * (vx / 4 + 143 / 32) ≤ 48 * (209 / 32 - vx / 4 + vy / 2) := by linarith
    have := (div_le_iff₀ hb).2 this
    linarith


/-- The `addLe` aux point in the parameter `u = 1/(s − 1)`, on the line through `P`. -/
theorem alOI_eq_P (G vx vy : ℝ) (hs : 1 < alOs vx vy) :
    alOI G vx vy = (G + 50 + 20 * (1 / (alOs vx vy - 1)),
      -99 + (-(99 + alOSx vx)) * (1 / (alOs vx vy - 1))) := by
  have hne : alOs vx vy - 1 ≠ 0 := by linarith
  unfold alOI
  refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring

/-- The `addLe` aux point in the parameter `u = 1/(s − 1)`, on the line through `R`. -/
theorem alOI_eq_R (G vx vy : ℝ) (hs : 1 < alOs vx vy) :
    alOI G vx vy = (G + 50 + 20 * (1 / (alOs vx vy - 1)),
      -162 + (-(162 + alOSy vy)) * (1 / (alOs vx vy - 1))) := by
  have hne : alOs vx vy - 1 ≠ 0 := by linarith
  have e : alOs vx vy * 63 = alOSx vx - alOSy vy := by unfold alOs; ring
  unfold alOI
  refine Prod.ext ?_ ?_ <;> simp only
  · field_simp; ring
  · field_simp; linear_combination e

/-- On the hypotenuse `v_y = 2 − v_x` the `addLe` aux point is affine in `u = 1/(s − 1)`. -/
theorem alOI_eq_hyp (G a : ℝ) (hs : 1 < alOs a (2 - a)) :
    alOI G a (2 - a) = (G + 50 + 20 * (1 / (alOs a (2 - a) - 1)),
      -120 + 335 / 48 * (1 / (alOs a (2 - a) - 1))) := by
  have hne : alOs a (2 - a) - 1 ≠ 0 := by linarith
  have e : alOs a (2 - a) * 63 = 2257 / 32 - 3 * a / 4 := by unfold alOs alOSx alOSy; ring
  unfold alOI
  refine Prod.ext ?_ ?_ <;> simp only
  · field_simp; ring
  · unfold alOSx; field_simp; linear_combination 2048 * e

/-- **The `addLe` aux point (for `v_x + v_y ≤ 2`) lies in every convex set containing its values
at `(1/2, 1/2)`, `(3/2, 1/2)`, `(1/2, 3/2)`.** -/
theorem alOI_mem_convex {G : ℝ} {S : Set Point} (hS : Convex ℝ S)
    (h00 : alOI G (1 / 2) (1 / 2) ∈ S) (h10 : alOI G (3 / 2) (1 / 2) ∈ S)
    (h01 : alOI G (1 / 2) (3 / 2) ∈ S) {vx vy : ℝ} (hx1 : 1 / 2 ≤ vx) (hy1 : 1 / 2 ≤ vy)
    (hxy : vx + vy ≤ 2) : alOI G vx vy ∈ S := by
  have hS' : Convex ℝ S := hS
  have seg : ∀ a b : Point, a ∈ S → b ∈ S → ArtGallery.segment a b ⊆ S := fun a b ha hb => by
    rw [segment_eq]; exact hS'.segment_subset ha hb
  have hs : ∀ a b, a ≤ 2 → 1 / 2 ≤ b → 1 < alOs a b := fun a b ha hb => alOs_gt ha hb
  -- the parameter `u` is increasing in `v_x` and decreasing in `v_y`
  have umono : ∀ a a' b b', a ≤ a' → b' ≤ b → a' ≤ 2 → 1 / 2 ≤ b' →
      1 / (alOs a b - 1) ≤ 1 / (alOs a' b' - 1) := by
    intro a a' b b' haa hbb ha' hb'
    have h1 := hs a' b' ha' hb'
    apply one_div_le_one_div_of_le (by linarith)
    unfold alOs alOSx alOSy; linarith
  have hx2 : vx ≤ 3 / 2 := by linarith
  -- on the line through `R` at `v_y = 1/2`
  have hB : alOI G vx (1 / 2) ∈ S := by
    have hm := affine_mem_segment (G + 50) 20 (-162) (-(162 + alOSy (1 / 2)))
      (1 / (alOs vx (1 / 2) - 1)) (1 / (alOs (1 / 2) (1 / 2) - 1)) (1 / (alOs (3 / 2) (1 / 2) - 1))
      (Or.inl ⟨umono _ _ _ _ hx1 le_rfl (by linarith) le_rfl,
        umono _ _ _ _ hx2 le_rfl (by norm_num) le_rfl⟩)
    rw [← alOI_eq_R G vx (1 / 2) (hs _ _ (by linarith) le_rfl),
      ← alOI_eq_R G (1 / 2) (1 / 2) (hs _ _ (by norm_num) le_rfl),
      ← alOI_eq_R G (3 / 2) (1 / 2) (hs _ _ (by norm_num) le_rfl)] at hm
    exact seg _ _ h00 h10 hm
  -- on the hypotenuse
  have hH : alOI G vx (2 - vx) ∈ S := by
    have hm := affine_mem_segment (G + 50) 20 (-120) (335 / 48)
      (1 / (alOs vx (2 - vx) - 1)) (1 / (alOs (1 / 2) (2 - 1 / 2) - 1))
      (1 / (alOs (3 / 2) (2 - 3 / 2) - 1))
      (Or.inl ⟨umono _ _ _ _ hx1 (by linarith) (by linarith) (by linarith),
        umono _ _ _ _ hx2 (by linarith) (by norm_num) (by norm_num)⟩)
    rw [← alOI_eq_hyp G vx (hs _ _ (by linarith) (by linarith)),
      ← alOI_eq_hyp G (1 / 2) (hs _ _ (by norm_num) (by norm_num)),
      ← alOI_eq_hyp G (3 / 2) (hs _ _ (by norm_num) (by norm_num))] at hm
    have e1 : (2 : ℝ) - 1 / 2 = 3 / 2 := by norm_num
    have e2 : (2 : ℝ) - 3 / 2 = 1 / 2 := by norm_num
    rw [e1, e2] at hm
    exact seg _ _ h01 h10 hm
  -- on the line through `P` at `v_x`
  have hm := affine_mem_segment (G + 50) 20 (-99) (-(99 + alOSx vx)) (1 / (alOs vx vy - 1))
    (1 / (alOs vx (2 - vx) - 1)) (1 / (alOs vx (1 / 2) - 1))
    (Or.inl ⟨umono _ _ _ _ le_rfl (by linarith) (by linarith) hy1,
      umono _ _ _ _ le_rfl hy1 (by linarith) le_rfl⟩)
  rw [← alOI_eq_P G vx vy (hs _ _ (by linarith) hy1),
    ← alOI_eq_P G vx (2 - vx) (hs _ _ (by linarith) (by linarith)),
    ← alOI_eq_P G vx (1 / 2) (hs _ _ (by linarith) le_rfl)] at hm
  exact seg _ _ hH hB hm

end

end ArtGallery.Orthogonal.Hard
