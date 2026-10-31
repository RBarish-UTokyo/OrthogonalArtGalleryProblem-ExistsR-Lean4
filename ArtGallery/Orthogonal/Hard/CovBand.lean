module

public import ArtGallery.Orthogonal.Hard.CovStrip
public import ArtGallery.Orthogonal.Hard.NookCov

/-!
# The strips of the zones

In the strip rows of a zone (`−1 ≤ y ≤ −1/4` for the floor, `2H − 1/4 ≤ y ≤ 2H` for the
ceiling) every grid cell is a region cell, except the cells of the floor block of the
`invRevLe` slot (inside `[31, 59] × [−1, −1/2]` in the frame of the slot) and the notch below a
copy nook (checked by `decide` on the zone data).  Hence a point of a floor strip lies in the
region or in the block window of an `invRevLe` slot (`floor_band`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade Set

/-! ### Grid cells -/

/-- Index containment of a cell in a grid rectangle. -/
def cellInZ (i j : ℕ) (r : GRect) : Bool := decide (r.1 ≤ i ∧ i < r.2.1 ∧ r.2.2.1 ≤ j ∧ j < r.2.2.2)

/-- The cells of `[i₀, i₁) × [j₀, j₁)` not covered by the rectangles. -/
def gapsOf (rs : List GRect) (i0 i1 j0 j1 : ℕ) : List (ℕ × ℕ) :=
  (List.range' i0 (i1 - i0)).flatMap fun i => (List.range' j0 (j1 - j0)).filterMap fun j =>
    if rs.any (cellInZ i j) then none else some (i, j)

/-- The cell `(i, j)` as a grid rectangle. -/
def cellR (c : ℕ × ℕ) : GRect := (c.1, c.1 + 1, c.2, c.2 + 1)

/-- **A point of a grid box lies in a rectangle or in a gap cell.** -/
theorem grid_cells {φ ψ : ℕ → ℝ} {NX NY : ℕ} (hφ : StrictMonoOn φ (Iio NX))
    (hψ : StrictMonoOn ψ (Iio NY)) {rs : List GRect} (hrs : ∀ r ∈ rs, r.2.1 < NX ∧ r.2.2.2 < NY)
    {i0 i1 j0 j1 : ℕ} (hi : i0 < i1) (hi1 : i1 < NX) (hj : j0 < j1) (hj1 : j1 < NY) {p : Point}
    (h1 : φ i0 ≤ p.1) (h2 : p.1 ≤ φ i1) (h3 : ψ j0 ≤ p.2) (h4 : p.2 ≤ ψ j1) :
    (∃ r ∈ rs, p ∈ (realR φ ψ r).set) ∨
      ∃ c ∈ gapsOf rs i0 i1 j0 j1, p ∈ (realR φ ψ (cellR c)).set := by
  have mφ : ∀ a c, a ≤ c → c < NX → φ a ≤ φ c := fun a c hac hc =>
    (hφ.le_iff_le (show a ∈ Iio NX from lt_of_le_of_lt hac hc) hc).2 hac
  have mψ : ∀ a c, a ≤ c → c < NY → ψ a ≤ ψ c := fun a c hac hc =>
    (hψ.le_iff_le (show a ∈ Iio NY from lt_of_le_of_lt hac hc) hc).2 hac
  have ex : i0 + (i1 - i0 - 1) + 1 = i1 := by omega
  have ey : j0 + (j1 - j0 - 1) + 1 = j1 := by omega
  obtain ⟨i, hi1', hi2', hxi, hxi'⟩ := nexists_step (f := φ) (i1 - i0 - 1) i0 h1 (by rw [ex]; exact h2)
  obtain ⟨j, hj1', hj2', hyj, hyj'⟩ := nexists_step (f := ψ) (j1 - j0 - 1) j0 h3 (by rw [ey]; exact h4)
  by_cases hc : rs.any (cellInZ i j) = true
  · left
    obtain ⟨r, hr, hri⟩ := List.any_eq_true.1 hc
    simp only [cellInZ, decide_eq_true_eq] at hri
    obtain ⟨r1, r2, r3, r4⟩ := hri
    obtain ⟨w1, w2⟩ := hrs r hr
    refine ⟨r, hr, ?_, ?_, ?_, ?_⟩ <;> simp only [realR]
    · exact (mφ _ _ r1 (by omega)).trans hxi
    · exact hxi'.trans (mφ _ _ r2 w1)
    · exact (mψ _ _ r3 (by omega)).trans hyj
    · exact hyj'.trans (mψ _ _ r4 w2)
  · right
    refine ⟨(i, j), ?_, hxi, hxi', hyj, hyj'⟩
    simp only [gapsOf, List.mem_flatMap, List.mem_filterMap, List.mem_range'_1]
    refine ⟨i, ⟨hi1', by omega⟩, j, ⟨hj1', by omega⟩, ?_⟩
    simp only [Bool.not_eq_true] at hc
    simp [hc]

/-! ### The strips of the templates -/

/-- The strip rows of a template zone and its index bounds. -/
def zoneStripB (zt : TZone) : Bool :=
  decide (zt.zone.L < zt.zone.R ∧ zt.zone.R < zt.zone.NX ∧ zt.zone.F < zt.zone.T ∧
    zt.zone.T < zt.zone.NY) &&
  zt.zone.rects.all (fun r => decide (r.2.1 < zt.zone.NX ∧ r.2.2.2 < zt.zone.NY))

/-- The strip gaps of a template zone. -/
def tGaps (zt : TZone) : List (ℕ × ℕ) := gapsOf zt.zone.rects zt.zone.L zt.zone.R zt.zone.F zt.zone.T

/-- The gap cells lie in `[a, b] × (−∞, −1/2]` (template frame, `H ≥ 1000`). -/
def gapWinB (t : ITmpl) (zt : TZone) (a b : ℚ) : Bool :=
  (tGaps zt).all fun c =>
    decide (a ≤ (zt.xs.getD c.1 0 : ℚ) / t.D ∧ (zt.xs.getD (c.1 + 1) 0 : ℚ) / t.D ≤ b ∧
      0 ≤ (zt.ys.getD (c.2 + 1) (0, 0)).2 ∧
      2 * ((zt.ys.getD (c.2 + 1) (0, 0)).1 - (zt.ys.getD (c.2 + 1) (0, 0)).2 * 1000) ≤ -(t.D : ℤ))

theorem floor_strip_tmpls :
    allFloorTmpls.all (fun t => zoneStripB (fz t)) = true ∧
    (oBasin :: oVarFloor).all (fun t => tGaps (fz t) = []) = true ∧
    (oSlotFloor .invGe ++ oSlotFloor .addLe ++ oSlotFloor .addGe).all
      (fun t => tGaps (fz t) = []) = true ∧
    (oSlotFloor .invRevLe).all (fun t => gapWinB t (fz t) 31 59) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem ceil_strip_tmpls :
    allCeilTmpls.all (fun t => zoneStripB (cz t) && (tGaps (cz t)).isEmpty) = true := by
  decide +kernel


/-! ### Floor zones -/

variable {n : ℕ} {Φ : List Constraint}

/-- A point of the strip rows of a floor template zone lies in a rectangle of the zone or in a
gap cell. -/
theorem fzone_strip {t : ITmpl} (ht : t ∈ allFloorTmpls) {H ox : ℚ} (hH : 1000 ≤ H) {p : Point}
    (h1 : (fzone t H ox).L ≤ p.1) (h2 : p.1 ≤ (fzone t H ox).R) (h3 : -1 ≤ p.2)
    (h4 : p.2 ≤ -1 / 4) :
    (∃ r ∈ (fzone t H ox).rs, p ∈ r.set) ∨
      ∃ c ∈ tGaps (fz t), p ∈ (realR (tzX t (fz t) ox) (tzY t (fz t) H) (cellR c)).set := by
  have hf := fz_facts ht
  have hD := floorTmpl_D ht
  have hs := List.all_eq_true.1 floor_strip_tmpls.1 t ht
  simp only [zoneStripB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
  obtain ⟨⟨hLR, hRN, hFT, hTN⟩, hrs⟩ := hs
  have hH' : (1000 : ℝ) ≤ H := by exact_mod_cast hH
  have eF := tz_F hf hD (H : ℝ)
  have eT := tz_T hf hD (H : ℝ)
  simp only [Bool.false_eq_true, ↓reduceIte] at eF eT
  rcases grid_cells (tz_monoX hf hD ox) (tz_monoY hf hD hH') hrs hLR hRN hFT hTN h1 h2
    (by rw [eF]; exact h3) (by rw [eT]; exact h4) with ⟨r, hr, hpr⟩ | ⟨c, hc, hpc⟩
  · exact Or.inl ⟨_, List.mem_map.2 ⟨r, hr, rfl⟩, hpr⟩
  · exact Or.inr ⟨c, hc, hpc⟩

/-- The strip window of a gap cell of an `invRevLe` floor template. -/
theorem invRevLe_gap {t : ITmpl} (ht : t ∈ oSlotFloor .invRevLe) {H ox : ℚ} (hH : 1000 ≤ H)
    {c : ℕ × ℕ} (hc : c ∈ tGaps (fz t)) {p : Point}
    (hp : p ∈ (realR (tzX t (fz t) ox) (tzY t (fz t) H) (cellR c)).set) :
    (ox : ℝ) + 31 ≤ p.1 ∧ p.1 ≤ ox + 59 ∧ p.2 ≤ -1 / 2 := by
  have hD := floorTmpl_D (mem_allFloorTmpls_slot ht)
  have hw := List.all_eq_true.1 (List.all_eq_true.1 floor_strip_tmpls.2.2.2 t ht) c hc
  simp only [decide_eq_true_eq] at hw
  obtain ⟨w1, w2, w3, w4⟩ := hw
  obtain ⟨p1, p2, -, p4⟩ := hp
  simp only [realR, cellR, tzX, tzY] at p1 p2 p4
  have hD' : (0 : ℝ) < t.D := by exact_mod_cast hD
  have hH' : (1000 : ℝ) ≤ H := by exact_mod_cast hH
  refine ⟨?_, ?_, ?_⟩
  · have : ((31 : ℚ) : ℝ) ≤ (((fz t).xs.getD c.1 0 : ℚ) / t.D : ℚ) := by exact_mod_cast w1
    push_cast at this; linarith
  · have : ((((fz t).xs.getD (c.1 + 1) 0 : ℚ) / t.D : ℚ) : ℝ) ≤ ((59 : ℚ) : ℝ) := by exact_mod_cast w2
    push_cast at this; linarith
  · set y0 := ((fz t).ys.getD (c.2 + 1) (0, 0)).1
    set d := ((fz t).ys.getD (c.2 + 1) (0, 0)).2
    have e3 : (0 : ℝ) ≤ d := by exact_mod_cast w3
    have e4 : 2 * ((y0 : ℝ) - d * 1000) ≤ -(t.D : ℝ) := by exact_mod_cast w4
    have : ((y0 : ℝ) - d * H) / t.D ≤ -1 / 2 := by
      rw [div_le_iff₀ hD']; nlinarith
    linarith

/-- **The strip rows of a floor zone**: a point lies in the region or in the block window of an
`invRevLe` slot. -/
theorem floor_zone_strip {Z : FZone} (hZ : Z ∈ zfO n Φ) {p : Point} (h1 : Z.L ≤ p.1)
    (h2 : p.1 ≤ Z.R) (h3 : -1 ≤ p.2) (h4 : p.2 ≤ -1 / 4) :
    p ∈ PO n Φ ∨ ∃ c < paramC Φ, cKind (gadAt Φ c) = .invRevLe ∧
      (slotG n Φ c : ℝ) + 31 ≤ p.1 ∧ p.1 ≤ (slotG n Φ c : ℝ) + 59 ∧ p.2 ≤ -1 / 2 := by
  have hH := paramH_ge_q n Φ
  have reg : ∀ r ∈ Z.rs, p ∈ r.set → p ∈ PO n Φ := fun r hr hp =>
    mem_filled_of_region (zone_rect_floor hZ hr) hp
  have noGap : ∀ {t : ITmpl} {ox : ℚ}, t ∈ allFloorTmpls → Z = fzone t (paramH n Φ) ox →
      tGaps (fz t) = [] → p ∈ PO n Φ := by
    intro t ox ht hZt hg
    subst hZt
    rcases fzone_strip ht hH h1 h2 h3 h4 with ⟨r, hr, hp⟩ | ⟨c, hc, -⟩
    · exact reg r hr hp
    · rw [hg] at hc; simp at hc
  have h2' := floor_strip_tmpls.2
  simp only [List.all_eq_true, decide_eq_true_eq] at h2'
  obtain ⟨hb, hs, -⟩ := h2'
  simp only [zfO, List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_range,
    List.mem_map] at hZ
  rcases hZ with (rfl | ⟨k, -, t, ht, rfl⟩) | ⟨c, hc, t, ht, rfl⟩
  · exact Or.inl (noGap List.mem_cons_self rfl (hb _ List.mem_cons_self))
  · exact Or.inl (noGap (mem_allFloorTmpls_var ht) rfl (hb _ (List.mem_cons_of_mem _ ht)))
  · have hta := mem_allFloorTmpls_slot ht
    generalize hk : cKind (gadAt Φ c) = k at ht
    cases k with
    | invRevLe =>
      rcases fzone_strip hta hH h1 h2 h3 h4 with ⟨r, hr, hp⟩ | ⟨g, hg, hp⟩
      · exact Or.inl (reg r hr hp)
      · obtain ⟨w1, w2, w3⟩ := invRevLe_gap ht hH hg hp
        exact Or.inr ⟨c, hc, hk, by exact_mod_cast w1, by exact_mod_cast w2, w3⟩
    | invGe => exact Or.inl (noGap hta rfl (hs t (by simp [ht])))
    | addLe => exact Or.inl (noGap hta rfl (hs t (by simp [ht])))
    | addGe => exact Or.inl (noGap hta rfl (hs t (by simp [ht])))

/-- **The floor strip**: a point of `[x_L, x_R] × [−1, −1/4]` lies in the region or in the block
window of an `invRevLe` slot. -/
theorem floor_band {p : Point} (h1 : (xL n Φ : ℝ) ≤ p.1) (h2 : p.1 ≤ xR n Φ) (h3 : -1 ≤ p.2)
    (h4 : p.2 ≤ -1 / 4) :
    p ∈ PO n Φ ∨ ∃ c < paramC Φ, cKind (gadAt Φ c) = .invRevLe ∧
      (slotG n Φ c : ℝ) + 31 ≤ p.1 ∧ p.1 ≤ (slotG n Φ c : ℝ) + 59 ∧ p.2 ≤ -1 / 2 := by
  by_cases hZ : ∀ Z ∈ zfO n Φ, p.1 ≤ Z.L ∨ Z.R ≤ p.1
  · exact Or.inl (floor_strip_filled h1 h2 h3 h4 hZ)
  · push Not at hZ
    obtain ⟨Z, hZ, hl, hr⟩ := hZ
    exact floor_zone_strip hZ hl.le hr.le h3 h4


/-! ### Ceiling zones -/

/-- The strip gaps of the copy-nook zone (real grid) are notch cells. -/
theorem nook_strip_gaps : (gapsOf cnRR 0 19 0 3).all
    (fun c => decide (7 ≤ c.1 ∧ c.1 + 1 ≤ 16 ∧ 1 ≤ c.2)) = true := by decide +kernel

theorem cnRR_lt : ∀ r ∈ cnRR, r.2.1 < 20 ∧ r.2.2.2 < 19 := by decide

/-- A point of the strip rows of a ceiling template zone (mirrored) lies in the region. -/
theorem czone_strip {t : ITmpl} (ht : t ∈ allCeilTmpls) {H b : ℚ} (hH : 1000 ≤ H) {q : Point}
    (h1 : (czone t H b).L ≤ q.1) (h2 : q.1 ≤ (czone t H b).R) (h3 : -(2 * (H : ℝ)) ≤ q.2)
    (h4 : q.2 ≤ -(2 * (H : ℝ)) + 1 / 4) : ∃ r ∈ (czone t H b).rs, q ∈ r.set := by
  have hf := cz_facts ht
  have hD : 0 < t.D := by
    have := ceilTmpl_D ht; exact this
  have hs := List.all_eq_true.1 ceil_strip_tmpls t ht
  simp only [zoneStripB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.isEmpty_iff] at hs
  obtain ⟨⟨⟨hLR, hRN, hFT, hTN⟩, hrs⟩, hg⟩ := hs
  have hH' : (1000 : ℝ) ≤ H := by exact_mod_cast hH
  have eF := tz_F hf hD (H : ℝ)
  have eT := tz_T hf hD (H : ℝ)
  simp only [↓reduceIte] at eF eT
  rcases grid_cells (tz_monoX hf hD (-(b : ℝ))) (tz_monoY hf hD hH') hrs hLR hRN hFT hTN
    (p := q) (by simpa [czone, tzFZone, gFZone] using h1) (by simpa [czone, tzFZone, gFZone] using h2)
    (by rw [eF]; linarith) (by rw [eT]; linarith) with ⟨r, hr, hpr⟩ | ⟨c, hc, -⟩
  · refine ⟨_, ?_, hpr⟩
    simp only [czone, tzFZone, gFZone]
    exact List.mem_map.2 ⟨r, hr, rfl⟩
  · simp only [tGaps] at hg; rw [hg] at hc; simp at hc

theorem nook_phi0 {a b H : ℚ} (ge : Bool) :
    nookφ a b ge H 0 = -(nzone a b ge H).R := by
  rw [nookφ_eq ge (by norm_num), nzone, cn_R, neg_neg]; simp [cnXe]

theorem nook_phi19 {a b H : ℚ} (ge : Bool) :
    nookφ a b ge H 19 = -(nzone a b ge H).L := by
  rw [nookφ_eq ge (by norm_num), nzone, cn_L, neg_neg]; simp [cnXe, cnXs]

theorem nook_psi0 {a b H : ℚ} (ge : Bool) : nookψ a b ge H 0 = 2 * (H : ℝ) - 1 / 4 := by
  rw [nookψ_eq ge (by norm_num)]; simp [cnYe]

theorem nook_psi3 {a b H : ℚ} (ge : Bool) : nookψ a b ge H 3 = 2 * (H : ℝ) := by
  rw [nookψ_eq ge (by norm_num)]; simp [cnYe, cnYs]

/-- **The strip rows of a ceiling zone**: a point lies in the region or in the notch window of a
copy nook. -/
theorem ceil_zone_strip {Z : FZone} (hZ : Z ∈ zcO n Φ) {p : Point}
    (h1 : -Z.R ≤ p.1) (h2 : p.1 ≤ -Z.L) (h3 : 2 * Hr n Φ - 1 / 4 ≤ p.2) (h4 : p.2 ≤ 2 * Hr n Φ) :
    p ∈ PO n Φ ∨ ∃ i ∈ inputsO n Φ,
      iφ Φ (paramH n Φ) i.var i 7 ≤ p.1 ∧ p.1 ≤ iφ Φ (paramH n Φ) i.var i 16 ∧
      iψ Φ (paramH n Φ) i.var i 1 ≤ p.2 := by
  have hH := paramH_ge_q n Φ
  have creg : ∀ {t : ITmpl} {b : ℚ}, t ∈ allCeilTmpls → Z = czone t (paramH n Φ) b →
      p ∈ PO n Φ := by
    intro t b ht hZt
    subst hZt
    obtain ⟨r, hr, hq⟩ := czone_strip ht (b := b) hH (q := -p) (by simp only [Prod.fst_neg]; linarith)
      (by simp only [Prod.fst_neg]; linarith) (by simp only [Prod.snd_neg, Hr] at h4 ⊢; linarith)
      (by simp only [Prod.snd_neg, Hr] at h3 ⊢; linarith)
    exact mem_filled_of_region (zone_rect_ceil hZ hr) (Rect.mem_neg.2 hq)
  simp only [zcO, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_reverse,
    List.mem_range, List.mem_filter, beq_iff_eq] at hZ
  rcases hZ with (⟨i, hi, t, ht, rfl⟩ | ⟨k, hk, t, ht, rfl⟩) | ⟨k, hk, i, ⟨hi, hik⟩, rfl⟩
  · exact Or.inl (creg (mem_allCeilTmpls_input ht) rfl)
  · exact Or.inl (creg (mem_allCeilTmpls_var ht) rfl)
  · have hZ' : nzone (varA Φ k) i.b i.ge (paramH n Φ) ∈ zcO n Φ := nzone_mem hk hi hik
    obtain ⟨d1, d2⟩ := inputO_delta hi hk
    have hφ := nookφ_mono hH d1 d2 i.ge
    have hψ := nookψ_mono hH d1 d2 i.ge
    rw [← nook_phi0 i.ge] at h1
    rw [← nook_phi19 i.ge] at h2
    rcases grid_cells hφ hψ cnRR_lt (by norm_num : 0 < 19) (by norm_num) (by norm_num : 0 < 3)
      (by norm_num) h1 h2 (by rw [nook_psi0]; simpa [Hr] using h3)
      (by rw [nook_psi3]; simpa [Hr] using h4) with ⟨r, hr, hp⟩ | ⟨c, hc, hp⟩
    · left
      have hm : realR (nookφ (varA Φ k) i.b i.ge (paramH n Φ)) (nookψ (varA Φ k) i.b i.ge (paramH n Φ)) r
          ∈ (nzone (varA Φ k) i.b i.ge (paramH n Φ)).rs.map Rect.neg := by
        rw [nzone_rs]; exact List.mem_map.2 ⟨r, hr, rfl⟩
      obtain ⟨r', hr', he⟩ := List.mem_map.1 hm
      rw [← he] at hp
      exact mem_filled_of_region (zone_rect_ceil hZ' hr') hp
    · right
      have hw := List.all_eq_true.1 nook_strip_gaps c hc
      simp only [decide_eq_true_eq] at hw
      obtain ⟨w1, w2, w3⟩ := hw
      obtain ⟨p1, p2, p3, -⟩ := hp
      simp only [realR, cellR] at p1 p2 p3
      have mφ : ∀ a c, a ≤ c → c < 20 → nookφ (varA Φ k) i.b i.ge (paramH n Φ) a ≤
          nookφ (varA Φ k) i.b i.ge (paramH n Φ) c := fun a c hac hc =>
        (hφ.le_iff_le (show a ∈ Iio 20 from lt_of_le_of_lt hac hc) hc).2 hac
      have mψ : ∀ a c, a ≤ c → c < 19 → nookψ (varA Φ k) i.b i.ge (paramH n Φ) a ≤
          nookψ (varA Φ k) i.b i.ge (paramH n Φ) c := fun a c hac hc =>
        (hψ.le_iff_le (show a ∈ Iio 19 from lt_of_le_of_lt hac hc) hc).2 hac
      have hc3 : c.2 < 3 := by
        simp only [gapsOf, List.mem_flatMap, List.mem_filterMap, List.mem_range'_1] at hc
        obtain ⟨i', -, j', hj', h⟩ := hc
        split_ifs at h; cases h; simp only; omega
      refine ⟨i, hi, ?_, ?_, ?_⟩ <;> rw [hik]
      · exact (mφ _ _ w1 (by omega)).trans p1
      · exact p2.trans (mφ _ _ w2 (by norm_num))
      · exact (mψ _ _ w3 (by omega)).trans p3


/-- **The ceiling strip**: a point of `[x_L, x_R] × [2H − 1/4, 2H]` lies in the region or in the
notch window of a copy nook. -/
theorem ceil_band {p : Point} (h1 : (xL n Φ : ℝ) ≤ p.1) (h2 : p.1 ≤ xR n Φ)
    (h3 : 2 * Hr n Φ - 1 / 4 ≤ p.2) (h4 : p.2 ≤ 2 * Hr n Φ) :
    p ∈ PO n Φ ∨ ∃ i ∈ inputsO n Φ,
      iφ Φ (paramH n Φ) i.var i 7 ≤ p.1 ∧ p.1 ≤ iφ Φ (paramH n Φ) i.var i 16 ∧
      iψ Φ (paramH n Φ) i.var i 1 ≤ p.2 := by
  by_cases hZ : ∀ Z ∈ zcO n Φ, -p.1 ≤ Z.L ∨ Z.R ≤ -p.1
  · exact Or.inl (ceil_strip_filled h1 h2 h3 h4 hZ)
  · push Not at hZ
    obtain ⟨Z, hZ, hl, hr⟩ := hZ
    exact ceil_zone_strip hZ (by linarith) (by linarith) h3 h4

end

end ArtGallery.Orthogonal.Hard
