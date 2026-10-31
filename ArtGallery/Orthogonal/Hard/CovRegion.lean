module

public import ArtGallery.Orthogonal.Hard.CovSeen

/-!
# Completeness: where the points of the region are

Every point of the region lies in a rectangle of a floor zone, in a (mirrored) rectangle of a
ceiling zone, or in the band `[−1, 2H]` outside the open spans of the zones of its strip.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

/-- A rectangle of `hcRects` is a zone rectangle or a gap rectangle of the strip. -/
theorem hcRects_cases {y₀ T e : ℝ} :
    ∀ {zs : List FZone} {s : ℝ} {r : Rect}, r ∈ hcRects y₀ T s zs e →
      (∃ Z ∈ zs, r ∈ Z.rs) ∨ (r.2.2.1 = y₀ ∧ r.2.2.2 = T)
  | [], s, r, h => by
    simp only [hcRects, List.mem_singleton] at h
    subst h; exact Or.inr ⟨rfl, rfl⟩
  | Z :: zs, s, r, h => by
    simp only [hcRects, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨Z, List.mem_cons_self, h⟩
    · rcases hcRects_cases h with ⟨Z', hZ', hr⟩ | h
      · exact Or.inl ⟨Z', List.mem_cons_of_mem _ hZ', hr⟩
      · exact Or.inr h

/-- **The places of the region.** -/
theorem region_cases {z : Point} (hz : z ∈ PO n Φ) :
    (∃ Z ∈ zfO n Φ, ∃ r ∈ Z.rs, z ∈ r.set) ∨
    (∃ Z ∈ zcO n Φ, ∃ r ∈ Z.rs, z ∈ r.neg.set) ∨
    (-1 ≤ z.2 ∧ z.2 ≤ 2 * Hr n Φ ∧
      (z.2 < -1 / 4 → ∀ Z ∈ zfO n Φ, ¬(Z.L < z.1 ∧ z.1 < Z.R)) ∧
      (2 * Hr n Φ - 1 / 4 < z.2 → ∀ Z ∈ zcO n Φ, ¬(-Z.R < z.1 ∧ z.1 < -Z.L))) := by
  have hH := Hr_ge' (n := n) (Φ := Φ)
  -- a point inside the open span of a zone of its strip is in a rectangle of the zone
  by_cases hf : z.2 < -1 / 4 ∧ ∃ Z ∈ zfO n Φ, Z.L < z.1 ∧ z.1 < Z.R
  · obtain ⟨hy, Z, hZ, h1, h2⟩ := hf
    have hz' := hz
    rw [PO, filledO] at hz'
    obtain ⟨r, hr, hzr⟩ := hz'
    rcases region_rect_floor hZ r hr with h | h
    · exact Or.inl ⟨Z, hZ, r, h, hzr⟩
    · exact absurd ⟨h1, h2, hy⟩ (h z hzr)
  by_cases hc : 2 * Hr n Φ - 1 / 4 < z.2 ∧ ∃ Z ∈ zcO n Φ, -Z.R < z.1 ∧ z.1 < -Z.L
  · obtain ⟨hy, Z, hZ, h1, h2⟩ := hc
    have hz' := hz
    rw [PO, filledO] at hz'
    obtain ⟨r, hr, hzr⟩ := hz'
    rcases region_rect_ceil hZ r hr with h | h
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 h
      exact Or.inr (Or.inl ⟨Z, hZ, r', hr', hzr⟩)
    · exact absurd ⟨h1, h2, hy⟩ (h z hzr)
  have hf' : z.2 < -1 / 4 → ∀ Z ∈ zfO n Φ, ¬(Z.L < z.1 ∧ z.1 < Z.R) :=
    fun hy Z hZ h => hf ⟨hy, Z, hZ, h⟩
  have hc' : 2 * Hr n Φ - 1 / 4 < z.2 → ∀ Z ∈ zcO n Φ, ¬(-Z.R < z.1 ∧ z.1 < -Z.L) :=
    fun hy Z hZ h => hc ⟨hy, Z, hZ, h⟩
  have hz' := hz
  rw [PO, filledO] at hz'
  obtain ⟨r, hr, hzr⟩ := hz'
  simp only [regionRectsO, combRects, List.mem_cons, List.mem_append] at hr
  rcases hr with rfl | hr | hr
  · -- the hall
    obtain ⟨-, -, h3, h4⟩ := hzr
    exact Or.inr (Or.inr ⟨by linarith, by simp only [Hr] at h4 ⊢; linarith, hf', hc'⟩)
  · rcases hcRects_cases hr with ⟨Z, hZ, hrZ⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨Z, hZ, r, hrZ, hzr⟩
    · obtain ⟨-, -, h3, h4⟩ := hzr
      rw [e1] at h3; rw [e2] at h4
      exact Or.inr (Or.inr ⟨h3, by linarith, hf', hc'⟩)
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    rcases hcRects_cases hr' with ⟨Z, hZ, hrZ⟩ | ⟨e1, e2⟩
    · exact Or.inr (Or.inl ⟨Z, hZ, r', hrZ, hzr⟩)
    · obtain ⟨-, -, h3, h4⟩ := hzr
      simp only [Rect.neg] at h3 h4
      rw [e1] at h4; rw [e2] at h3
      simp only [Hr] at h3 h4 ⊢
      exact Or.inr (Or.inr ⟨by linarith, by linarith, hf', hc'⟩)

/-! ### Zones and groups -/

/-- **The floor zones**: the basin zone, the floor zones of the variables, the floor zones of the
slots. -/
theorem zfO_cases {Z : FZone} (hZ : Z ∈ zfO n Φ) :
    (∃ g ∈ basinZ, g.ceil = false ∧ Z = fzone g.t (paramH n Φ) ((xL n Φ : ℚ) + g.δ)) ∨
    (∃ k < n, ∃ g ∈ varZ, g.ceil = false ∧ Z = fzone g.t (paramH n Φ) ((varA Φ k : ℚ) + g.δ)) ∨
    (∃ c : Fin (paramC Φ), ∃ g ∈ slotZ (cKind (gadAt Φ c)), g.ceil = false ∧
      Z = fzone g.t (paramH n Φ) ((slotG n Φ c : ℚ) + g.δ)) := by
  simp only [zfO, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_range, List.mem_map] at hZ
  rcases hZ with (rfl | ⟨k, hk, t, ht, rfl⟩) | ⟨c, hc, t, ht, rfl⟩
  · exact Or.inl ⟨_, List.mem_singleton_self _, rfl, by simp⟩
  · refine Or.inr (Or.inl ⟨k, hk, ⟨t, false, 0⟩, ?_, rfl, by simp⟩)
    simp only [varZ, List.mem_append, List.mem_map]
    exact Or.inr ⟨t, ht, rfl⟩
  · refine Or.inr (Or.inr ⟨⟨c, hc⟩, ⟨t, false, 0⟩, ?_, rfl, by simp⟩)
    simp only [slotZ, List.mem_append, List.mem_map]
    exact Or.inl ⟨t, ht, rfl⟩

/-- **The ceiling zones**: the ceiling zones of the inputs (in the groups of their slots) and of
the variables, and the copy nooks. -/
theorem zcO_cases {Z : FZone} (hZ : Z ∈ zcO n Φ) :
    (∃ c : Fin (paramC Φ), ∃ g ∈ slotZ (cKind (gadAt Φ c)), g.ceil = true ∧
      Z = czone g.t (paramH n Φ) ((slotG n Φ c : ℚ) + g.δ)) ∨
    (∃ k < n, ∃ g ∈ varZ, g.ceil = true ∧ Z = czone g.t (paramH n Φ) ((varA Φ k : ℚ) + g.δ)) ∨
    (∃ i ∈ inputsO n Φ, Z = nzone (varA Φ i.var) i.b i.ge (paramH n Φ)) := by
  simp only [zcO, List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range,
    List.mem_map, List.mem_filter, beq_iff_eq] at hZ
  rcases hZ with (⟨i, hi, t, ht, rfl⟩ | ⟨k, hk, t, ht, rfl⟩) | ⟨k, hk, i, ⟨hi, hik⟩, rfl⟩
  · simp only [inputsO, slotInputsO, List.mem_flatMap, List.mem_range, List.mem_map] at hi
    obtain ⟨c, hc, inp, hinp, rfl⟩ := hi
    refine Or.inl ⟨⟨c, hc⟩, ⟨t, true, inp.lx⟩, ?_, rfl, rfl⟩
    simp only [slotZ, List.mem_append, List.mem_flatMap, List.mem_map]
    exact Or.inr ⟨inp, hinp, t, ht, rfl⟩
  · refine Or.inr (Or.inl ⟨k, hk, ⟨t, true, 0⟩, ?_, rfl, by simp⟩)
    simp only [varZ, List.mem_append, List.mem_map]
    exact Or.inl ⟨t, ht, rfl⟩
  · exact Or.inr (Or.inr ⟨i, hi, by rw [hik]⟩)

/-- A rectangle of the floor zone of a group zone is a group rectangle. -/
theorem fzone_rect_group {g : GZ} {ox : ℚ} (hc : g.ceil = false) {r : Rect}
    (hr : r ∈ (fzone g.t (paramH n Φ) (ox + g.δ)).rs) :
    ∃ l ∈ g.rects, r = l.real ox (Hr n Φ) := by
  have := GZ.rects_real (n := n) (Φ := Φ) g ox
  rw [hc] at this
  simp only [Bool.false_eq_true, ↓reduceIte] at this
  rw [← this] at hr
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
  exact ⟨l, hl, rfl⟩

/-- A (mirrored) rectangle of the ceiling zone of a group zone is a group rectangle. -/
theorem czone_rect_group {g : GZ} {ox : ℚ} (hc : g.ceil = true) {r : Rect}
    (hr : r ∈ (czone g.t (paramH n Φ) (ox + g.δ)).rs) :
    ∃ l ∈ g.rects, r.neg = l.real ox (Hr n Φ) := by
  have := GZ.rects_real (n := n) (Φ := Φ) g ox
  rw [hc] at this
  simp only [↓reduceIte] at this
  have hm : r.neg ∈ (czone g.t (paramH n Φ) (ox + g.δ)).rs.map Rect.neg := List.mem_map.2 ⟨r, hr, rfl⟩
  rw [← this] at hm
  obtain ⟨l, hl, he⟩ := List.mem_map.1 hm
  exact ⟨l, hl, he.symm⟩

/-! ### The band -/

/-- A point of the band `[−1, 2H]` outside the block windows of the `invRevLe` slots and the
notch windows of the copy nooks. -/
def BandOK (n : ℕ) (Φ : List Constraint) (z : Point) : Prop :=
  -1 ≤ z.2 ∧ z.2 ≤ 2 * Hr n Φ ∧
  (∀ c < paramC Φ, cKind (gadAt Φ c) = .invRevLe →
    ¬((slotG n Φ c : ℝ) + 31 < z.1 ∧ z.1 < (slotG n Φ c : ℝ) + 61 ∧ z.2 < -1 / 2)) ∧
  (∀ i ∈ inputsO n Φ, ¬(iφ Φ (paramH n Φ) i.var i 7 < z.1 ∧
      z.1 < iφ Φ (paramH n Φ) i.var i 16 ∧ iψ Φ (paramH n Φ) i.var i 1 < z.2))

/-- **The band is seen by the guard of variable `0` or by `H_L`.** -/
theorem band_seen (hΦ : ∀ c ∈ Φ, c.VarsLt n) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) {z : Point}
    (hz : z ∈ PO n Φ) (hb : BandOK n Φ z) :
    (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (gZero n Φ v) z ∨
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (hL n Φ) z := by
  obtain ⟨h1, h2, hW, hE⟩ := hb
  by_cases hy : z.2 ≤ 2 * Hr n Φ - 1 / 4
  · exact Or.inl (sees_g0_floor hv1 hv2 hz h1 hy hW)
  · push Not at hy
    exact sees_ceil hΦ hv1 hv2 hz hy h2 hE

/-- The first floor template of `invRevLe` spans the block window. -/
theorem invRevLe_t0 : ∃ t ∈ oSlotFloor .invRevLe, t.xmin - 1 / 8 ≤ 31 ∧ 61 ≤ t.xmax + 1 / 8 := by
  refine ⟨_, List.mem_cons_self, ?_⟩
  constructor <;> decide +kernel

/-- **The block window of an `invRevLe` slot lies in the open span of a floor zone.** -/
theorem window_span {c : ℕ} (hc : c < paramC Φ) (hk : cKind (gadAt Φ c) = .invRevLe) {z : Point}
    (h1 : (slotG n Φ c : ℝ) + 31 < z.1) (h2 : z.1 < (slotG n Φ c : ℝ) + 61) (h3 : z.2 < -1 / 4) :
    ∃ Z ∈ zfO n Φ, Z.L < z.1 ∧ z.1 < Z.R := by
  obtain ⟨t, ht, hx0, hx1⟩ := invRevLe_t0
  have hg : (⟨t, false, 0⟩ : GZ) ∈ slotZ (cKind (gadAt Φ c)) := by
    rw [hk]; simp only [slotZ, List.mem_append, List.mem_map]; exact Or.inl ⟨t, ht, rfl⟩
  have hin := slotZ_in (n := n) hc _ hg
  have hb : z ∈ (⟨t, false, 0⟩ : GZ).box.set (slotG n Φ c) (Hr n Φ) := by
    simp only [GZ.box, Bool.false_eq_true, ↓reduceIte, floorBoxL, LBox.shift, LBox.set,
      Option.map_some, Option.some.injEq, forall_eq', reduceCtorEq, false_implies, implies_true,
      true_and, and_true, mem_ofPred_eq, AH.ev]
    have e0 : ((t.xmin - 1 / 8 + 0 : ℚ) : ℝ) ≤ 31 := by exact_mod_cast (by linarith : t.xmin - 1 / 8 + 0 ≤ 31)
    have e1 : (61 : ℝ) ≤ ((t.xmax + 1 / 8 + 0 : ℚ) : ℝ) := by
      exact_mod_cast (by linarith : (61 : ℚ) ≤ t.xmax + 1 / 8 + 0)
    refine ⟨by push_cast at e0 ⊢; linarith, by push_cast at e1 ⊢; linarith, by push_cast; linarith⟩
  have := GZ.box_set hin hb
  simp only [Bool.false_eq_true, ↓reduceIte] at this
  exact ⟨_, hin.2, this.1, this.2.1⟩

/-- **The notch window of a copy nook lies in the open span of a ceiling zone.** -/
theorem notch_span (hΦ : ∀ c ∈ Φ, c.VarsLt n) {i : InputSeg} (hi : i ∈ inputsO n Φ) {z : Point}
    (h1 : iφ Φ (paramH n Φ) i.var i 7 < z.1) (h2 : z.1 < iφ Φ (paramH n Φ) i.var i 16) :
    ∃ Z ∈ zcO n Φ, -Z.R < z.1 ∧ z.1 < -Z.L := by
  have hk := inputsO_var hΦ hi
  have hH := paramH_ge_q n Φ
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  have hφ := nookφ_mono hH d1 d2 i.ge
  refine ⟨_, nzone_mem hk hi rfl, ?_, ?_⟩
  · rw [← nook_phi0 i.ge]
    exact lt_trans (hφ (by simp) (by simp : (7 : ℕ) ∈ Iio 20) (by norm_num)) h1
  · rw [← nook_phi19 i.ge]
    exact lt_trans h2 (hφ (by simp : (16 : ℕ) ∈ Iio 20) (by simp) (by norm_num))

/-- **The band case of the decomposition is a band point.** -/
theorem bandOK_of_cases (hΦ : ∀ c ∈ Φ, c.VarsLt n) {z : Point} (h1 : -1 ≤ z.2)
    (h2 : z.2 ≤ 2 * Hr n Φ) (hf : z.2 < -1 / 4 → ∀ Z ∈ zfO n Φ, ¬(Z.L < z.1 ∧ z.1 < Z.R))
    (hc : 2 * Hr n Φ - 1 / 4 < z.2 → ∀ Z ∈ zcO n Φ, ¬(-Z.R < z.1 ∧ z.1 < -Z.L)) :
    BandOK n Φ z := by
  refine ⟨h1, h2, fun c hc' hk ⟨w1, w2, w3⟩ => ?_, fun i hi ⟨e1, e2, e3⟩ => ?_⟩
  · obtain ⟨Z, hZ, l1, l2⟩ := window_span hc' hk w1 w2 (by linarith)
    exact hf (by linarith) Z hZ ⟨l1, l2⟩
  · obtain ⟨Z, hZ, l1, l2⟩ := notch_span hΦ hi e1 e2
    have := nook_window' hΦ hi
    exact hc (by linarith) Z hZ ⟨l1, l2⟩

/-! ### Separation of the groups from the windows -/

/-- No block window near a point of a variable group. -/
theorem var_noW {k : ℕ} (hk : k < n) {z : Point} (h1 : z.1 ≤ (varA Φ k : ℝ) + 4) :
    ∀ c < paramC Φ, cKind (gadAt Φ c) = .invRevLe →
      ¬((slotG n Φ c : ℝ) + 31 < z.1 ∧ z.1 < (slotG n Φ c : ℝ) + 61 ∧ z.2 < -1 / 2) := by
  rintro c - - ⟨w1, -, -⟩
  have := var_slot_sep (n := n) (Φ := Φ) (c := c) hk
  linarith

/-- No notch window near a point right of `−97`. -/
theorem right_noE (hΦ : ∀ c ∈ Φ, c.VarsLt n) {z : Point} (h1 : -97 ≤ z.1) :
    ∀ i ∈ inputsO n Φ, ¬(iφ Φ (paramH n Φ) i.var i 7 < z.1 ∧
      z.1 < iφ Φ (paramH n Φ) i.var i 16 ∧ iψ Φ (paramH n Φ) i.var i 1 < z.2) := by
  rintro i hi ⟨-, e2, -⟩
  obtain ⟨-, e16, -, e0⟩ := nook_window hΦ hi
  linarith

/-- No notch window near a point of the basin. -/
theorem basin_noE (hΦ : ∀ c ∈ Φ, c.VarsLt n) {z : Point} (h1 : z.1 ≤ (xL n Φ : ℝ) + 99) :
    ∀ i ∈ inputsO n Φ, ¬(iφ Φ (paramH n Φ) i.var i 7 < z.1 ∧
      z.1 < iφ Φ (paramH n Φ) i.var i 16 ∧ iψ Φ (paramH n Φ) i.var i 1 < z.2) := by
  rintro i hi ⟨e1, -, -⟩
  obtain ⟨e7, -, eL, -⟩ := nook_window hΦ hi
  linarith

/-- No block window near a point of the basin. -/
theorem basin_noW {z : Point} (h1 : z.1 ≤ (xL n Φ : ℝ) + 100) :
    ∀ c < paramC Φ, cKind (gadAt Φ c) = .invRevLe →
      ¬((slotG n Φ c : ℝ) + 31 < z.1 ∧ z.1 < (slotG n Φ c : ℝ) + 61 ∧ z.2 < -1 / 2) := by
  rintro c - - ⟨w1, -, -⟩
  have := xL_slot_sep (n := n) (Φ := Φ) c
  linarith

/-- Only the block window of its own slot is near a point of a slot group. -/
theorem slot_noW {c : ℕ} {z : Point} (h1 : (slotG n Φ c : ℝ) - 460 ≤ z.1)
    (h2 : z.1 ≤ (slotG n Φ c : ℝ) + 560) :
    ∀ c' < paramC Φ, c' ≠ c → cKind (gadAt Φ c') = .invRevLe →
      ¬((slotG n Φ c' : ℝ) + 31 < z.1 ∧ z.1 < (slotG n Φ c' : ℝ) + 61 ∧ z.2 < -1 / 2) := by
  rintro c' - hne - ⟨w1, w2, -⟩
  rcases lt_or_gt_of_ne hne with h | h
  · have := slotG_sep (n := n) (Φ := Φ) h; linarith
  · have := slotG_sep (n := n) (Φ := Φ) h; linarith

/-- **Assembly over the zones.**  If every point of a zone rectangle is seen by a guard of `Gs`
or is a band point, and the guard of variable `0` and `H_L` are in `Gs`, then `Gs` sees the
whole region. -/
theorem cover_of_zones (hΦ : ∀ c ∈ Φ, c.VarsLt n) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    {Gs : Set Point} (h0 : gZero n Φ v ∈ Gs) (hL0 : hL n Φ ∈ Gs)
    (hfl : ∀ Z ∈ zfO n Φ, ∀ r ∈ Z.rs, ∀ z ∈ r.set, z ∈ PO n Φ →
      (∃ g ∈ Gs, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees g z) ∨ BandOK n Φ z)
    (hce : ∀ Z ∈ zcO n Φ, ∀ r ∈ Z.rs, ∀ z ∈ r.neg.set, z ∈ PO n Φ →
      (∃ g ∈ Gs, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees g z) ∨ BandOK n Φ z) :
    ∀ z ∈ PO n Φ, ∃ g ∈ Gs, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees g z := by
  intro z hz
  have band : BandOK n Φ z → ∃ g ∈ Gs, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees g z :=
    fun hb => (band_seen hΦ hv1 hv2 hz hb).elim (fun h => ⟨_, h0, h⟩) (fun h => ⟨_, hL0, h⟩)
  rcases region_cases hz with ⟨Z, hZ, r, hr, hzr⟩ | ⟨Z, hZ, r, hr, hzr⟩ | ⟨h1, h2, hf, hc⟩
  · exact (hfl Z hZ r hr z hzr hz).elim id band
  · exact (hce Z hZ r hr z hzr hz).elim id band
  · exact band (bandOK_of_cases hΦ h1 h2 hf hc)

end

end ArtGallery.Orthogonal.Hard
