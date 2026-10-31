module

public import ArtGallery.Orthogonal.Hard.CovUse
public import ArtGallery.Orthogonal.Hard.CertGroup

/-!
# Group coverage certificates in the polygon

For a template group placed at `ox` (its zones are zones of the polygon) whose coverage frame has
the region rectangles of the group (`c.frame.good = (groupLR gs).map Prod.fst`), every point of
the region inside the box of a zone of the group lies in an item of the certificate, or in a
region rectangle not covered entirely and in the strips (`groupCov_cover`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

theorem zone_rect_floor {Z : FZone} (hZ : Z ∈ zfO n Φ) {r : Rect} (hr : r ∈ Z.rs) :
    r ∈ regionRectsO n Φ := by
  obtain ⟨A, B, hAB, -, -⟩ := hc_split zfO_good zord_zfO Z hZ
  simp only [regionRectsO, combRects, List.mem_cons, List.mem_append]
  right; left
  rw [hAB]; simp [hr]

theorem zone_rect_ceil {Z : FZone} (hZ : Z ∈ zcO n Φ) {r : Rect} (hr : r ∈ Z.rs) :
    r.neg ∈ regionRectsO n Φ := by
  obtain ⟨A, B, hAB, -, -⟩ := hc_split zcO_good zord_zcO Z hZ
  simp only [regionRectsO, combRects, List.mem_cons, List.mem_append]
  right; right
  rw [hAB]; exact List.mem_map.2 ⟨r, by simp [hr], rfl⟩

/-- The rectangles of a group zone are region rectangles. -/
theorem GZ.rect_region {g : GZ} {ox : ℚ} (hg : g.InPoly n Φ ox) {l : LR} (hl : l ∈ g.rects) :
    l.real ox (Hr n Φ) ∈ regionRectsO n Φ := by
  have hm : l.real ox (Hr n Φ) ∈ g.rects.map (LR.real ox (Hr n Φ)) := List.mem_map.2 ⟨l, hl, rfl⟩
  rw [GZ.rects_real] at hm
  unfold GZ.InPoly at hg
  cases hc : g.ceil
  · rw [hc] at hg hm; simp only [Bool.false_eq_true, ↓reduceIte] at hg hm
    exact zone_rect_floor hg.2 hm
  · rw [hc] at hg hm; simp only [↓reduceIte] at hg hm
    obtain ⟨r, hr, he⟩ := List.mem_map.1 hm
    rw [← he]; exact zone_rect_ceil hg.2 hr

theorem mem_filled_of_region {r : Rect} (hr : r ∈ regionRectsO n Φ) :
    r.set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled := by
  intro z hz; rw [filledO]; exact ⟨r, hr, hz⟩

/-- The region rectangles of a group lie in the region. -/
theorem groupLR_filled {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) {R : LR}
    (hR : R ∈ (groupLR gs).map Prod.fst) :
    (R.real ox (Hr n Φ)).set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled := by
  obtain ⟨⟨l, k⟩, hlk, rfl⟩ := List.mem_map.1 hR
  simp only [groupLR, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq] at hlk
  obtain ⟨k', hk', l', hl', rfl, rfl⟩ := hlk
  rw [List.getD_eq_getElem _ _ hk'] at hl'
  exact mem_filled_of_region (GZ.rect_region (hgs _ (List.getElem_mem hk')) hl')

/-- **A group coverage certificate in the polygon.** -/
theorem groupCov_cover {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) {c : GroupCov}
    (hok : c.ok = true) (hgood : c.frame.good = (groupLR gs).map Prod.fst)
    (hstrips : ∀ R ∈ c.frame.strips,
      (R.real ox (Hr n Φ)).set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (hhall : (c.frame.hall.real ox (Hr n Φ)).set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    {z : Point} (hz : z ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled) {g : GZ} (hg : g ∈ gs)
    (hzb : z ∈ g.box.set ox (Hr n Φ)) :
    (∃ k < c.items.length, z ∈ (c.items.getD k CItem.dflt).set ox (Hr n Φ) ∧
      (c.items.getD k CItem.dflt).set ox (Hr n Φ) ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled ∧
      ∀ p ∈ c.rngs.getD k [], p.real ox (Hr n Φ) ∈ (c.items.getD k CItem.dflt).set ox (Hr n Φ)) ∨
    (∃ i, ∃ hi : i < c.frame.good.length, z ∈ ((c.frame.good[i]).real ox (Hr n Φ)).set ∧
      c.kind i ≠ 0 ∧ -1 ≤ z.2 ∧ z.2 ≤ 2 * Hr n Φ) := by
  -- the region rectangle of `z` is a rectangle of the zone of `g`
  have hz' := hz
  rw [filledO] at hz'
  obtain ⟨r, hr, hzr⟩ := hz'
  have hb := GZ.box_set (hgs g hg) hzb
  have hrg : r ∈ g.rects.map (LR.real ox (Hr n Φ)) := by
    rw [GZ.rects_real]
    have hin := hgs g hg
    unfold GZ.InPoly at hin
    cases hcg : g.ceil
    · rw [hcg] at hin hb; simp only [Bool.false_eq_true, ↓reduceIte] at hin hb ⊢
      rcases region_rect_floor hin.2 r hr with h | h
      · exact h
      · exact absurd hb (h z hzr)
    · rw [hcg] at hin hb; simp only [↓reduceIte] at hin hb ⊢
      rcases region_rect_ceil hin.2 r hr with h | h
      · exact h
      · exact absurd hb (h z hzr)
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hrg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hlg : l ∈ c.frame.good := by
    rw [hgood]
    refine List.mem_map.2 ⟨(l, k), ?_, rfl⟩
    simp only [groupLR, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨k, hk, l, by rw [List.getD_eq_getElem _ _ hk]; exact hl, rfl⟩
  obtain ⟨i, hi, hil⟩ := List.getElem_of_mem hlg
  have hS : ∀ R ∈ c.frame.good ++ c.frame.strips,
      (R.real ox (Hr n Φ)).set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled := by
    intro R hR
    rcases List.mem_append.1 hR with hR | hR
    · rw [hgood] at hR; exact groupLR_filled hgs hR
    · exact hstrips R hR
  rw [← hil] at hzr
  rcases GroupCov.sound' hok (Hr_ge n Φ) ox hS hhall hi hzr with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hi, hzr, h1, h2, h3⟩

end

end ArtGallery.Orthogonal.Hard
