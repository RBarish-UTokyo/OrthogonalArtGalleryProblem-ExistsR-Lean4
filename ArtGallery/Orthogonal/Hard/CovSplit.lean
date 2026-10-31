module

public import ArtGallery.Orthogonal.Hard.CovGroup

/-!
# Splitting the frame check of a group coverage certificate

The zone check `FZoneC.ok` of a large zone and the frame check `GCovC.ok` exceed the memory of one
kernel declaration.  They are split into the head conditions of a zone and its columns
(`FZoneC.ok_of_parts`), and the zones and the segment conditions of a frame
(`GCovC.ok_of_parts`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

/-- The head conditions of a zone check. -/
def FZoneC.headB (zc : FZoneC) : Bool :=
  incQB zc.xs && incAHB zc.ys &&
  decide (zc.iL < zc.iR ∧ zc.iR < zc.xs.length ∧ zc.jlo < zc.jhi ∧ zc.jhi < zc.ys.length) &&
  (zc.rects ++ zc.nr).all (fun r => decide (r.2.1 < zc.xs.length ∧ r.2.2.2 < zc.ys.length))

/-- The column `i` of a zone check, as in `FZoneC.ok`. -/
def FZoneC.colB0 (zc : FZoneC) (i : ℕ) : Bool :=
  decide (i < zc.iL) ||
    (List.range zc.jhi).all fun j => decide (j < zc.jlo) || (zc.rects ++ zc.nr).any (cellInB i j)

/-- The column `i` of a zone check: the rectangles meeting the column are selected once, then
every cell of the column is looked up among them. -/
def FZoneC.colB (zc : FZoneC) (i : ℕ) : Bool :=
  decide (i < zc.iL) ||
    let rs := (zc.rects ++ zc.nr).filter fun r => decide (r.1 ≤ i ∧ i < r.2.1)
    (List.range zc.jhi).all fun j => decide (j < zc.jlo) ||
      rs.any fun r => decide (r.2.2.1 ≤ j ∧ j < r.2.2.2)

theorem FZoneC.colB0_of_colB {zc : FZoneC} {i : ℕ} (h : zc.colB i = true) : zc.colB0 i = true := by
  simp only [FZoneC.colB, FZoneC.colB0, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, List.mem_filter, cellInB] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun j hj => ?_
    rcases h j hj with h | ⟨r, ⟨hr, hri⟩, hrj⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, hri.1, hri.2, hrj.1, hrj.2⟩

theorem FZoneC.ok_of_parts {zc : FZoneC} (h0 : zc.headB = true)
    (h1 : idxAll zc.colB 0 zc.iR = true) : zc.ok = true := by
  show (zc.headB && (List.range zc.iR).all zc.colB0) = true
  rw [h0, List.range_eq_range']
  simp only [idxAll, List.all_eq_true, Nat.sub_zero] at h1
  simpa [List.all_eq_true] using fun x hx => FZoneC.colB0_of_colB (h1 x hx)

theorem idxAll_one {p : ℕ → Bool} {k : ℕ} (h : p k = true) : idxAll p k (k + 1) = true := by
  simp [idxAll, h]

/-- The segment conditions of a frame check. -/
def GCovC.segsB (g : GCovC) : Bool :=
  partB g.F.x0 g.F.x1 g.fl && partB g.F.x0 g.F.x1 g.ce && g.fl.all (g.segB true) &&
    g.ce.all (g.segB false)

theorem GCovC.ok_of_parts {g : GCovC}
    (hz : idxAll (fun k => (g.zones.getD k zoneD).ok) 0 g.zones.length = true)
    (hs : g.segsB = true) : g.ok = true := by
  have hz' : g.zones.all FZoneC.ok = true := by
    rw [List.all_eq_true]
    intro z hzm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hzm
    have := List.all_eq_true.1 hz k (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    rwa [List.getD_eq_getElem _ _ hk] at this
  unfold GCovC.segsB at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
  unfold GCovC.ok
  rw [hz', h1, h2, h3, h4]
  rfl

end

end ArtGallery.Orthogonal.Hard
