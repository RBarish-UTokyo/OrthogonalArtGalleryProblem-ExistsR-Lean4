module

public import ArtGallery.Orthogonal.Hard.CovGroup

/-!
# Using a group coverage certificate

`GroupCov.sound'`: every point of a region rectangle of a group is covered by an item of the
certificate, unless the rectangle is not covered entirely (covering kind `≠ 0`) and the point lies
in the strips `−1 ≤ y ≤ 2H` (covered globally).  `GroupCov.patchB` checks that every region
rectangle meeting a window `(a, b) × (−∞, −1/2)` of the floor strip is covered entirely.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade Set

/-- The covering kind of the region rectangle `i`. -/
def GroupCov.kind (c : GroupCov) (i : ℕ) : ℕ := (c.trees.getD i (3, .leaf 0)).1

/-- **An item of a valid certificate covering a point of a clipped region rectangle.** -/
theorem GroupCov.item_of_clip {c : GroupCov} (h : c.ok = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {S : Set Point} (hgood : ∀ R ∈ c.frame.good ++ c.frame.strips, (R.real ox H).set ⊆ S)
    (hhall : (c.frame.hall.real ox H).set ⊆ S) {i : ℕ} (hi : i < c.frame.good.length) {z : Point}
    (hzr : ∃ r, clipLR (c.frame.good[i]) (c.kind i) = some r ∧ z ∈ (r.real ox H).set) :
    ∃ k < c.items.length, z ∈ (c.items.getD k CItem.dflt).set ox H ∧
      (c.items.getD k CItem.dflt).set ox H ⊆ S ∧
      ∀ p ∈ c.rngs.getD k [], p.real ox H ∈ (c.items.getD k CItem.dflt).set ox H := by
  simp only [GroupCov.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hfr, hlen⟩, htl⟩, hit⟩, hrng⟩, htr⟩ := h
  have hRi : c.frame.good.getD i LR.dflt0 = c.frame.good[i] := List.getD_eq_getElem _ _ hi
  have ht := idxAll_sound htr hi
  simp only [GroupCov.treeIB, hRi, Bool.and_eq_true] at ht
  obtain ⟨_, htree⟩ := ht
  obtain ⟨r, hr, hzr⟩ := hzr
  simp only [GroupCov.kind] at hr
  rw [hr] at htree
  obtain ⟨k, hk, hzk⟩ := treeB_sound hH ox _ r htree z hzr
  have hk' : k < c.items.length := by simpa using hk
  rw [getD_map_allLines hk'] at hzk
  refine ⟨k, hk', (CItem.mem_set_iff ox H _ z).2 hzk, ?_, fun p hp => ?_⟩
  · have hitk := idxAll_sound hit hk'
    simp only [GroupCov.itemB, Bool.and_eq_true, List.all_eq_true] at hitk
    obtain ⟨⟨hin, hbox⟩, hoff⟩ := hitk
    have hsub := CItem.subset_good (it := c.items.getD k CItem.dflt) hin hH ox (F := c.frame.F)
      (by simp only [Bool.and_eq_true]; exact hbox)
      (good := (c.frame.hall.real ox H) :: (c.frame.good ++ c.frame.strips).map (LR.real ox H))
      (forb := c.frame.forb)
      (fun z hz => by
        rcases GCovC.cover hfr hH ox hz with h | ⟨R', hR', hzR'⟩ | h
        · exact Or.inl ⟨_, List.mem_cons_self, h⟩
        · exact Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨R', hR', rfl⟩), hzR'⟩
        · exact Or.inr h)
      (List.all_eq_true.2 hoff)
    intro w hw
    obtain ⟨A, ⟨R', hR', rfl⟩, hwA⟩ := hsub hw
    rcases List.mem_cons.1 hR' with rfl | hR'
    · exact hhall hwA
    · obtain ⟨R'', hR'', rfl⟩ := List.mem_map.1 hR'
      exact hgood R'' hR'' hwA
  · have := List.all_eq_true.1 (idxAll_sound hrng hk') p hp
    exact (CItem.mem_set_iff ox H _ _).2 (inLinesB_sound this hH ox)

/-- **Soundness of a group coverage certificate, all points.**  A point of a region rectangle of
the group lies in an item (contained in `S`, containing the range points of its guard), or the
rectangle is not covered entirely and the point lies in the strips `−1 ≤ y ≤ 2H`. -/
theorem GroupCov.sound' {c : GroupCov} (h : c.ok = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {S : Set Point} (hgood : ∀ R ∈ c.frame.good ++ c.frame.strips, (R.real ox H).set ⊆ S)
    (hhall : (c.frame.hall.real ox H).set ⊆ S) {i : ℕ} (hi : i < c.frame.good.length) {z : Point}
    (hz : z ∈ ((c.frame.good[i]).real ox H).set) :
    (∃ k < c.items.length, z ∈ (c.items.getD k CItem.dflt).set ox H ∧
      (c.items.getD k CItem.dflt).set ox H ⊆ S ∧
      ∀ p ∈ c.rngs.getD k [], p.real ox H ∈ (c.items.getD k CItem.dflt).set ox H) ∨
    (c.kind i ≠ 0 ∧ -1 ≤ z.2 ∧ z.2 ≤ 2 * H) := by
  have hok := h
  simp only [GroupCov.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, htr⟩ := hok
  have hRi : c.frame.good.getD i LR.dflt0 = c.frame.good[i] := List.getD_eq_getElem _ _ hi
  have ht := idxAll_sound htr hi
  simp only [GroupCov.treeIB, hRi, Bool.and_eq_true] at ht
  have hcond : clipCondB (c.frame.good[i]) (c.kind i) = true := ht.1
  obtain ⟨z1, z2, z3, z4⟩ := hz
  simp only [LR.real] at z1 z2 z3 z4
  have item : ∀ r, clipLR (c.frame.good[i]) (c.kind i) = some r → z ∈ (r.real ox H).set →
      (∃ k < c.items.length, z ∈ (c.items.getD k CItem.dflt).set ox H ∧
        (c.items.getD k CItem.dflt).set ox H ⊆ S ∧
        ∀ p ∈ c.rngs.getD k [], p.real ox H ∈ (c.items.getD k CItem.dflt).set ox H) :=
    fun r hr hzr => GroupCov.item_of_clip h hH ox hgood hhall hi ⟨r, hr, hzr⟩
  obtain ⟨k, hk⟩ : ∃ k, c.kind i = k := ⟨_, rfl⟩
  rw [hk] at hcond item ⊢
  match k, hcond with
  | 0, _ => exact Or.inl (item _ rfl ⟨z1, z2, z3, z4⟩)
  | 1, hc =>
    have := AH.le_sound hc hH
    simp only [AH.ev] at this z4
    push_cast at this
    by_cases hy : z.2 ≤ -1
    · refine Or.inl (item _ rfl ⟨z1, z2, z3, ?_⟩); simp only [LR.real, AH.ev]; push_cast; linarith
    · exact Or.inr ⟨by norm_num, by linarith, by linarith⟩
  | 2, hc =>
    have := AH.le_sound hc hH
    simp only [AH.ev] at this z3
    push_cast at this
    by_cases hy : 2 * H ≤ z.2
    · refine Or.inl (item _ rfl ⟨z1, z2, ?_, z4⟩); simp only [LR.real, AH.ev]; push_cast; linarith
    · exact Or.inr ⟨by norm_num, by linarith, by linarith⟩
  | 3, hc =>
    simp only [clipCondB, Bool.and_eq_true] at hc
    have h1 := AH.le_sound hc.1 hH
    have h2 := AH.le_sound hc.2 hH
    simp only [AH.ev] at h1 h2 z3 z4
    push_cast at h1 h2
    exact Or.inr ⟨by norm_num, by linarith, by linarith⟩
  | n + 4, hc => simp [clipCondB] at hc

/-- Every region rectangle meeting the window `(a, b) × (−∞, −1/2)` is covered entirely. -/
def GroupCov.patchB (c : GroupCov) (a b : ℚ) : Bool :=
  idxAll (fun i => let R := c.frame.good.getD i LR.dflt0
    c.kind i == 0 || decide (R.x1 ≤ a) || decide (b ≤ R.x0) || AH.le (-1 / 2, 0) R.y0)
    0 c.frame.good.length

theorem GroupCov.patch_kind {c : GroupCov} {a b : ℚ} (h : c.patchB a b = true) {H : ℝ}
    (hH : 1000 ≤ H) (ox : ℝ) {i : ℕ} (hi : i < c.frame.good.length) {z : Point}
    (hz : z ∈ ((c.frame.good[i]).real ox H).set) (h1 : ox + a < z.1) (h2 : z.1 < ox + b)
    (h3 : z.2 < -1 / 2) : c.kind i = 0 := by
  have hp := idxAll_sound h hi
  have hRi : c.frame.good.getD i LR.dflt0 = c.frame.good[i] := List.getD_eq_getElem _ _ hi
  simp only [hRi, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨z1, z2, z3, z4⟩ := hz
  simp only [LR.real] at z1 z2 z3 z4
  rcases hp with ((hp | hp) | hp) | hp
  · exact hp
  · exfalso
    have : ((c.frame.good[i]).x1 : ℝ) ≤ a := by exact_mod_cast hp
    linarith
  · exfalso
    have : (b : ℝ) ≤ (c.frame.good[i]).x0 := by exact_mod_cast hp
    linarith
  · exfalso
    have := AH.le_sound hp hH
    simp only [AH.ev] at this z3
    push_cast at this
    linarith

end

end ArtGallery.Orthogonal.Hard
