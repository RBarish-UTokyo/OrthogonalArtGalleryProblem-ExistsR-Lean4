module

public import ArtGallery.Orthogonal.Hard.CanonAddO
public import ArtGallery.Orthogonal.Hard.CovSeen
public import ArtGallery.Stade.GuardTools

/-!
# Completeness: generic tools for the canonical guards

Rectangles in convex sets, the sample values of the aux points, and `groupCov_canon`: a group
coverage certificate whose items with a range contain the range of a witness gives, for each
point of the group, a canonical guard seeing it (or a pocket item, or a strip).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### The canonical guards lie in the hulls of their ranges -/

/-- A rectangle lies in every convex set containing its corners. -/
theorem rect_subset_convex {S : Set Point} (hS : Convex ℝ S) {x0 x1 y0 y1 : ℝ}
    (h00 : (x0, y0) ∈ S) (h10 : (x1, y0) ∈ S) (h01 : (x0, y1) ∈ S) (h11 : (x1, y1) ∈ S)
    {p : Point} (hx0 : x0 ≤ p.1) (hx1 : p.1 ≤ x1) (hy0 : y0 ≤ p.2) (hy1 : p.2 ≤ y1) : p ∈ S := by
  have seg : ∀ a b : Point, a ∈ S → b ∈ S → ArtGallery.segment a b ⊆ S := fun a b ha hb => by
    rw [segment_eq]; exact hS.segment_subset ha hb
  have hb : ((p.1, y0) : Point) ∈ S :=
    seg _ _ h00 h10 ((mem_segment_horiz_iff (le_trans hx0 hx1)).2 ⟨rfl, hx0, hx1⟩)
  have ht : ((p.1, y1) : Point) ∈ S :=
    seg _ _ h01 h11 ((mem_segment_horiz_iff (le_trans hx0 hx1)).2 ⟨rfl, hx0, hx1⟩)
  exact seg _ _ hb ht ((mem_segment_vert_iff (le_trans hy0 hy1)).2 ⟨rfl, hy0, hy1⟩)

/-- The real corners of an `LR` in a convex set. -/
theorem LR.corners_real_mem {S : Set Point} {r : LR} {ox H : ℝ}
    (h : ∀ p ∈ r.corners, p.real ox H ∈ S) :
    ((ox + r.x0 : ℝ), r.y0.ev H) ∈ S ∧ ((ox + r.x1 : ℝ), r.y0.ev H) ∈ S ∧
      ((ox + r.x0 : ℝ), r.y1.ev H) ∈ S ∧ ((ox + r.x1 : ℝ), r.y1.ev H) ∈ S := by
  simp only [LR.corners, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- **A rectangle of an `LR` in every convex set containing its corners.** -/
theorem LR.real_subset_convex {S : Set Point} (hS : Convex ℝ S) {r : LR} {ox H : ℝ}
    (h : ∀ p ∈ r.corners, p.real ox H ∈ S) : ((r.real ox H).set) ⊆ S := by
  obtain ⟨h00, h10, h01, h11⟩ := LR.corners_real_mem h
  intro p hp
  simp only [LR.real, Rect.set, mem_ofPred_eq] at hp
  exact rect_subset_convex hS h00 h10 h01 h11 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

/-! ### Sample values of the aux points -/

theorem alOI_s00 (G : ℝ) : alOI G (1 / 2) (1 / 2) = (G + 16990 / 71, -3942 / 71) := by
  unfold alOI alOs alOSx alOSy; ext <;> norm_num <;> ring

theorem alOI_s10 (G : ℝ) : alOI G (3 / 2) (1 / 2) = (G + 10114 / 41, -2106 / 41) := by
  unfold alOI alOs alOSx alOSy; ext <;> norm_num <;> ring

theorem alOI_s01 (G : ℝ) : alOI G (1 / 2) (3 / 2) = (G + 51770 / 229, -13410 / 229) := by
  unfold alOI alOs alOSx alOSy; ext <;> norm_num <;> ring

theorem agOI_s00 (G : ℝ) : agOI G (1 / 2) (1 / 2) = (G + 131550 / 1607, -50139 / 1607) := by
  unfold agOI agOs agOSx agOSy; ext <;> norm_num <;> ring

theorem agOI_s02 (G : ℝ) : agOI G (1 / 2) 2 = (G + 26790 / 331, -10383 / 331) := by
  unfold agOI agOs agOSx agOSy; ext <;> norm_num <;> ring

theorem agOI_s20 (G : ℝ) : agOI G 2 (1 / 2) = (G + 130350 / 1583, -48291 / 1583) := by
  unfold agOI agOs agOSx agOSy; ext <;> norm_num <;> ring

theorem agOI_s22 (G : ℝ) : agOI G 2 2 = (G + 132750 / 1631, -50067 / 1631) := by
  unfold agOI agOs agOSx agOSy; ext <;> norm_num <;> ring

/-! ### Items seen by a canonical guard -/

/-- The first witness `< m` whose range lies in `rng`. -/
def findW (R : ℕ → List LP) (m : ℕ) (rng : List LP) : Option ℕ :=
  (List.range m).find? fun i => (R i).all (· ∈ rng)

/-- Every item of the certificate with a nonempty range contains the range of a witness. -/
def guardB (R : ℕ → List LP) (m : ℕ) (c : GroupCov) : Bool :=
  (List.range c.items.length).all fun k =>
    (c.rngs.getD k []).isEmpty || (findW R m (c.rngs.getD k [])).isSome

theorem guardB_sound {R : ℕ → List LP} {m : ℕ} {c : GroupCov} (h : guardB R m c = true) {k : ℕ}
    (hk : k < c.items.length) (hne : c.rngs.getD k [] ≠ []) :
    ∃ i < m, ∀ p ∈ R i, p ∈ c.rngs.getD k [] := by
  have := List.all_eq_true.1 h k (List.mem_range.2 hk)
  simp only [Bool.or_eq_true, List.isEmpty_iff] at this
  rcases this with h1 | h1
  · exact absurd h1 hne
  · obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 h1
    have hm := List.find?_some hi
    have hmem := List.mem_of_find?_eq_some hi
    simp only [List.all_eq_true, decide_eq_true_eq] at hm
    exact ⟨i, List.mem_range.1 hmem, hm⟩

/-- **A group coverage certificate with canonical guards.**  A point of the region in a zone box
of the group is seen by the canonical guard of a witness, or lies in an item without range (a
pocket), or in a strip rectangle (covered globally). -/
theorem groupCov_canon {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) {c : GroupCov}
    (hok : c.ok = true) (hgood : c.frame.good = (groupLR gs).map Prod.fst)
    (hstrips : ∀ R ∈ c.frame.strips,
      (R.real ox (Hr n Φ)).set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (hhall : (c.frame.hall.real ox (Hr n Φ)).set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    {R : ℕ → List LP} {m : ℕ} (hG : guardB R m c = true) {γ : ℕ → Point}
    (hγ : ∀ i < m, ∀ S : Set Point, Convex ℝ S → (∀ p ∈ R i, p.real ox (Hr n Φ) ∈ S) → γ i ∈ S)
    {z : Point} (hz : z ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled) {g : GZ} (hg : g ∈ gs)
    (hzb : z ∈ g.box.set ox (Hr n Φ)) :
    (∃ i < m, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (γ i) z) ∨
    (∃ k < c.items.length, c.rngs.getD k [] = [] ∧ z ∈ (c.items.getD k CItem.dflt).set ox (Hr n Φ)) ∨
    (∃ i, ∃ hi : i < c.frame.good.length, z ∈ ((c.frame.good[i]).real ox (Hr n Φ)).set ∧
      c.kind i ≠ 0 ∧ -1 ≤ z.2 ∧ z.2 ≤ 2 * Hr n Φ) := by
  rcases groupCov_cover hgs hok hgood hstrips hhall hz hg hzb with ⟨k, hk, hzk, hkP, hrk⟩ | h
  · by_cases hne : c.rngs.getD k [] = []
    · exact Or.inr (Or.inl ⟨k, hk, hne, hzk⟩)
    · left
      obtain ⟨i, hi, hiR⟩ := guardB_sound hG hk hne
      have hγk := hγ i hi _ (CItem.convex _ _ _) fun p hp => hrk p (hiR p hp)
      exact ⟨i, hi, Stade.sees_of_convex (CItem.convex _ _ _) hkP hγk hzk⟩
  · exact Or.inr (Or.inr h)

/-! ### Items -/

/-- **Every item of a valid certificate lies in the region.** -/
theorem GroupCov.item_subset {c : GroupCov} (h : c.ok = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {S : Set Point} (hgood : ∀ R ∈ c.frame.good ++ c.frame.strips, (R.real ox H).set ⊆ S)
    (hhall : (c.frame.hall.real ox H).set ⊆ S) {k : ℕ} (hk : k < c.items.length) :
    (c.items.getD k CItem.dflt).set ox H ⊆ S := by
  simp only [GroupCov.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hfr, -⟩, -⟩, hit⟩, -⟩, -⟩ := h
  have hitk := idxAll_sound hit hk
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

/-- A point of the item's lines (with `inLinesB` on all its lines) lies in the item. -/
theorem CItem.mem_of_inLinesB {it : CItem} {p : LP} (h : inLinesB it.allLines p = true) {H : ℝ}
    (hH : 1000 ≤ H) (ox : ℝ) : p.real ox H ∈ it.set ox H :=
  (CItem.mem_set_iff ox H _ _).2 (inLinesB_sound h hH ox)

/-- **Mouth items**: a guard in an item containing both ends of a mouth sees the mouth. -/
theorem CItem.sees_mouth {P : Polygon} {it : CItem} {ox H : ℝ} (hS : it.set ox H ⊆ P.filled)
    {γ : Point} (hγ : γ ∈ it.set ox H) {a b : Point} (ha : a ∈ it.set ox H)
    (hb : b ∈ it.set ox H) : ∀ m ∈ ArtGallery.segment a b, P.Sees γ m := by
  intro m hm
  have hm' : m ∈ it.set ox H := by
    rw [segment_eq] at hm; exact (CItem.convex ox H it).segment_subset ha hb hm
  exact Stade.sees_of_convex (CItem.convex _ _ _) hS hγ hm'

/-- **Pocket items**: a point of an item whose lines contain the four sides of a quadrilateral
lies in the quadrilateral. -/
theorem CItem.mem_quad {it : CItem} {ox H : ℝ} {lo dn up hi : LP} (h1 : (lo, dn) ∈ it.lines)
    (h2 : (dn, up) ∈ it.lines) (h3 : (up, hi) ∈ it.lines) (h4 : (hi, lo) ∈ it.lines) {z : Point}
    (hz : z ∈ it.set ox H) :
    z ∈ piece (quad (lo.real ox H) (dn.real ox H) (up.real ox H) (hi.real ox H)) := by
  have hl := hz.1
  exact mem_piece_quad.2 ⟨hl _ h1, hl _ h2, hl _ h3, hl _ h4⟩

/-- A strictly convex counter-clockwise quadrilateral with its vertices in a convex set lies in
it. -/
theorem quad_subset_convex {S : Set Point} (hS : Convex ℝ S) {lo dn up hi : Point}
    (h1 : 0 < det lo dn up) (h2 : 0 < det dn up hi) (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn)
    (hlo : lo ∈ S) (hdn : dn ∈ S) (hup : up ∈ S) (hhi : hi ∈ S) : piece (quad lo dn up hi) ⊆ S := by
  intro z hz
  obtain ⟨s, hs, m, hm, hzm⟩ := quad_fan h1 h2 h3 h4 hz
  have seg : ∀ a b : Point, a ∈ S → b ∈ S → ArtGallery.segment a b ⊆ S := fun a b ha hb => by
    rw [segment_eq]; exact hS.segment_subset ha hb
  exact seg _ _ (seg _ _ hlo hhi hs) (seg _ _ hdn hup hm) hzm

/-! ### Group certificates from a zone rectangle -/

/-- **A group coverage certificate in the polygon, from a rectangle of a group zone.** -/
theorem groupCov_cover_rect {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox)
    {c : GroupCov} (hok : c.ok = true) (hgood : c.frame.good = (groupLR gs).map Prod.fst)
    (hstrips : ∀ R ∈ c.frame.strips,
      (R.real ox (Hr n Φ)).set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (hhall : (c.frame.hall.real ox (Hr n Φ)).set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    {g : GZ} (hg : g ∈ gs) {l : LR} (hl : l ∈ g.rects) {z : Point}
    (hz : z ∈ (l.real ox (Hr n Φ)).set) :
    (∃ k < c.items.length, z ∈ (c.items.getD k CItem.dflt).set ox (Hr n Φ) ∧
      (c.items.getD k CItem.dflt).set ox (Hr n Φ) ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled ∧
      ∀ p ∈ c.rngs.getD k [], p.real ox (Hr n Φ) ∈ (c.items.getD k CItem.dflt).set ox (Hr n Φ)) ∨
    (∃ i, ∃ hi : i < c.frame.good.length, z ∈ ((c.frame.good[i]).real ox (Hr n Φ)).set ∧
      c.kind i ≠ 0 ∧ -1 ≤ z.2 ∧ z.2 ≤ 2 * Hr n Φ) := by
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
  rw [← hil] at hz
  rcases GroupCov.sound' hok (Hr_ge n Φ) ox hS hhall hi hz with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hi, hz, h1, h2, h3⟩

/-- **Canonical guards from a zone rectangle**: seen by a canonical guard, or in an item without
range, or in the band with a nonzero kind. -/
theorem groupCov_canon_rect {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox)
    {c : GroupCov} (hok : c.ok = true) (hgood : c.frame.good = (groupLR gs).map Prod.fst)
    (hstrips : ∀ R ∈ c.frame.strips,
      (R.real ox (Hr n Φ)).set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (hhall : (c.frame.hall.real ox (Hr n Φ)).set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    {R : ℕ → List LP} {m : ℕ} (hG : guardB R m c = true) {γ : ℕ → Point}
    (hγ : ∀ i < m, ∀ S : Set Point, Convex ℝ S → (∀ p ∈ R i, p.real ox (Hr n Φ) ∈ S) → γ i ∈ S)
    {g : GZ} (hg : g ∈ gs) {l : LR} (hl : l ∈ g.rects) {z : Point}
    (hz : z ∈ (l.real ox (Hr n Φ)).set) :
    (∃ i < m, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (γ i) z) ∨
    (∃ k < c.items.length, c.rngs.getD k [] = [] ∧ z ∈ (c.items.getD k CItem.dflt).set ox (Hr n Φ)) ∨
    (∃ i, ∃ hi : i < c.frame.good.length, z ∈ ((c.frame.good[i]).real ox (Hr n Φ)).set ∧
      c.kind i ≠ 0 ∧ -1 ≤ z.2 ∧ z.2 ≤ 2 * Hr n Φ) := by
  rcases groupCov_cover_rect hgs hok hgood hstrips hhall hg hl hz with ⟨k, hk, hzk, hkP, hrk⟩ | h
  · by_cases hne : c.rngs.getD k [] = []
    · exact Or.inr (Or.inl ⟨k, hk, hne, hzk⟩)
    · left
      obtain ⟨i, hi, hiR⟩ := guardB_sound hG hk hne
      have hγk := hγ i hi _ (CItem.convex _ _ _) fun p hp => hrk p (hiR p hp)
      exact ⟨i, hi, Stade.sees_of_convex (CItem.convex _ _ _) hkP hγk hzk⟩
  · exact Or.inr (Or.inr h)

end

end ArtGallery.Orthogonal.Hard
