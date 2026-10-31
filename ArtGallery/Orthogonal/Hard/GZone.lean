module

public import ArtGallery.Orthogonal.Hard.CombRegion

/-!
# Zones around a feature

A grid zone (`Zone`) around a feature hanging from the floor of its box: the feature's vertices are
the grid points `idx`, and every boundary segment of the zone is an edge of the feature or one of
the two floor pieces joining the box corners `(L, F)`, `(R, F)` to the ends of the feature
(`src`).  The Boolean check `featOK` (evaluated by `decide` on the indices) together with
`zoneOK` gives, for every realisation by strictly increasing maps `φ`, `ψ`, the properties
`FZone.Good` required by the half-comb lemmas (`gfzone_good`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational Set Metric

/-- The two grid points of a segment are `a, b` in some order. -/
def segIsB (e : GSeg) (a b : ℕ × ℕ) : Bool := (e.1 == a && e.2 == b) || (e.1 == b && e.2 == a)

/-- The source of a boundary segment: `(0, i)`: the feature edge `i, i+1`; `(1, 0)`: the floor
piece from `(L, F)` to the first vertex; `(2, n−1)`: from `(R, F)` to the last vertex. -/
def srcOK (z : Zone) (idx : List (ℕ × ℕ)) (e : GSeg) : ℕ × ℕ → Bool
  | (0, i) => decide (i + 1 < idx.length) && segIsB e (idx.getD i (0, 0)) (idx.getD (i + 1) (0, 0))
  | (1, j) => j == 0 && segIsB e (z.L, z.F) (idx.getD 0 (0, 0))
  | (2, j) => j + 1 == idx.length && segIsB e (z.R, z.F) (idx.getD j (0, 0))
  | _ => false

/-- **The feature check** of a zone around the feature with grid vertices `idx`, and the sources
`src` of its boundary segments. -/
def featOK (z : Zone) (idx src : List (ℕ × ℕ)) : Bool :=
  decide (2 ≤ idx.length) && idx.all (fun p => decide (p.1 < z.NX ∧ p.2 < z.NY)) &&
  (idx.getD 0 (0, 0)).2 == z.F && (idx.getD (idx.length - 1) (0, 0)).2 == z.F &&
  decide (z.L < (idx.getD 0 (0, 0)).1 ∧
    (idx.getD 0 (0, 0)).1 < (idx.getD (idx.length - 1) (0, 0)).1 ∧
    (idx.getD (idx.length - 1) (0, 0)).1 < z.R) &&
  src.length == z.pedges.length &&
  (List.range z.pedges.length).all (fun e =>
    srcOK z idx (z.pedges.getD e ((0, 0), (0, 0))) (src.getD e (3, 0))) &&
  (List.range (idx.length - 1)).all (fun i => decide ((0, i) ∈ src)) &&
  decide ((1, 0) ∈ src) && decide ((2, idx.length - 1) ∈ src)

/-- The facts of `featOK`. -/
structure FeatFacts (z : Zone) (idx src : List (ℕ × ℕ)) : Prop where
  len : 2 ≤ idx.length
  bd : ∀ p ∈ idx, p.1 < z.NX ∧ p.2 < z.NY
  fF : (idx.getD 0 (0, 0)).2 = z.F
  lF : (idx.getD (idx.length - 1) (0, 0)).2 = z.F
  ord : z.L < (idx.getD 0 (0, 0)).1 ∧
    (idx.getD 0 (0, 0)).1 < (idx.getD (idx.length - 1) (0, 0)).1 ∧
    (idx.getD (idx.length - 1) (0, 0)).1 < z.R
  slen : src.length = z.pedges.length
  srcs : ∀ e < z.pedges.length,
    srcOK z idx (z.pedges.getD e ((0, 0), (0, 0))) (src.getD e (3, 0)) = true
  edges : ∀ i < idx.length - 1, (0, i) ∈ src
  first : (1, 0) ∈ src
  last : (2, idx.length - 1) ∈ src

theorem featFacts {z : Zone} {idx src : List (ℕ × ℕ)} (h : featOK z idx src = true) :
    FeatFacts z idx src := by
  simp only [featOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ### Chains as unions of edges -/

theorem mem_edgeSeg_of_chainSet : ∀ {l : List Point} {p : Point}, p ∈ chainSet l →
    ∃ i, i + 1 < l.length ∧ p ∈ edgeSeg l i
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: l, p, h => by
    rw [chainSet_cons_cons] at h
    rcases h with h | h
    · exact ⟨0, by simp, by rw [edgeSeg_cons_cons_zero]; exact h⟩
    · obtain ⟨i, hi, hp⟩ := mem_edgeSeg_of_chainSet h
      exact ⟨i + 1, by simp at hi ⊢; omega, by rw [edgeSeg_cons_succ]; exact hp⟩

/-! ### Realisation -/

/-- The realised rectangle. -/
def realR (φ ψ : ℕ → ℝ) (r : GRect) : Rect := (φ r.1, φ r.2.1, ψ r.2.2.1, ψ r.2.2.2)

/-- The realised zone around a feature. -/
def gFZone (φ ψ : ℕ → ℝ) (z : Zone) (idx : List (ℕ × ℕ)) : FZone :=
  ⟨idx.map (gpt φ ψ), z.rects.map (realR φ ψ), φ z.L, φ z.R⟩

section Sound

variable {z : Zone} {φ ψ : ℕ → ℝ} (hz : ZoneFacts z) (hφ : StrictMonoOn φ (Iio z.NX))
  (hψ : StrictMonoOn ψ (Iio z.NY))
include hz hφ hψ

theorem rect_facts' {g : GRect} (hg : g ∈ z.rects) :
    g.1 < z.NX ∧ g.2.1 < z.NX ∧ g.2.2.1 < z.NY ∧ g.2.2.2 < z.NY ∧ (realR φ ψ g).Pos := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have := rectOK_facts (hz.rect k hk)
  rw [List.getD_eq_getElem _ _ hk] at this
  obtain ⟨hr1, hr2, hr3, hr4, -⟩ := this
  exact ⟨by omega, hr3, by omega, hr4, hφ (by simp only [mem_Iio]; omega) hr3 hr1,
    hψ (by simp only [mem_Iio]; omega) hr4 hr2⟩

theorem zoneUnion_eq : zoneUnion φ ψ z = RU (z.rects.map (realR φ ψ)) := by
  have e : zonePieces φ ψ z = (z.rects.map (realR φ ψ)).map Rect.poly := by
    simp only [zonePieces, List.map_map]; rfl
  rw [zoneUnion, e, pieceUnion_rects]
  intro r hr
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
  exact (rect_facts' hz hφ hψ hg).2.2.2.2

omit hz hφ hψ in
theorem quadIn_of_quadCov {y : Point} {sx sy : Bool} (h : QuadCov φ ψ z y sx sy) :
    QuadIn (RU (z.rects.map (realR φ ψ))) y sx sy := by
  obtain ⟨r, hr, -, -, hx, hy⟩ := h
  exact (quadIn_rect (r := realR φ ψ r) hx hy).mono (RU_mono' (List.mem_map_of_mem hr))

omit hz hφ hψ in
theorem gseg_of_segIsB {e : GSeg} {a b : ℕ × ℕ} (h : segIsB e a b = true) {y : Point}
    (hy : y ∈ gseg φ ψ e) : y ∈ ArtGallery.segment (gpt φ ψ a) (gpt φ ψ b) := by
  simp only [segIsB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [gseg, h1, h2] at hy; exact hy
  · rw [gseg, h1, h2, Geometry.segment_comm] at hy; exact hy

omit hz hφ hψ in
theorem segIsB_gseg {e : GSeg} {a b : ℕ × ℕ} (h : segIsB e a b = true) {y : Point}
    (hy : y ∈ ArtGallery.segment (gpt φ ψ a) (gpt φ ψ b)) : y ∈ gseg φ ψ e := by
  simp only [segIsB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [gseg, h1, h2]; exact hy
  · rw [gseg, h1, h2, Geometry.segment_comm]; exact hy

omit hz hφ hψ in
theorem mem_src {src : List (ℕ × ℕ)} {c : ℕ × ℕ} (h : c ∈ src) :
    ∃ e < src.length, src.getD e (3, 0) = c := by
  obtain ⟨e, he, rfl⟩ := List.getElem_of_mem h
  exact ⟨e, he, List.getD_eq_getElem _ _ he⟩

omit hz hφ hψ in
theorem fstPt_map_gpt {idx : List (ℕ × ℕ)} (h : idx ≠ []) :
    fstPt (idx.map (gpt φ ψ)) = gpt φ ψ (idx.getD 0 (0, 0)) := by
  cases idx with
  | nil => exact absurd rfl h
  | cons p l => simp [fstPt]

omit hz hφ hψ in
theorem lstPt_map_gpt {idx : List (ℕ × ℕ)} (h : idx ≠ []) :
    lstPt (idx.map (gpt φ ψ)) = gpt φ ψ (idx.getD (idx.length - 1) (0, 0)) := by
  simp only [lstPt, List.getLastD_eq_getLast?, List.getLast?_map, List.getLast?_eq_getLast h,
    Option.map_some, Option.getD_some]
  congr 1
  rw [List.getLast_eq_getElem, List.getD_eq_getElem _ _ (by
    have : idx.length ≠ 0 := by simpa using h
    omega)]

/-- **Zones around features are good.** -/
theorem gfzone_good {idx src : List (ℕ × ℕ)} (hf : FeatFacts z idx src) :
    (gFZone φ ψ z idx).Good (ψ z.F) (ψ z.T) := by
  have hlen := hf.len
  have hne : idx ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  have hidx : ∀ i < idx.length, (idx.getD i (0, 0)).1 < z.NX ∧ (idx.getD i (0, 0)).2 < z.NY :=
    fun i hi => hf.bd _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  have ha' := hidx 0 (by omega)
  have hb' := hidx (idx.length - 1) (by omega)
  obtain ⟨o1, o2, o3⟩ := hf.ord
  have hfst : fstPt (gFZone φ ψ z idx).f = gpt φ ψ (idx.getD 0 (0, 0)) := fstPt_map_gpt hne
  have hlst : lstPt (gFZone φ ψ z idx).f = gpt φ ψ (idx.getD (idx.length - 1) (0, 0)) :=
    lstPt_map_gpt hne
  have hL : z.L < z.NX := hz.box.1
  have hR : z.R < z.NX := hz.box.2.1
  have mx : ∀ {i j : ℕ}, i < z.NX → j < z.NX → i < j → φ i < φ j := fun hi hj hij =>
    hφ (by simp only [mem_Iio]; exact hi) (by simp only [mem_Iio]; exact hj) hij
  have m1 := mx hL ha'.1 o1
  have m2 := mx ha'.1 hb'.1 o2
  have m3 := mx hb'.1 hR o3
  have hUeq := zoneUnion_eq hz hφ hψ
  have hrs : (gFZone φ ψ z idx).rs = z.rects.map (realR φ ψ) := rfl
  -- the boundary segments with a given source
  have hsrc : ∀ c ∈ src, ∃ e < z.pedges.length,
      srcOK z idx (z.pedges.getD e ((0, 0), (0, 0))) c = true := by
    intro c hc
    obtain ⟨e, he, hec⟩ := mem_src hc
    rw [hf.slen] at he
    exact ⟨e, he, hec ▸ hf.srcs e he⟩
  -- the floor pieces
  have floorL : ∀ x, φ z.L ≤ x → x ≤ φ (idx.getD 0 (0, 0)).1 →
      ((x, ψ z.F) : Point) ∈ RU (z.rects.map (realR φ ψ)) := by
    intro x h1 h2
    obtain ⟨e, he, hs⟩ := hsrc _ hf.first
    simp only [srcOK, Bool.and_eq_true, beq_iff_eq] at hs
    rw [← hUeq]
    refine zone_cover hz hφ hψ he (segIsB_gseg hs.2 ?_)
    simp only [gpt]
    rw [hf.fF]
    exact mem_segment_horiz (by rw [min_eq_left m1.le]; exact h1) (by rw [max_eq_right m1.le]; exact h2)
  have floorR : ∀ x, φ (idx.getD (idx.length - 1) (0, 0)).1 ≤ x → x ≤ φ z.R →
      ((x, ψ z.F) : Point) ∈ RU (z.rects.map (realR φ ψ)) := by
    intro x h1 h2
    obtain ⟨e, he, hs⟩ := hsrc _ hf.last
    simp only [srcOK, Bool.and_eq_true, beq_iff_eq] at hs
    rw [← hUeq]
    refine zone_cover hz hφ hψ he (segIsB_gseg hs.2 ?_)
    simp only [gpt]
    rw [hf.lF]
    exact mem_segment_horiz (by rw [min_eq_right m3.le]; exact h1) (by rw [max_eq_left m3.le]; exact h2)
  -- the edges of the feature
  have hedge : ∀ i, i + 1 < idx.length → edgeSeg (gFZone φ ψ z idx).f i =
      ArtGallery.segment (gpt φ ψ (idx.getD i (0, 0))) (gpt φ ψ (idx.getD (i + 1) (0, 0))) := by
    intro i hi
    simp only [gFZone, edgeSeg]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
      List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp
  refine ⟨by simpa [gFZone] using hlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfst]; show ψ (idx.getD 0 (0, 0)).2 = ψ z.F; rw [hf.fF]
  · rw [hlst]; show ψ (idx.getD (idx.length - 1) (0, 0)).2 = ψ z.F; rw [hf.lF]
  · rw [hfst]; exact m1
  · rw [hfst, hlst]; exact m2
  · rw [hlst]; exact m3
  · intro r hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
    exact (rect_facts' hz hφ hψ hg).2.2.2.2
  · intro r hr p hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
    refine zone_in_box hz hφ hψ (K := grect φ ψ g) (List.mem_map_of_mem hg) p ?_
    rw [show grect φ ψ g = (realR φ ψ g).poly from rfl,
      Rect.piece_poly (rect_facts' hz hφ hψ hg).2.2.2.2]
    exact hp
  · intro p hp
    obtain ⟨i, hi, hp⟩ := mem_edgeSeg_of_chainSet hp
    have hi' : i + 1 < idx.length := by simpa [gFZone] using hi
    rw [hedge i hi'] at hp
    obtain ⟨e, he, hs⟩ := hsrc _ (hf.edges i (by omega))
    simp only [srcOK, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hrs, ← hUeq]
    exact zone_cover hz hφ hψ he (segIsB_gseg hs.2 hp)
  · intro x h1 h2
    rw [hfst] at h2
    exact floorL x h1 h2
  · intro x h1 h2
    rw [hlst] at h1
    exact floorR x h1 h2
  · intro r hr y hy
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
    obtain ⟨j, hj, hyj⟩ := hy
    rw [hfst, hlst, hrs, ← hUeq]
    show _ ∨ (y.2 = ψ z.F ∧ φ z.L ≤ y.1 ∧ y.1 ≤ φ (idx.getD 0 (0, 0)).1) ∨
      (y.2 = ψ z.F ∧ φ (idx.getD (idx.length - 1) (0, 0)).1 ≤ y.1 ∧ y.1 ≤ φ z.R) ∨
      y ∈ interior (zoneUnion φ ψ z) ∨ (y.2 = ψ z.T ∧ φ z.L ≤ y.1 ∧ y.1 ≤ φ z.R) ∨
      ((y.1 = φ z.L ∨ y.1 = φ z.R) ∧ ψ z.F ≤ y.2 ∧ y.2 ≤ ψ z.T)
    have hs := zone_side hz hφ hψ (K := grect φ ψ g) (List.mem_map_of_mem hg)
      (j := j) (by simpa [grect, rectP_n] using hj) hyj
    rcases hs with ⟨e, he, hye⟩ | hs | hs | hs
    · have hsr := hf.srcs e he
      generalize src.getD e (3, 0) = c at hsr
      obtain ⟨c1, c2⟩ := c
      rcases c1 with _ | _ | _ | c1
      · simp only [srcOK, Bool.and_eq_true, decide_eq_true_eq] at hsr
        left
        have := gseg_of_segIsB hsr.2 hye
        rw [← hedge c2 hsr.1] at this
        exact edgeSeg_subset (by simpa [gFZone] using hsr.1) this
      · simp only [srcOK, Bool.and_eq_true, beq_iff_eq] at hsr
        right; left
        have := gseg_of_segIsB hsr.2 hye
        simp only [gpt] at this
        rw [hf.fF] at this
        have e1 := seg_fst_ge this; have e2 := seg_fst_le this
        have e3 := seg_snd_ge this; have e4 := seg_snd_le this
        simp only [min_self, max_self, min_eq_left m1.le, max_eq_right m1.le] at e1 e2 e3 e4
        exact ⟨le_antisymm e4 e3, e1, e2⟩
      · simp only [srcOK, Bool.and_eq_true, beq_iff_eq] at hsr
        obtain ⟨hc2, hsr⟩ := hsr
        have hc2' : c2 = idx.length - 1 := by omega
        rw [hc2'] at hsr
        right; right; left
        have := gseg_of_segIsB hsr hye
        simp only [gpt] at this
        rw [hf.lF] at this
        have e1 := seg_fst_ge this; have e2 := seg_fst_le this
        have e3 := seg_snd_ge this; have e4 := seg_snd_le this
        simp only [min_self, max_self, min_eq_right m3.le, max_eq_left m3.le] at e1 e2 e3 e4
        exact ⟨le_antisymm e4 e3, e1, e2⟩
      · simp [srcOK] at hsr
    · right; right; right; left; exact hs
    · right; right; right; right; left; exact hs
    · right; right; right; right; right; exact hs
  · intro x h1 h2
    have ht := zone_tiles hz hφ hψ z.topTiles z.L hz.tiles hL x h1 h2
    exact ⟨fun h => quadIn_of_quadCov (ht.1 h),
      fun h => quadIn_of_quadCov (ht.2 h)⟩
  · intro t h1 h2
    have ht := zone_left hz hφ hψ h1 h2
    exact ⟨quadIn_of_quadCov ht.1, fun h => quadIn_of_quadCov (ht.2 h)⟩
  · intro t h1 h2
    have ht := zone_right hz hφ hψ h1 h2
    exact ⟨quadIn_of_quadCov ht.1, fun h => quadIn_of_quadCov (ht.2 h)⟩

end Sound

end

end ArtGallery.Orthogonal.Hard
