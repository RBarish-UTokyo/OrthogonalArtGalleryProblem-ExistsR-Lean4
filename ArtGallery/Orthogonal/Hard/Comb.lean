module

public import ArtGallery.Orthogonal.Hard.OrthChain

/-!
# Combs with dented features

Stade's comb lemmas (`ArtGallery/Stade/Chains.lean`) assemble a simple polygon from a rectangle
and *features* hanging below its floor and standing above its ceiling; a feature meets the line
only in its two end points.  In the orthogonal construction a copy-nook feature also dips below
the ceiling (the *notch* under its chain helper).  A *dented* feature may meet and cross its line,
but only inside its own closed x-span `[x_first, x_last]`; the gap segments of the comb lie
outside the spans, so the comb arguments go through unchanged.

* `FloorFeatureD`, `CeilFeatureD`: dented features (every ordinary feature is one:
  `FloorFeature.toD`, `CeilFeature.toD`);
* `comb_floorD`, `comb_ceilingD`, `simple_of_combsD`: the comb lemmas for dented features, where
  the floor and ceiling parts are separated by a horizontal line `y = m`;
* `oFloorDB`, `oCeilDB`: comparison-only checks for dented orthogonal features, with soundness
  over `ℝ`, invariance under monotone coordinate maps and grid versions.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade.Chain ArtGallery.Irrational Set

/-- A *dented floor feature* for the line `y = y₀` inside the strip `x_lo < x < x_hi`: a simple
chain with at least two vertices, starting and ending on the line (from left to right), meeting the
line only between its end points, and lying strictly inside the strip. -/
def FloorFeatureD (y₀ xlo xhi : ℝ) (f : List Point) : Prop :=
  2 ≤ f.length ∧ ChainSimple f ∧ (fstPt f).2 = y₀ ∧ (lstPt f).2 = y₀ ∧
    (fstPt f).1 < (lstPt f).1 ∧
    (∀ p ∈ chainSet f, p.2 = y₀ → (fstPt f).1 ≤ p.1 ∧ p.1 ≤ (lstPt f).1) ∧
    (∀ p ∈ chainSet f, xlo < p.1 ∧ p.1 < xhi)

/-- A *dented ceiling feature* for the line `y = Y` (from right to left). -/
def CeilFeatureD (Y xlo xhi : ℝ) (f : List Point) : Prop :=
  2 ≤ f.length ∧ ChainSimple f ∧ (fstPt f).2 = Y ∧ (lstPt f).2 = Y ∧
    (lstPt f).1 < (fstPt f).1 ∧
    (∀ p ∈ chainSet f, p.2 = Y → (lstPt f).1 ≤ p.1 ∧ p.1 ≤ (fstPt f).1) ∧
    (∀ p ∈ chainSet f, xlo < p.1 ∧ p.1 < xhi)

theorem FloorFeature.toD {y₀ xlo xhi : ℝ} {f : List Point} (h : FloorFeature y₀ xlo xhi f) :
    FloorFeatureD y₀ xlo xhi f := by
  obtain ⟨hlen, hcs, hfy, hly, hfl, hbel, hx⟩ := h
  refine ⟨hlen, hcs, hfy, hly, hfl, fun p hp hpy => ?_, hx⟩
  rcases hbel p hp with h | rfl | rfl
  · exact absurd hpy (ne_of_lt h)
  · exact ⟨le_rfl, hfl.le⟩
  · exact ⟨hfl.le, le_rfl⟩

theorem CeilFeature.toD {Y xlo xhi : ℝ} {f : List Point} (h : CeilFeature Y xlo xhi f) :
    CeilFeatureD Y xlo xhi f := by
  obtain ⟨hlen, hcs, hfy, hly, hfl, hab, hx⟩ := h
  refine ⟨hlen, hcs, hfy, hly, hfl, fun p hp hpy => ?_, hx⟩
  rcases hab p hp with h | rfl | rfl
  · exact absurd hpy (ne_of_gt h)
  · exact ⟨hfl.le, le_rfl⟩
  · exact ⟨le_rfl, hfl.le⟩

/-! ### The floor comb -/

/-- **Comb (floor), dented features.**  The polyline from `(s, y₀)` through the dented features
`fs` to `(x_hi, y₀)` is simple, and lies on the line `y = y₀` between `s` and `x_hi` or on the
features. -/
theorem comb_floorD {y₀ xlo xhi : ℝ} : ∀ (fs : List (List Point)) (s : ℝ), s < xhi →
    (∀ f ∈ fs, FloorFeatureD y₀ xlo xhi f) → (∀ f ∈ fs, s < (fstPt f).1) →
    fs.Pairwise (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (lstPt f).1 < (fstPt g).1) →
    ChainSimple ((s, y₀) :: fs.flatten ++ [(xhi, y₀)]) ∧
      chainSet ((s, y₀) :: fs.flatten ++ [(xhi, y₀)]) ⊆
        hline y₀ s xhi ∪ {p | ∃ f ∈ fs, p ∈ chainSet f}
  | [], s, hs, _, _, _ => by
    simp only [List.flatten_nil, List.nil_append, List.cons_append, chainSet_cons_cons,
      chainSet_single, union_empty]
    refine ⟨⟨fun h => by simp at h; linarith, by simp, trivial⟩, ?_⟩
    exact (segment_subset_hline hs.le).trans subset_union_left
  | f :: fs, s, hs, hF, hfst, hpw => by
    obtain ⟨hlen, hcs, hfy, hly, hfl, hon, hx⟩ := hF f (by simp)
    set a := fstPt f
    set q := lstPt f
    have hqmem := lstPt_mem hlen
    have hq : q = (q.1, y₀) := Prod.ext rfl hly
    have ha : a = (a.1, y₀) := Prod.ext rfl hfy
    have hpw' := List.pairwise_cons.1 hpw
    have ih := comb_floorD fs q.1 (hx q hqmem).2 (fun g hg => hF g (by simp [hg]))
      (fun g hg => (hpw'.1 g hg).2) hpw'.2
    set f' := f.tail.dropLast
    have hfdec : f = a :: (f' ++ [q]) := decomp_of_two_le hlen
    have hsa : s < a.1 := hfst f (by simp)
    have hP1 : ChainSimple ((s, y₀) :: (a :: f') ++ [q]) := by
      have e : (s, y₀) :: (a :: f') ++ [q] = (s, y₀) :: f := by rw [hfdec]; rfl
      rw [e, hfdec, chainSimple_cons_cons, ← hfdec]
      refine ⟨fun h => by rw [← h] at hsa; simp at hsa, ?_, hcs⟩
      rintro x ⟨hx1, hx2⟩
      have hxl := segment_subset_hline' (y₀ := y₀) (a := (s, y₀)) rfl hfy hsa.le hx1
      have := (hon x hx2 hxl.1).1
      rw [Set.mem_singleton_iff, ha]
      exact Prod.ext (le_antisymm hxl.2.2 this) hxl.1
    have hS1 : chainSet ((s, y₀) :: (a :: f') ++ [q]) =
        ArtGallery.segment (s, y₀) a ∪ chainSet f := by
      have e : (s, y₀) :: (a :: f') ++ [q] = (s, y₀) :: a :: (f' ++ [q]) := rfl
      rw [e, chainSet_cons_cons, ← hfdec]
    have hseg : ArtGallery.segment (s, y₀) a ⊆ hline y₀ s a.1 :=
      segment_subset_hline' (a := (s, y₀)) rfl hfy hsa.le
    have hjoin : chainSet ((s, y₀) :: (a :: f') ++ [q]) ∩ chainSet (q :: (fs.flatten ++ [(xhi, y₀)]))
        ⊆ {q} := by
      rw [hS1]
      rintro x ⟨hx1, hx2⟩
      have hx2' := ih.2 (by rw [hq] at hx2 ⊢; simpa using hx2)
      rcases hx1 with hx1 | hx1
      · have h1 := hseg hx1
        exfalso
        rcases hx2' with h2 | ⟨g, hg, hxg⟩
        · linarith [h1.2.2, h2.2.1]
        · obtain ⟨-, -, -, -, -, hgon, -⟩ := hF g (by simp [hg])
          have hqg := (hpw'.1 g hg).2
          have := (hgon x hxg h1.1).1
          linarith [h1.2.2]
      · rcases hx2' with h2 | ⟨g, hg, hxg⟩
        · have := (hon x hx1 h2.1).2
          rw [Set.mem_singleton_iff, hq]
          exact Prod.ext (le_antisymm this h2.2.1) h2.1
        · exact absurd hxg (Set.disjoint_left.1 (hpw'.1 g hg).1 hx1)
    have hcomb := ChainSimple.join hP1 (by rw [hq] at ih ⊢; simpa using ih.1) hjoin
    have e : (s, y₀) :: (f :: fs).flatten ++ [(xhi, y₀)] =
        ((s, y₀) :: (a :: f')) ++ q :: (fs.flatten ++ [(xhi, y₀)]) := by
      conv_lhs => rw [List.flatten_cons, hfdec]
      simp
    rw [e]
    refine ⟨hcomb, ?_⟩
    rw [chainSet_append_cons, hS1]
    refine union_subset (union_subset ?_ ?_) ?_
    · intro x hxs
      have := hseg hxs
      exact Or.inl ⟨this.1, this.2.1, by linarith [this.2.2, hfl, (hx q hqmem).2]⟩
    · intro x hx; exact Or.inr ⟨f, by simp, hx⟩
    · intro x hx
      rcases ih.2 (by rw [hq] at hx ⊢; simpa using hx) with h | ⟨g, hg, hxg⟩
      · exact Or.inl ⟨h.1, by linarith [h.2.1], h.2.2⟩
      · exact Or.inr ⟨g, by simp [hg], hxg⟩

/-! ### The ceiling comb, by reflection -/

theorem CeilFeatureD.neg {Y xlo xhi : ℝ} {f : List Point} (h : CeilFeatureD Y xlo xhi f) :
    FloorFeatureD (-Y) (-xhi) (-xlo) (f.map (fun q => -q)) := by
  obtain ⟨hlen, hcs, hfy, hly, hfl, hon, hx⟩ := h
  rw [FloorFeatureD, fstPt_map_neg hlen, lstPt_map_neg]
  refine ⟨by simpa using hlen, chainSimple_map_neg hcs, by simp [hfy], by simp [hly],
    by simp; linarith, ?_, ?_⟩
  · intro p hp hpy
    rw [chainSet_map_neg] at hp
    have := hon _ hp (by simp only [Prod.snd_neg, hpy, neg_neg])
    simp only [Prod.fst_neg] at this ⊢
    constructor <;> linarith [this.1, this.2]
  · intro p hp
    rw [chainSet_map_neg] at hp
    have := hx _ hp
    simp at this
    constructor <;> linarith [this.1, this.2]

/-- **Comb (ceiling), dented features.** -/
theorem comb_ceilingD {Y xlo xhi : ℝ} (hlt : xlo < xhi) (fs : List (List Point))
    (hF : ∀ f ∈ fs, CeilFeatureD Y xlo xhi f)
    (hpw : fs.Pairwise (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (fstPt g).1 < (lstPt f).1)) :
    ChainSimple ((xhi, Y) :: fs.flatten ++ [(xlo, Y)]) ∧
      chainSet ((xhi, Y) :: fs.flatten ++ [(xlo, Y)]) ⊆
        hline Y xlo xhi ∪ {p | ∃ f ∈ fs, p ∈ chainSet f} := by
  have hF' : ∀ f ∈ fs.map (List.map (fun q => -q)), FloorFeatureD (-Y) (-xhi) (-xlo) f := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact (hF g hg).neg
  have hfst : ∀ f ∈ fs.map (List.map (fun q => -q)), -xhi < (fstPt f).1 := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    obtain ⟨hlen, -, -, -, -, -, hx⟩ := hF g hg
    rw [fstPt_map_neg hlen]
    have := (hx _ (fstPt_mem hlen)).2
    simp; linarith
  have hpw' : (fs.map (List.map (fun q => -q))).Pairwise
      (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (lstPt f).1 < (fstPt g).1) := by
    rw [List.pairwise_map]
    refine hpw.imp_of_mem (fun {f g} hf hg hfg => ⟨?_, ?_⟩)
    · rw [Set.disjoint_iff]
      rintro x ⟨h1, h2⟩
      rw [chainSet_map_neg] at h1 h2
      exact Set.disjoint_left.1 hfg.1 h1 h2
    · rw [lstPt_map_neg, fstPt_map_neg (hF g hg).1]
      simp; linarith [hfg.2]
  obtain ⟨h1, h2⟩ := comb_floorD (xlo := -xhi) _ (-xhi) (by linarith) hF' hfst hpw'
  have e : (-xhi, -Y) :: (fs.map (List.map (fun q => -q))).flatten ++ [(-xlo, -Y)] =
      ((xhi, Y) :: fs.flatten ++ [(xlo, Y)]).map (fun q => -q) := by
    simp [List.map_flatten]
  rw [e] at h1 h2
  refine ⟨?_, ?_⟩
  · have := chainSimple_map_neg h1
    simpa [List.map_map] using this
  · intro p hp
    have hp' : -p ∈ chainSet (((xhi, Y) :: fs.flatten ++ [(xlo, Y)]).map (fun q => -q)) := by
      rw [chainSet_map_neg, neg_neg]; exact hp
    rcases h2 hp' with h | ⟨f, hf, hpf⟩
    · left
      obtain ⟨hy, hx1, hx2⟩ := h
      simp at hy hx1 hx2
      exact ⟨by linarith, by linarith, by linarith⟩
    · right
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      rw [chainSet_map_neg, neg_neg] at hpf
      exact ⟨g, hg, hpf⟩

/-! ### Rectangle with dented combs -/

/-- **Rectangle with dented combs.**  As `ArtGallery.Stade.Chain.simple_of_combs`, for dented
features, when the floor features lie below a line `y = m` and the ceiling features above it,
`y_lo < m < y_hi`. -/
theorem simple_of_combsD {xlo xhi ylo yhi m : ℝ} (hx : xlo < xhi) (hm1 : ylo < m) (hm2 : m < yhi)
    (F C : List (List Point)) (hF : ∀ f ∈ F, FloorFeatureD ylo xlo xhi f)
    (hFm : ∀ f ∈ F, ∀ p ∈ chainSet f, p.2 < m)
    (hFpw : F.Pairwise (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (lstPt f).1 < (fstPt g).1))
    (hC : ∀ f ∈ C, CeilFeatureD yhi xlo xhi f)
    (hCm : ∀ f ∈ C, ∀ p ∈ chainSet f, m < p.2)
    (hCpw : C.Pairwise (fun f g => Disjoint (chainSet f) (chainSet g) ∧ (fstPt g).1 < (lstPt f).1)) :
    (Polygon.mk ([(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten ++
      [(xlo, yhi)])).Simple := by
  have hfst : ∀ f ∈ F, xlo < (fstPt f).1 := fun f hf =>
    ((hF f hf).2.2.2.2.2.2 _ (fstPt_mem (hF f hf).1)).1
  obtain ⟨hF1, hF2⟩ := comb_floorD F xlo hx hF hfst hFpw
  obtain ⟨hC1, hC2⟩ := comb_ceilingD hx C hC hCpw
  have hW : ChainSimple ((xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)]) := by
    have e : (xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)] =
        ((xlo, ylo) :: F.flatten) ++ (xhi, ylo) :: [(xhi, yhi)] := by simp
    rw [e]
    refine ChainSimple.join (by simpa using hF1)
      ⟨fun h => by simp at h; linarith, by simp, trivial⟩ ?_
    rintro p ⟨h1, h2⟩
    simp only [chainSet_cons_cons, chainSet_single, union_empty] at h2
    have hp1 := vseg_fst h2
    have h1' : p ∈ chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo)]) := by simpa using h1
    rcases hF2 h1' with ⟨hpy, -, -⟩ | ⟨f, hf, hpf⟩
    · exact Prod.ext hp1 hpy
    · exact absurd hp1 (ne_of_lt ((hF f hf).2.2.2.2.2.2 p hpf).2)
  have hWset : chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)]) =
      chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo)]) ∪
        ArtGallery.segment (xhi, ylo) (xhi, yhi) := by
    have e : (xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)] =
        ((xlo, ylo) :: F.flatten) ++ (xhi, ylo) :: [(xhi, yhi)] := by simp
    rw [e, chainSet_append_cons]
    simp
  have hFbd : ∀ p ∈ chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo)]),
      p.2 < m ∧ xlo ≤ p.1 ∧ p.1 ≤ xhi ∧ (p.1 = xlo → p = (xlo, ylo)) := by
    intro p hp
    rcases hF2 hp with ⟨hpy, h1, h2⟩ | ⟨f, hf, hpf⟩
    · exact ⟨by linarith, h1, h2, fun h => Prod.ext h hpy⟩
    · have := (hF f hf).2.2.2.2.2.2 p hpf
      exact ⟨hFm f hf p hpf, this.1.le, this.2.le, fun h => absurd h (ne_of_gt this.1)⟩
  have hCbd : ∀ p ∈ chainSet ((xhi, yhi) :: C.flatten ++ [(xlo, yhi)]),
      m < p.2 ∧ (p.1 = xlo → p = (xlo, yhi)) ∧ (p.1 = xhi → p = (xhi, yhi)) := by
    intro p hp
    rcases hC2 hp with ⟨hpy, -, -⟩ | ⟨f, hf, hpf⟩
    · exact ⟨by linarith, fun h => Prod.ext h hpy, fun h => Prod.ext h hpy⟩
    · have := (hC f hf).2.2.2.2.2.2 p hpf
      exact ⟨hCm f hf p hpf, fun h => absurd h (ne_of_gt this.1),
        fun h => absurd h (ne_of_lt this.2)⟩
  have hAll : ChainSimple ((xlo, ylo) :: F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten ++
      [(xlo, yhi)]) := by
    have e : (xlo, ylo) :: F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten ++ [(xlo, yhi)] =
        ((xlo, ylo) :: F.flatten ++ [(xhi, ylo)]) ++ (xhi, yhi) :: (C.flatten ++ [(xlo, yhi)]) := by
      simp
    rw [e]
    refine ChainSimple.join (by simpa using hW) (by simpa using hC1) ?_
    rintro p ⟨h1, h2⟩
    have h1' : p ∈ chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)]) := by
      simpa using h1
    have h2' : p ∈ chainSet ((xhi, yhi) :: C.flatten ++ [(xlo, yhi)]) := by simpa using h2
    have hc := hCbd p h2'
    rw [hWset] at h1'
    rcases h1' with h1' | h1'
    · exact absurd (hFbd p h1').1 (by linarith [hc.1])
    · exact hc.2.2 (vseg_fst h1')
  have hAllset : chainSet ((xlo, ylo) :: F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten ++
      [(xlo, yhi)]) = chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo), (xhi, yhi)]) ∪
        chainSet ((xhi, yhi) :: C.flatten ++ [(xlo, yhi)]) := by
    have e : (xlo, ylo) :: F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten ++ [(xlo, yhi)] =
        ((xlo, ylo) :: F.flatten ++ [(xhi, ylo)]) ++ (xhi, yhi) :: (C.flatten ++ [(xlo, yhi)]) := by
      simp
    rw [e, chainSet_append_cons]
    simp
  have e : [(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten ++ [(xlo, yhi)] =
      (xlo, ylo) :: (F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten) ++ [(xlo, yhi)] := by
    simp
  rw [e]
  refine simple_of_chain (by simp) (by simpa using hAll) ?_
  rintro p ⟨h1, h2⟩
  have hp1 := vseg_fst h1
  have h2' : p ∈ chainSet ((xlo, ylo) :: F.flatten ++ (xhi, ylo) :: (xhi, yhi) :: C.flatten ++
      [(xlo, yhi)]) := by simpa using h2
  rw [hAllset, hWset] at h2'
  rcases h2' with (h | h) | h
  · exact Or.inl ((hFbd p h).2.2.2 hp1)
  · exact absurd (vseg_fst h) (by rw [hp1]; exact ne_of_lt hx)
  · exact Or.inr ((hCbd p h).2.1 hp1)

/-! ### Checks for dented orthogonal features -/

section Check

variable {α : Type*} [LinearOrder α]

/-- The edge `[u, v]` lies strictly below or strictly above the line `y = y₀`, or inside the
closed strip `x₁ ≤ x ≤ x₂`. -/
def lineOKB (y₀ x₁ x₂ : α) (u v : α × α) : Bool :=
  decide (u.2 < y₀ ∧ v.2 < y₀) || decide (y₀ < u.2 ∧ y₀ < v.2) ||
  decide (x₁ ≤ u.1 ∧ u.1 ≤ x₂ ∧ x₁ ≤ v.1 ∧ v.1 ≤ x₂)

/-- Every edge meets the line `y = y₀` only inside the span of the end points. -/
def spanB (y₀ : α) (ch : List (α × α)) : Bool :=
  match ch.head?, ch.getLast? with
  | some a, some z => oEdgesAll (lineOKB y₀ a.1 z.1) ch
  | _, _ => false

/-- The dented floor feature check for the line `y = y₀`. -/
def oFloorDB (y₀ : α) (ch : List (α × α)) : Bool :=
  decide (3 ≤ ch.length) && oChainB ch && endsB y₀ ch && spanB y₀ ch

/-- The dented ceiling feature check for the line `y = Y` (reversed orders). -/
def oCeilDB (Y : α) (ch : List (α × α)) : Bool :=
  oFloorDB (OrderDual.toDual Y) (ch.map (Prod.map OrderDual.toDual OrderDual.toDual))

end Check

section Map

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {f g : α → β} {S T : Set α}

theorem lineOKB_map (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {y₀ x₁ x₂ : α}
    (hy : y₀ ∈ T) (h₁ : x₁ ∈ S) (h₂ : x₂ ∈ S) {u v : α × α} (hu : u.1 ∈ S ∧ u.2 ∈ T)
    (hv : v.1 ∈ S ∧ v.2 ∈ T) :
    lineOKB (g y₀) (f x₁) (f x₂) (Prod.map f g u) (Prod.map f g v) = lineOKB y₀ x₁ x₂ u v := by
  simp only [lineOKB, Prod.map_fst, Prod.map_snd, hg.lt_iff_lt hu.2 hy, hg.lt_iff_lt hv.2 hy,
    hg.lt_iff_lt hy hu.2, hg.lt_iff_lt hy hv.2, hf.le_iff_le h₁ hu.1, hf.le_iff_le hu.1 h₂,
    hf.le_iff_le h₁ hv.1, hf.le_iff_le hv.1 h₂]

theorem oEdgesAll_lineOK_map (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {y₀ x₁ x₂ : α}
    (hy : y₀ ∈ T) (h₁ : x₁ ∈ S) (h₂ : x₂ ∈ S) :
    ∀ {l : List (α × α)}, InGrid S T l →
      oEdgesAll (lineOKB (g y₀) (f x₁) (f x₂)) (l.map (Prod.map f g)) =
        oEdgesAll (lineOKB y₀ x₁ x₂) l
  | [], _ => rfl
  | [_], _ => rfl
  | c :: d :: l, h => by
    simp only [List.map_cons, oEdgesAll]
    rw [lineOKB_map hf hg hy h₁ h₂ (h c (by simp)) (h d (by simp)), ← List.map_cons,
      oEdgesAll_lineOK_map hf hg hy h₁ h₂ h.tail]

theorem spanB_map (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {y₀ : α} (hy₀ : y₀ ∈ T)
    {l : List (α × α)} (h : InGrid S T l) :
    spanB (g y₀) (l.map (Prod.map f g)) = spanB y₀ l := by
  unfold spanB
  rw [List.head?_map, List.getLast?_map]
  cases ha : l.head? with
  | none => rfl
  | some a =>
    cases hz : l.getLast? with
    | none => rfl
    | some z =>
      have ha' := h a (List.mem_of_mem_head? ha)
      have hz' := h z (List.mem_of_getLast? hz)
      simp only [Option.map_some, Prod.map_fst]
      exact oEdgesAll_lineOK_map hf hg hy₀ ha'.1 hz'.1 h

theorem oFloorDB_map (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {y₀ : α} (hy₀ : y₀ ∈ T)
    {l : List (α × α)} (h : InGrid S T l) :
    oFloorDB (g y₀) (l.map (Prod.map f g)) = oFloorDB y₀ l := by
  unfold oFloorDB
  rw [oChainB_map hf hg h, endsB_map hf hg hy₀ h, List.length_map, spanB_map hf hg hy₀ h]

end Map

theorem convex_snd_lt (m : ℝ) : Convex ℝ {p : Point | p.2 < m} := by
  intro a ha b hb s t hs ht hst
  simp only [Set.mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at ha hb ⊢
  rcases eq_or_lt_of_le hs with rfl | hs'
  · simp only [zero_add] at hst; subst hst; simpa using hb
  · have h1 := mul_lt_mul_of_pos_left ha hs'
    have h2 := mul_le_mul_of_nonneg_left hb.le ht
    have : s * m + t * m = m := by rw [← add_mul, hst, one_mul]
    linarith

theorem convex_snd_gt (m : ℝ) : Convex ℝ {p : Point | m < p.2} := by
  intro a ha b hb s t hs ht hst
  simp only [Set.mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at ha hb ⊢
  rcases eq_or_lt_of_le hs with rfl | hs'
  · simp only [zero_add] at hst; subst hst; simpa using hb
  · have h1 := mul_lt_mul_of_pos_left ha hs'
    have h2 := mul_le_mul_of_nonneg_left hb.le ht
    have : s * m + t * m = m := by rw [← add_mul, hst, one_mul]
    linarith

/-- A chain whose vertices lie below `y = m` lies below it. -/
theorem chainSet_snd_lt {l : List Point} {m : ℝ} (h : ∀ p ∈ l, p.2 < m) :
    ∀ p ∈ chainSet l, p.2 < m := fun _ hp => chainSet_subset_of_convex (convex_snd_lt m) h hp

/-- A chain whose vertices lie above `y = m` lies above it. -/
theorem chainSet_snd_gt {l : List Point} {m : ℝ} (h : ∀ p ∈ l, m < p.2) :
    ∀ p ∈ chainSet l, m < p.2 := fun _ hp => chainSet_subset_of_convex (convex_snd_gt m) h hp

theorem mem_line_of_lineOKB {y₀ x₁ x₂ : ℝ} {u v p : Point} (h : lineOKB y₀ x₁ x₂ u v = true)
    (hp : p ∈ ArtGallery.segment u v) (hpy : p.2 = y₀) : x₁ ≤ p.1 ∧ p.1 ≤ x₂ := by
  have x1 := seg_fst_le hp; have x2 := seg_fst_ge hp
  have y1 := seg_snd_le hp; have y2 := seg_snd_ge hp
  simp only [lineOKB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · have : max u.2 v.2 < y₀ := max_lt h.1 h.2
    linarith
  · have : y₀ < min u.2 v.2 := lt_min h.1 h.2
    linarith
  · constructor
    · exact le_trans (le_min h.1 h.2.2.1) x2
    · exact le_trans x1 (max_le h.2.1 h.2.2.2)

/-- **Soundness of the dented floor feature check.** -/
theorem oFloorDB_sound {y₀ xlo xhi : ℝ} {ch : List Point} (h : oFloorDB y₀ ch = true)
    (hx : ∀ p ∈ ch, xlo < p.1 ∧ p.1 < xhi) : FloorFeatureD y₀ xlo xhi ch := by
  simp only [oFloorDB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h3, hch⟩, hends⟩, hspan⟩ := h
  obtain ⟨a, b, l, rfl⟩ : ∃ a b l, ch = a :: b :: l := by
    match ch, h3 with
    | a :: b :: l, _ => exact ⟨a, b, l, rfl⟩
  have hne : (b :: l) ≠ [] := by simp
  set z := (b :: l).getLast hne
  have hlast : (a :: b :: l).getLast? = some z := by
    rw [List.getLast?_eq_some_getLast (by simp)]
    simp [z, List.getLast_cons hne]
  simp only [endsB, List.head?_cons, hlast, decide_eq_true_eq] at hends
  simp only [spanB, List.head?_cons, hlast] at hspan
  obtain ⟨hay, hzy, haz⟩ := hends
  have hfst : fstPt (a :: b :: l) = a := rfl
  have hlst : lstPt (a :: b :: l) = z := by
    unfold lstPt; rw [List.getLastD_cons, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl
  refine ⟨by simp, oChainB_sound hch, by rw [hfst]; exact hay, by rw [hlst]; exact hzy,
    by rw [hfst, hlst]; exact haz, ?_, chainSet_subset_of_convex (convex_open_strip xlo xhi) hx⟩
  intro p hp hpy
  rw [hfst, hlst]
  obtain ⟨u, v, huv, hpuv⟩ := oEdgesAll_sound hspan hp
  exact mem_line_of_lineOKB huv hpuv hpy

/-- **Dented floor features from grids.** -/
theorem floorFeatureD_of_grid {xs ys : List ℝ} (hxs : xs.IsChain (· < ·))
    (hys : ys.IsChain (· < ·)) {l : List (ℕ × ℕ)} {j₀ : ℕ}
    (hl : ∀ p ∈ l, p.1 < xs.length ∧ p.2 < ys.length) (hj : j₀ < ys.length)
    (h : oFloorDB j₀ l = true) {xlo xhi : ℝ}
    (hx : ∀ p ∈ l, xlo < xs.getD p.1 0 ∧ xs.getD p.1 0 < xhi) :
    FloorFeatureD (ys.getD j₀ 0) xlo xhi (l.map (gridPt xs ys)) := by
  have hm := oFloorDB_map (strictMonoOn_getD hxs) (strictMonoOn_getD hys) (l := l) (y₀ := j₀)
    hj (fun p hp => hl p hp)
  rw [h, ← gridPt_eq] at hm
  refine oFloorDB_sound hm ?_
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact hx q hq

theorem ceilFeatureD_of_neg {Y xlo xhi : ℝ} {f : List Point}
    (h : FloorFeatureD (-Y) (-xhi) (-xlo) (f.map (fun q => -q))) : CeilFeatureD Y xlo xhi f := by
  obtain ⟨hlen, hcs, hfy, hly, hfl, hon, hx⟩ := h
  have hlen' : 2 ≤ f.length := by simpa using hlen
  rw [fstPt_map_neg hlen'] at hfy hfl hon
  rw [lstPt_map_neg] at hly hfl hon
  refine ⟨hlen', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := chainSimple_map_neg hcs
    simpa [List.map_map, Function.comp_def] using this
  · simp only [Prod.snd_neg, neg_inj] at hfy; exact hfy
  · simp only [Prod.snd_neg, neg_inj] at hly; exact hly
  · simp only [Prod.fst_neg, neg_lt_neg_iff] at hfl; exact hfl
  · intro p hp hpy
    have hp' : -p ∈ chainSet (f.map (fun q => -q)) := by rw [chainSet_map_neg, neg_neg]; exact hp
    have := hon _ hp' (by simp [hpy])
    simp only [Prod.fst_neg, neg_le_neg_iff] at this
    exact ⟨this.2, this.1⟩
  · intro p hp
    have hp' : -p ∈ chainSet (f.map (fun q => -q)) := by rw [chainSet_map_neg, neg_neg]; exact hp
    have := hx _ hp'
    simp only [Prod.fst_neg, neg_lt_neg_iff] at this
    exact ⟨this.2, this.1⟩

/-- **Dented ceiling features from grids.** -/
theorem ceilFeatureD_of_grid {xs ys : List ℝ} (hxs : xs.IsChain (· < ·))
    (hys : ys.IsChain (· < ·)) {l : List (ℕ × ℕ)} {j₀ : ℕ}
    (hl : ∀ p ∈ l, p.1 < xs.length ∧ p.2 < ys.length) (hj : j₀ < ys.length)
    (h : oCeilDB j₀ l = true) {xlo xhi : ℝ}
    (hx : ∀ p ∈ l, xlo < xs.getD p.1 0 ∧ xs.getD p.1 0 < xhi) :
    CeilFeatureD (ys.getD j₀ 0) xlo xhi (l.map (gridPt xs ys)) := by
  apply ceilFeatureD_of_neg
  set F : ℕᵒᵈ → ℝ := fun i => -xs.getD (OrderDual.ofDual i) 0
  set G : ℕᵒᵈ → ℝ := fun j => -ys.getD (OrderDual.ofDual j) 0
  have hF : StrictMonoOn F {i | OrderDual.ofDual i < xs.length} := by
    intro i hi j hj hij
    have := strictMonoOn_getD hxs (a := OrderDual.ofDual j) (b := OrderDual.ofDual i) hj hi hij
    simp only [F, neg_lt_neg_iff]; exact this
  have hG : StrictMonoOn G {j | OrderDual.ofDual j < ys.length} := by
    intro i hi j hj hij
    have := strictMonoOn_getD hys (a := OrderDual.ofDual j) (b := OrderDual.ofDual i) hj hi hij
    simp only [G, neg_lt_neg_iff]; exact this
  have e : (l.map (gridPt xs ys)).map (fun q => -q) =
      (l.map (Prod.map OrderDual.toDual OrderDual.toDual)).map (Prod.map F G) := by
    simp only [List.map_map]
    rfl
  have hm := oFloorDB_map hF hG (y₀ := OrderDual.toDual j₀)
    (l := l.map (Prod.map OrderDual.toDual OrderDual.toDual)) hj (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hl q hq)
  rw [← e] at hm
  have hG0 : G (OrderDual.toDual j₀) = -ys.getD j₀ 0 := rfl
  rw [hG0] at hm
  refine oFloorDB_sound (hm.trans h) ?_
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
  have := hx r hr
  simp only [gridPt, Prod.fst_neg, neg_lt_neg_iff]
  exact ⟨this.2, this.1⟩

/-! ### Features from monotone images -/

section Mono

variable {α : Type*} [LinearOrder α] {f g : α → ℝ} {S T : Set α}

/-- **Dented floor features from monotone images.**  The image of a chain passing `oFloorDB y₀`
under coordinate maps strictly increasing on its coordinates is a dented floor feature of the
line `y = g y₀`. -/
theorem floorFeatureD_of_mono (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {l : List (α × α)}
    (hl : InGrid S T l) {y₀ : α} (hy₀ : y₀ ∈ T) (h : oFloorDB y₀ l = true) {xlo xhi : ℝ}
    (hx : ∀ p ∈ l, xlo < f p.1 ∧ f p.1 < xhi) :
    FloorFeatureD (g y₀) xlo xhi (l.map (Prod.map f g)) := by
  have hm := oFloorDB_map hf hg hy₀ hl
  rw [h] at hm
  refine oFloorDB_sound hm ?_
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact hx q hq

/-- **Dented ceiling features from monotone images.** -/
theorem ceilFeatureD_of_mono (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {l : List (α × α)}
    (hl : InGrid S T l) {Y : α} (hY : Y ∈ T) (h : oCeilDB Y l = true) {xlo xhi : ℝ}
    (hx : ∀ p ∈ l, xlo < f p.1 ∧ f p.1 < xhi) :
    CeilFeatureD (g Y) xlo xhi (l.map (Prod.map f g)) := by
  apply ceilFeatureD_of_neg
  set F : αᵒᵈ → ℝ := fun i => -f (OrderDual.ofDual i)
  set G : αᵒᵈ → ℝ := fun j => -g (OrderDual.ofDual j)
  have hF : StrictMonoOn F {i | OrderDual.ofDual i ∈ S} := by
    intro i hi j hj hij
    have := hf hj hi hij
    simp only [F, neg_lt_neg_iff]; exact this
  have hG : StrictMonoOn G {j | OrderDual.ofDual j ∈ T} := by
    intro i hi j hj hij
    have := hg hj hi hij
    simp only [G, neg_lt_neg_iff]; exact this
  have e : (l.map (Prod.map f g)).map (fun q => -q) =
      (l.map (Prod.map OrderDual.toDual OrderDual.toDual)).map (Prod.map F G) := by
    simp only [List.map_map]
    rfl
  have hm := oFloorDB_map hF hG (y₀ := OrderDual.toDual Y)
    (l := l.map (Prod.map OrderDual.toDual OrderDual.toDual)) hY (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hl q hq)
  rw [← e] at hm
  have hG0 : G (OrderDual.toDual Y) = -g Y := rfl
  rw [hG0] at hm
  refine oFloorDB_sound (hm.trans h) ?_
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
  have := hx r hr
  simp only [Prod.map_fst, Prod.fst_neg, neg_lt_neg_iff]
  exact ⟨this.2, this.1⟩

end Mono

end

end ArtGallery.Orthogonal.Hard
