module

public import ArtGallery.Orthogonal.Hard.RatEq
public import ArtGallery.Stade.RobustCheck
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.GetD

/-!
# Orthogonal chains: a simplicity check by coordinate comparisons

Every edge of the orthogonal polygon of the hardness construction is horizontal or vertical.
Whether two axis-parallel segments meet depends only on the *order* of their coordinates, so the
simplicity of an orthogonal chain depends only on the order type of its abscissae and of its
ordinates.  This file makes that precise.

* `oChainB l`: a Boolean check, over any linear order, that uses only comparisons `<` and `=` of
  coordinates: every edge is axis-parallel and non-degenerate, consecutive edges are
  perpendicular, and non-consecutive edges have strictly separated bounding boxes.
* `oChainB_sound`: over `ℝ` the check implies `ChainSimple`.
* `oChainB_map`: the check is invariant under maps `x ↦ f x`, `y ↦ g y` that are strictly
  increasing on the coordinates of the chain.
* `oFloorB`, `oFloorB_sound`, `oFloorB_map`: the same for floor features
  (`ArtGallery.Stade.Chain.FloorFeature`); ceiling features are floor features of the reversed
  orders (`oCeilB`, `ceilFeature_of_oCeilB`).

A chain with symbolic coordinates is handled by writing it as the image of a chain of *grid
indices* `(i, j) : ℕ × ℕ` under `i ↦ xs[i]`, `j ↦ ys[j]` for strictly increasing lists `xs`,
`ys` (`floorFeature_of_grid`, `ceilFeature_of_grid`): the check on the grid chain is decided by
`decide`, and only the orderings of `xs` and `ys` remain to be proved.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade.Chain ArtGallery.Irrational Set

section Check

variable {α : Type*} [LinearOrder α]

/-- The edge `[a, b]` is axis-parallel and non-degenerate. -/
def axisB (a b : α × α) : Bool :=
  (decide (a.1 = b.1) && !decide (a.2 = b.2)) || (decide (a.2 = b.2) && !decide (a.1 = b.1))

/-- The bounding boxes of `[a, b]` and `[c, d]` are strictly separated by a vertical or a
horizontal line. -/
def boxSepB (a b c d : α × α) : Bool :=
  decide (a.1 < c.1 ∧ a.1 < d.1 ∧ b.1 < c.1 ∧ b.1 < d.1) ||
  decide (c.1 < a.1 ∧ c.1 < b.1 ∧ d.1 < a.1 ∧ d.1 < b.1) ||
  decide (a.2 < c.2 ∧ a.2 < d.2 ∧ b.2 < c.2 ∧ b.2 < d.2) ||
  decide (c.2 < a.2 ∧ c.2 < b.2 ∧ d.2 < a.2 ∧ d.2 < b.2)

/-- The edges `[a, b]` (vertical) and `[b, c]` (horizontal), or vice versa, turn at `b`. -/
def turnB (a b c : α × α) : Bool :=
  (decide (a.1 = b.1) && decide (b.2 = c.2)) || (decide (a.2 = b.2) && decide (b.1 = c.1))

/-- `f` holds for every edge of the chain. -/
def oEdgesAll (f : α × α → α × α → Bool) : List (α × α) → Bool
  | a :: b :: l => f a b && oEdgesAll f (b :: l)
  | _ => true

/-- The conditions on the first edge `[a, b]` of a chain `a, b, l…`: a turn at `b`, and box
separation from all edges after the next one. -/
def oFirstOK (a b : α × α) : List (α × α) → Bool
  | [] => true
  | c :: l => turnB a b c && oEdgesAll (boxSepB a b) (c :: l)

/-- The simplicity check of an orthogonal open chain. -/
def oChainB : List (α × α) → Bool
  | a :: b :: l => axisB a b && oFirstOK a b l && oChainB (b :: l)
  | _ => true

/-- The end points of the chain lie on the line `y = y₀`, the first one left of the last one. -/
def endsB (y₀ : α) (ch : List (α × α)) : Bool :=
  match ch.head?, ch.getLast? with
  | some a, some z => decide (a.2 = y₀ ∧ z.2 = y₀ ∧ a.1 < z.1)
  | _, _ => false

/-- The floor feature check for the line `y = y₀`: at least three vertices, a simple orthogonal
chain, end points on the line (from left to right), all other vertices strictly below. -/
def oFloorB (y₀ : α) (ch : List (α × α)) : Bool :=
  decide (3 ≤ ch.length) && oChainB ch && endsB y₀ ch &&
  ch.tail.dropLast.all (fun p => decide (p.2 < y₀))

/-- The ceiling feature check for the line `y = Y`: the floor feature check for the reversed
orders (end points from right to left, other vertices strictly above). -/
def oCeilB (Y : α) (ch : List (α × α)) : Bool :=
  oFloorB (OrderDual.toDual Y) (ch.map (Prod.map OrderDual.toDual OrderDual.toDual))

end Check

/-! ### Invariance under monotone coordinate maps -/

section Map

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {f g : α → β} {S T : Set α}

/-- All abscissae lie in `S`, all ordinates in `T`. -/
def InGrid (S T : Set α) (l : List (α × α)) : Prop := ∀ p ∈ l, p.1 ∈ S ∧ p.2 ∈ T

omit [LinearOrder α] in
theorem InGrid.tail {a : α × α} {l : List (α × α)} (h : InGrid S T (a :: l)) : InGrid S T l :=
  fun p hp => h p (List.mem_cons_of_mem _ hp)

theorem axisB_map (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {a b : α × α}
    (ha : a.1 ∈ S ∧ a.2 ∈ T) (hb : b.1 ∈ S ∧ b.2 ∈ T) :
    axisB (Prod.map f g a) (Prod.map f g b) = axisB a b := by
  simp only [axisB, Prod.map_fst, Prod.map_snd, hf.injOn.eq_iff ha.1 hb.1,
    hg.injOn.eq_iff ha.2 hb.2]

theorem boxSepB_map (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {a b c d : α × α}
    (ha : a.1 ∈ S ∧ a.2 ∈ T) (hb : b.1 ∈ S ∧ b.2 ∈ T) (hc : c.1 ∈ S ∧ c.2 ∈ T)
    (hd : d.1 ∈ S ∧ d.2 ∈ T) :
    boxSepB (Prod.map f g a) (Prod.map f g b) (Prod.map f g c) (Prod.map f g d) =
      boxSepB a b c d := by
  obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc; obtain ⟨hd1, hd2⟩ := hd
  simp only [boxSepB, Prod.map_fst, Prod.map_snd, hf.lt_iff_lt ha1 hc1, hf.lt_iff_lt ha1 hd1,
    hf.lt_iff_lt hb1 hc1, hf.lt_iff_lt hb1 hd1, hf.lt_iff_lt hc1 ha1, hf.lt_iff_lt hc1 hb1,
    hf.lt_iff_lt hd1 ha1, hf.lt_iff_lt hd1 hb1, hg.lt_iff_lt ha2 hc2, hg.lt_iff_lt ha2 hd2,
    hg.lt_iff_lt hb2 hc2, hg.lt_iff_lt hb2 hd2, hg.lt_iff_lt hc2 ha2, hg.lt_iff_lt hc2 hb2,
    hg.lt_iff_lt hd2 ha2, hg.lt_iff_lt hd2 hb2]

theorem turnB_map (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {a b c : α × α}
    (ha : a.1 ∈ S ∧ a.2 ∈ T) (hb : b.1 ∈ S ∧ b.2 ∈ T) (hc : c.1 ∈ S ∧ c.2 ∈ T) :
    turnB (Prod.map f g a) (Prod.map f g b) (Prod.map f g c) = turnB a b c := by
  simp only [turnB, Prod.map_fst, Prod.map_snd, hf.injOn.eq_iff ha.1 hb.1,
    hg.injOn.eq_iff hb.2 hc.2, hg.injOn.eq_iff ha.2 hb.2, hf.injOn.eq_iff hb.1 hc.1]

theorem oEdgesAll_boxSep_map (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {a b : α × α}
    (ha : a.1 ∈ S ∧ a.2 ∈ T) (hb : b.1 ∈ S ∧ b.2 ∈ T) :
    ∀ {l : List (α × α)}, InGrid S T l →
      oEdgesAll (boxSepB (Prod.map f g a) (Prod.map f g b)) (l.map (Prod.map f g)) =
        oEdgesAll (boxSepB a b) l
  | [], _ => rfl
  | [_], _ => rfl
  | c :: d :: l, h => by
    simp only [List.map_cons, oEdgesAll]
    rw [boxSepB_map hf hg ha hb (h c (by simp)) (h d (by simp)), ← List.map_cons,
      oEdgesAll_boxSep_map hf hg ha hb h.tail]

theorem oChainB_map (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) :
    ∀ {l : List (α × α)}, InGrid S T l → oChainB (l.map (Prod.map f g)) = oChainB l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have ha := h a (by simp)
    have hb := h b (by simp)
    simp only [List.map_cons, oChainB]
    rw [axisB_map hf hg ha hb, ← List.map_cons, oChainB_map hf hg h.tail]
    congr 2
    cases l with
    | nil => rfl
    | cons c l =>
      simp only [List.map_cons, oFirstOK]
      rw [turnB_map hf hg ha hb (h c (by simp)), ← List.map_cons,
        oEdgesAll_boxSep_map hf hg ha hb h.tail.tail]

theorem endsB_map (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {y₀ : α} (hy₀ : y₀ ∈ T)
    {l : List (α × α)} (h : InGrid S T l) :
    endsB (g y₀) (l.map (Prod.map f g)) = endsB y₀ l := by
  unfold endsB
  rw [List.head?_map, List.getLast?_map]
  cases ha : l.head? with
  | none => rfl
  | some a =>
    cases hz : l.getLast? with
    | none => rfl
    | some z =>
      have ha' := h a (List.mem_of_mem_head? ha)
      have hz' := h z (List.mem_of_getLast? hz)
      simp only [Option.map_some, Prod.map_fst, Prod.map_snd, hg.injOn.eq_iff ha'.2 hy₀,
        hg.injOn.eq_iff hz'.2 hy₀, hf.lt_iff_lt ha'.1 hz'.1]

theorem oFloorB_map (hf : StrictMonoOn f S) (hg : StrictMonoOn g T) {y₀ : α} (hy₀ : y₀ ∈ T)
    {l : List (α × α)} (h : InGrid S T l) :
    oFloorB (g y₀) (l.map (Prod.map f g)) = oFloorB y₀ l := by
  have hall : (l.map (Prod.map f g)).tail.dropLast.all (fun p => decide (p.2 < g y₀)) =
      l.tail.dropLast.all (fun p => decide (p.2 < y₀)) := by
    rw [← List.map_tail, ← List.map_dropLast, Bool.eq_iff_iff, List.all_eq_true,
      List.all_eq_true]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Prod.map_snd, decide_eq_true_eq]
    refine forall₂_congr fun p hp => ?_
    have hp' := h p (List.mem_of_mem_tail (List.mem_of_mem_dropLast hp))
    exact hg.lt_iff_lt hp'.2 hy₀
  unfold oFloorB
  rw [oChainB_map hf hg h, endsB_map hf hg hy₀ h, List.length_map, hall]

end Map

/-! ### Soundness over the reals -/

theorem axisB_ne {a b : Point} (h : axisB a b = true) : a ≠ b := by
  rintro rfl
  simp [axisB] at h

theorem disjoint_of_boxSepB {a b c d : Point} (h : boxSepB a b c d = true) {p : Point}
    (h1 : p ∈ ArtGallery.segment a b) (h2 : p ∈ ArtGallery.segment c d) : False := by
  have x1 := seg_fst_le h1; have x2 := seg_fst_ge h1
  have x3 := seg_fst_le h2; have x4 := seg_fst_ge h2
  have y1 := seg_snd_le h1; have y2 := seg_snd_ge h1
  have y3 := seg_snd_le h2; have y4 := seg_snd_ge h2
  simp only [boxSepB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((h | h) | h) | h
  · have : max a.1 b.1 < min c.1 d.1 := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]; exact ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩
    linarith
  · have : max c.1 d.1 < min a.1 b.1 := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]; exact ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩
    linarith
  · have : max a.2 b.2 < min c.2 d.2 := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]; exact ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩
    linarith
  · have : max c.2 d.2 < min a.2 b.2 := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]; exact ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩
    linarith

theorem fst_eq_of_mem_vseg {a b p : Point} (hab : a.1 = b.1) (h : p ∈ ArtGallery.segment a b) :
    p.1 = a.1 := by
  have h1 := seg_fst_le h; have h2 := seg_fst_ge h
  rw [← hab, max_self] at h1; rw [← hab, min_self] at h2
  exact le_antisymm h1 h2

theorem snd_eq_of_mem_hseg {a b p : Point} (hab : a.2 = b.2) (h : p ∈ ArtGallery.segment a b) :
    p.2 = a.2 := by
  have h1 := seg_snd_le h; have h2 := seg_snd_ge h
  rw [← hab, max_self] at h1; rw [← hab, min_self] at h2
  exact le_antisymm h1 h2

theorem eq_of_turnB {a b c p : Point} (h : turnB a b c = true)
    (h1 : p ∈ ArtGallery.segment a b) (h2 : p ∈ ArtGallery.segment b c) : p = b := by
  simp only [turnB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact Prod.ext ((fst_eq_of_mem_vseg hx h1).trans hx) (snd_eq_of_mem_hseg hy h2)
  · exact Prod.ext (fst_eq_of_mem_vseg hx h2) ((snd_eq_of_mem_hseg hy h1).trans hy)

theorem oEdgesAll_sound {f : Point → Point → Bool} :
    ∀ {l : List Point}, oEdgesAll f l = true → ∀ {x : Point}, x ∈ chainSet l →
      ∃ u v, f u v = true ∧ x ∈ ArtGallery.segment u v
  | [], _, _, hx => by simp at hx
  | [_], _, _, hx => by simp at hx
  | a :: b :: l, h, x, hx => by
    simp only [oEdgesAll, Bool.and_eq_true] at h
    rw [chainSet_cons_cons] at hx
    rcases hx with hx | hx
    · exact ⟨a, b, h.1, hx⟩
    · exact oEdgesAll_sound h.2 hx

/-- **Soundness of the orthogonal chain check.** -/
theorem oChainB_sound : ∀ {l : List Point}, oChainB l = true → ChainSimple l
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, h => by
    simp only [oChainB, Bool.and_eq_true] at h
    obtain ⟨⟨hax, hfirst⟩, hrest⟩ := h
    refine ⟨axisB_ne hax, ?_, oChainB_sound hrest⟩
    cases l with
    | nil => simp
    | cons c l =>
      simp only [oFirstOK, Bool.and_eq_true] at hfirst
      rw [chainSet_cons_cons]
      rintro x ⟨hx1, hx2 | hx2⟩
      · exact eq_of_turnB hfirst.1 hx1 hx2
      · obtain ⟨u, v, huv, hxuv⟩ := oEdgesAll_sound hfirst.2 hx2
        exact (disjoint_of_boxSepB huv hx1 hxuv).elim

/-- **Soundness of the floor feature check.**  A chain passing `oFloorB y₀` and lying strictly
inside the strip `x_lo < x < x_hi` is a floor feature of the line `y = y₀`. -/
theorem oFloorB_sound {y₀ xlo xhi : ℝ} {ch : List Point} (h : oFloorB y₀ ch = true)
    (hx : ∀ p ∈ ch, xlo < p.1 ∧ p.1 < xhi) : FloorFeature y₀ xlo xhi ch := by
  simp only [oFloorB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h3, hch⟩, hends⟩, hmid⟩ := h
  obtain ⟨a, b, l, rfl⟩ : ∃ a b l, ch = a :: b :: l := by
    match ch, h3 with
    | a :: b :: l, _ => exact ⟨a, b, l, rfl⟩
  have hne : (b :: l) ≠ [] := by simp
  set z := (b :: l).getLast hne
  set m := (b :: l).dropLast
  have hbl : b :: l = m ++ [z] := (List.dropLast_append_getLast hne).symm
  have hlast : (a :: b :: l).getLast? = some z := by
    rw [List.getLast?_eq_some_getLast (by simp)]
    simp [z, List.getLast_cons hne]
  simp only [endsB, List.head?_cons, hlast, decide_eq_true_eq] at hends
  obtain ⟨hay, hzy, haz⟩ := hends
  simp only [List.tail_cons] at hmid
  have hm : m ≠ [] := by
    intro hm0
    have := congrArg List.length hm0
    simp only [m, List.length_dropLast, List.length_cons, List.length_nil] at this h3
    omega
  have hR : a :: b :: l = a :: (m ++ [z]) := by rw [hbl]
  have hfst : fstPt (a :: b :: l) = a := rfl
  have hlst : lstPt (a :: b :: l) = z := by
    rw [hR]; unfold lstPt; rw [List.getLastD_cons, List.getLastD_concat]
  have hmid' : ∀ p ∈ m, p.2 < y₀ := fun p hp => hmid p hp
  refine ⟨by simp, oChainB_sound hch, by rw [hfst]; exact hay, by rw [hlst]; exact hzy,
    by rw [hfst, hlst]; exact haz, ?_, ?_⟩
  · intro p hp
    rw [hfst, hlst]
    rw [hR] at hp
    obtain ⟨v, rest, hvr⟩ := List.exists_cons_of_ne_nil hm
    rw [hvr] at hp hmid'
    have e : a :: (v :: rest ++ [z]) = a :: v :: (rest ++ [z]) := rfl
    rw [e, chainSet_cons_cons] at hp
    rcases hp with hp | hp
    · rw [ArtGallery.Geometry.segment_comm] at hp
      rcases seg_below (hmid' v (by simp)) hay.le hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases chainSet_below v rest _ (hmid' v (by simp)) (fun q hq => hmid' q (by simp [hq]))
          hzy.le p hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · exact chainSet_subset_of_convex (convex_open_strip xlo xhi) hx

/-! ### Grids -/

/-- The point of the grid chain with abscissa index `i` and ordinate index `j`. -/
def gridPt (xs ys : List ℝ) (p : ℕ × ℕ) : Point := (xs.getD p.1 0, ys.getD p.2 0)

theorem strictMonoOn_getD {xs : List ℝ} (h : xs.IsChain (· < ·)) :
    StrictMonoOn (fun i => xs.getD i 0) (Iio xs.length) := by
  intro i hi j hj hij
  simp only [mem_Iio] at hi hj
  show xs.getD i 0 < xs.getD j 0
  rw [List.getD_eq_getElem (l := xs) (d := 0) hi, List.getD_eq_getElem (l := xs) (d := 0) hj]
  exact (List.isChain_iff_pairwise.1 h).rel_get_of_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij

theorem gridPt_eq (xs ys : List ℝ) :
    gridPt xs ys = Prod.map (fun i => xs.getD i 0) (fun j => ys.getD j 0) := rfl

/-- **Floor features from grids.**  The image of a grid chain passing `oFloorB j₀` under strictly
increasing coordinate lists is a floor feature of the line `y = ys[j₀]`. -/
theorem floorFeature_of_grid {xs ys : List ℝ} (hxs : xs.IsChain (· < ·))
    (hys : ys.IsChain (· < ·)) {l : List (ℕ × ℕ)} {j₀ : ℕ}
    (hl : ∀ p ∈ l, p.1 < xs.length ∧ p.2 < ys.length) (hj : j₀ < ys.length)
    (h : oFloorB j₀ l = true) {xlo xhi : ℝ}
    (hx : ∀ p ∈ l, xlo < xs.getD p.1 0 ∧ xs.getD p.1 0 < xhi) :
    FloorFeature (ys.getD j₀ 0) xlo xhi (l.map (gridPt xs ys)) := by
  have hm := oFloorB_map (strictMonoOn_getD hxs) (strictMonoOn_getD hys) (l := l) (y₀ := j₀)
    hj (fun p hp => hl p hp)
  rw [h, ← gridPt_eq] at hm
  refine oFloorB_sound hm ?_
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact hx q hq

/-- A chain whose reflection through the origin is a floor feature of `y = −Y` in the strip
`−x_hi < x < −x_lo` is a ceiling feature of `y = Y` in the strip `x_lo < x < x_hi`. -/
theorem ceilFeature_of_neg {Y xlo xhi : ℝ} {f : List Point}
    (h : FloorFeature (-Y) (-xhi) (-xlo) (f.map (fun q => -q))) : CeilFeature Y xlo xhi f := by
  obtain ⟨hlen, hcs, hfy, hly, hfl, hab, hx⟩ := h
  have hlen' : 2 ≤ f.length := by simpa using hlen
  rw [fstPt_map_neg hlen'] at hfy hfl hab
  rw [lstPt_map_neg] at hly hfl hab
  refine ⟨hlen', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := chainSimple_map_neg hcs
    simpa [List.map_map, Function.comp_def] using this
  · simp only [Prod.snd_neg, neg_inj] at hfy; exact hfy
  · simp only [Prod.snd_neg, neg_inj] at hly; exact hly
  · simp only [Prod.fst_neg, neg_lt_neg_iff] at hfl; exact hfl
  · intro p hp
    have hp' : -p ∈ chainSet (f.map (fun q => -q)) := by rw [chainSet_map_neg, neg_neg]; exact hp
    rcases hab _ hp' with h | h | h
    · left; simp only [Prod.snd_neg, neg_lt_neg_iff] at h; exact h
    · right; left; exact neg_inj.1 h
    · right; right; exact neg_inj.1 h
  · intro p hp
    have hp' : -p ∈ chainSet (f.map (fun q => -q)) := by rw [chainSet_map_neg, neg_neg]; exact hp
    have := hx _ hp'
    simp only [Prod.fst_neg, neg_lt_neg_iff] at this
    exact ⟨this.2, this.1⟩

/-- **Ceiling features from grids.**  The image of a grid chain passing `oCeilB j₀` under
strictly increasing coordinate lists is a ceiling feature of the line `y = ys[j₀]`. -/
theorem ceilFeature_of_grid {xs ys : List ℝ} (hxs : xs.IsChain (· < ·))
    (hys : ys.IsChain (· < ·)) {l : List (ℕ × ℕ)} {j₀ : ℕ}
    (hl : ∀ p ∈ l, p.1 < xs.length ∧ p.2 < ys.length) (hj : j₀ < ys.length)
    (h : oCeilB j₀ l = true) {xlo xhi : ℝ}
    (hx : ∀ p ∈ l, xlo < xs.getD p.1 0 ∧ xs.getD p.1 0 < xhi) :
    CeilFeature (ys.getD j₀ 0) xlo xhi (l.map (gridPt xs ys)) := by
  apply ceilFeature_of_neg
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
  have hm := oFloorB_map hF hG (y₀ := OrderDual.toDual j₀)
    (l := l.map (Prod.map OrderDual.toDual OrderDual.toDual)) hj (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hl q hq)
  rw [← e] at hm
  have hG0 : G (OrderDual.toDual j₀) = -ys.getD j₀ 0 := rfl
  rw [hG0] at hm
  refine oFloorB_sound (hm.trans h) ?_
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
  have := hx r hr
  simp only [gridPt, Prod.fst_neg, neg_lt_neg_iff]
  exact ⟨this.2, this.1⟩

end

end ArtGallery.Orthogonal.Hard
