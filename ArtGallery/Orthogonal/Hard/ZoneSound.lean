module

public import ArtGallery.Orthogonal.Hard.ZoneCheck
public import Mathlib.Data.List.GetD

/-!
# Soundness of the zone check

For a zone `z` passing `zoneOK` and realisation maps `φ, ψ` strictly increasing on the grid
indices, the realised rectangles `zonePieces φ ψ z` satisfy:

* `zone_isPiece`: every rectangle is a convex piece;
* `zone_side`: every point of every side of every rectangle lies on a realised boundary segment,
  or is interior to the union of the rectangles, or lies on the top or a lateral side of the box;
* `zone_tiles`: near every point of the box top, the lower quadrants are covered by rectangles;
* `zone_left`, `zone_right`: the first rectangle has the left box side as its left side, the last
  one the right box side as its right side;
* `zone_cover`: every realised boundary segment lies in the union of the rectangles.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational Set Metric

/-! ### Realisation -/

section Real

variable (φ ψ : ℕ → ℝ)

/-- The realised grid point. -/
def gpt (p : ℕ × ℕ) : Point := (φ p.1, ψ p.2)

/-- The realised grid segment. -/
def gseg (e : GSeg) : Set Point := ArtGallery.segment (gpt φ ψ e.1) (gpt φ ψ e.2)

/-- The realised grid rectangle. -/
def grect (r : GRect) : Polygon := rectP (φ r.1) (φ r.2.1) (ψ r.2.2.1) (ψ r.2.2.2)

/-- The realised rectangles of a zone. -/
def zonePieces (z : Zone) : List Polygon := z.rects.map (grect φ ψ)

/-- The union of the realised rectangles of a zone. -/
def zoneUnion (z : Zone) : Set Point := pieceUnion {K | K ∈ zonePieces φ ψ z}

end Real

/-! ### Segments -/

theorem mem_segment_vert {x a b y : ℝ} (h1 : min a b ≤ y) (h2 : y ≤ max a b) :
    ((x, y) : Point) ∈ ArtGallery.segment (x, a) (x, b) := by
  rcases eq_or_ne a b with rfl | hab
  · simp only [min_self, max_self] at h1 h2
    exact ⟨0, le_rfl, zero_le_one, by simp [le_antisymm h2 h1]⟩
  · refine ⟨(y - a) / (b - a), ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hab with h | h
      · rw [min_eq_left h.le] at h1; exact div_nonneg (by linarith) (by linarith)
      · rw [max_eq_left h.le] at h2; exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · rcases lt_or_gt_of_ne hab with h | h
      · rw [max_eq_right h.le] at h2; exact (div_le_one (by linarith)).2 (by linarith)
      · rw [min_eq_right h.le] at h1; exact (div_le_one_of_neg (by linarith)).2 (by linarith)
    · have : b - a ≠ 0 := sub_ne_zero.2 hab.symm
      ext <;> simp <;> field_simp <;> ring

theorem mem_segment_horiz {y a b x : ℝ} (h1 : min a b ≤ x) (h2 : x ≤ max a b) :
    ((x, y) : Point) ∈ ArtGallery.segment (a, y) (b, y) := by
  rcases eq_or_ne a b with rfl | hab
  · simp only [min_self, max_self] at h1 h2
    exact ⟨0, le_rfl, zero_le_one, by simp [le_antisymm h2 h1]⟩
  · refine ⟨(x - a) / (b - a), ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hab with h | h
      · rw [min_eq_left h.le] at h1; exact div_nonneg (by linarith) (by linarith)
      · rw [max_eq_left h.le] at h2; exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · rcases lt_or_gt_of_ne hab with h | h
      · rw [max_eq_right h.le] at h2; exact (div_le_one (by linarith)).2 (by linarith)
      · rw [min_eq_right h.le] at h1; exact (div_le_one_of_neg (by linarith)).2 (by linarith)
    · have : b - a ≠ 0 := sub_ne_zero.2 hab.symm
      ext <;> simp <;> field_simp <;> ring

theorem segment_subset_of_ends {a b c d : Point} (ha : a ∈ ArtGallery.segment c d)
    (hb : b ∈ ArtGallery.segment c d) : ArtGallery.segment a b ⊆ ArtGallery.segment c d := by
  rw [Geometry.segment_eq, Geometry.segment_eq] at *
  exact (convex_segment c d).segment_subset ha hb

/-! ### Monotonicity -/

section Mono

variable {φ ψ : ℕ → ℝ} {NX NY : ℕ} (hφ : StrictMonoOn φ (Iio NX)) (hψ : StrictMonoOn ψ (Iio NY))
include hφ hψ

omit hφ hψ in
theorem betweenB_sound {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Iio N)) {a b c : ℕ}
    (ha : a < N) (hb : b < N) (hc : c < N) (h : betweenB a b c = true) :
    min (f b) (f c) ≤ f a ∧ f a ≤ max (f b) (f c) := by
  simp only [betweenB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := hf.monotoneOn hb ha h1
    have e2 := hf.monotoneOn ha hc h2
    exact ⟨(min_le_left _ _).trans e1, e2.trans (le_max_right _ _)⟩
  · have e1 := hf.monotoneOn hc ha h1
    have e2 := hf.monotoneOn ha hb h2
    exact ⟨(min_le_right _ _).trans e1, e2.trans (le_max_left _ _)⟩

theorem onSegB_sound {p : ℕ × ℕ} {e : GSeg} (h : onSegB p e = true) (hp1 : p.1 < NX)
    (hp2 : p.2 < NY) (he1 : e.1.1 < NX) (he2 : e.2.1 < NX) (he3 : e.1.2 < NY) (he4 : e.2.2 < NY) :
    gpt φ ψ p ∈ gseg φ ψ e := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := e
  obtain ⟨p1, p2⟩ := p
  simp only [onSegB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h hp1 hp2 he1 he2 he3 he4
  unfold gpt gseg
  simp only
  rcases h with ⟨⟨rfl, rfl⟩, h3⟩ | ⟨⟨rfl, rfl⟩, h3⟩
  · obtain ⟨c1, c2⟩ := betweenB_sound hψ hp2 he3 he4 h3
    exact mem_segment_vert c1 c2
  · obtain ⟨c1, c2⟩ := betweenB_sound hφ hp1 he1 he2 h3
    exact mem_segment_horiz c1 c2

end Mono

/-! ### Items of a lateral side -/

theorem chainItems_bounds : ∀ (items : List (ℕ × ℕ × VItem)) (c d : ℕ),
    chainItems c items d = true → (∀ it ∈ items, it.1 < it.2.1) →
    c < d ∧ ∀ it ∈ items, c ≤ it.1 ∧ it.2.1 ≤ d
  | [], _, _, h, _ => by simp [chainItems] at h
  | [it], c, d, h, hlt => by
    simp only [chainItems, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hlt it (by simp), fun j hj => by simp at hj; subst hj; exact ⟨le_rfl, le_rfl⟩⟩
  | it :: it' :: rest, c, d, h, hlt => by
    simp only [chainItems, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h'⟩ := h
    obtain ⟨h1, h2⟩ := chainItems_bounds (it' :: rest) it.2.1 d h'
      (fun j hj => hlt j (List.mem_cons_of_mem _ hj))
    have h0 := hlt it (by simp)
    refine ⟨by omega, fun j hj => ?_⟩
    rcases List.mem_cons.1 hj with rfl | hj
    · exact ⟨le_rfl, h1.le⟩
    · have := h2 j hj; exact ⟨by omega, this.2⟩

theorem items_locate {ψ : ℕ → ℝ} {N : ℕ} (hψ : StrictMonoOn ψ (Iio N)) :
    ∀ (items : List (ℕ × ℕ × VItem)) (c d : ℕ), chainItems c items d = true →
      (∀ it ∈ items, it.1 < it.2.1) → d < N → ∀ s : ℝ, ψ c ≤ s → s ≤ ψ d →
      s = ψ c ∨ s = ψ d ∨ (∃ it ∈ items, ψ it.1 < s ∧ s < ψ it.2.1) ∨
        (∃ it ∈ items.dropLast, s = ψ it.2.1)
  | [], _, _, h, _, _, _, _, _ => by simp [chainItems] at h
  | [it], c, d, h, hlt, hd, s, h1, h2 => by
    simp only [chainItems, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases eq_or_lt_of_le h1 with h1 | h1
    · exact Or.inl h1.symm
    rcases eq_or_lt_of_le h2 with h2 | h2
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (Or.inl ⟨it, by simp, h1, h2⟩))
  | it :: it' :: rest, c, d, h, hlt, hd, s, h1, h2 => by
    have hb := chainItems_bounds _ _ _ h hlt
    simp only [chainItems, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h'⟩ := h
    have hit := hb.2 it (by simp)
    have hm : it.2.1 < N := lt_of_le_of_lt hit.2 hd
    rcases lt_trichotomy s (ψ it.2.1) with hs | hs | hs
    · rcases eq_or_lt_of_le h1 with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr (Or.inr (Or.inl ⟨it, by simp, h1, hs⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨it, by simp, hs⟩))
    · rcases items_locate hψ (it' :: rest) it.2.1 d h'
          (fun j hj => hlt j (List.mem_cons_of_mem _ hj)) hd s hs.le h2 with
        h | h | ⟨j, hj, hj'⟩ | ⟨j, hj, hj'⟩
      · exact absurd h hs.ne'
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨j, List.mem_cons_of_mem _ hj, hj'⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨j, ?_, hj'⟩))
        rw [List.dropLast_cons_of_ne_nil (by simp)]
        exact List.mem_cons_of_mem _ hj

theorem bpsOK_sound {z : Zone} {x : ℕ} : ∀ (items : List (ℕ × ℕ × VItem)) (bps : List ℕ),
    bpsOK z x items bps = true → ∀ it ∈ items.dropLast, ∃ e < z.pedges.length,
      onSegB (x, it.2.1) (z.pedges.getD e ((0, 0), (0, 0))) = true
  | [], [], _, it, hit => by simp at hit
  | [_], [], _, it, hit => by simp at hit
  | it₀ :: it₁ :: rest, e :: es, h, it, hit => by
    simp only [bpsOK, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.dropLast_cons_of_ne_nil (by simp)] at hit
    rcases List.mem_cons.1 hit with rfl | hit
    · exact ⟨e, h.1.1, h.1.2⟩
    · exact bpsOK_sound (it₁ :: rest) es h.2 it hit
  | [], _ :: _, h, _, _ => by simp [bpsOK] at h
  | [_], _ :: _, h, _, _ => by simp [bpsOK] at h
  | _ :: _ :: _, [], h, _, _ => by simp [bpsOK] at h

/-! ### Unpacking the check -/

section Unpack

variable {z : Zone}

/-- The facts of `zoneOK`. -/
structure ZoneFacts (z : Zone) : Prop where
  lbot : z.bot.length = z.rects.length
  ltop : z.top.length = z.rects.length
  lleft : z.left.length = z.rects.length
  lright : z.right.length = z.rects.length
  lcover : z.cover.length = z.pedges.length
  pbd : ∀ e ∈ z.pedges, e.1.1 < z.NX ∧ e.2.1 < z.NX ∧ e.1.2 < z.NY ∧ e.2.2 < z.NY
  box : z.L < z.NX ∧ z.R < z.NX ∧ z.F < z.NY ∧ z.T < z.NY
  pos : 0 < z.rects.length
  left0 : z.left.getD 0 (some ([], [])) = none
  rightLast : z.right.getD (z.rects.length - 1) (some ([], [])) = none
  rect : ∀ k < z.rects.length, rectOK z k = true
  tiles : tilesOK z z.L z.topTiles z.R = true
  cover : ∀ e < z.pedges.length,
    coverOK z (z.pedges.getD e ((0, 0), (0, 0))) (z.cover.getD e []) = true

theorem zoneFacts (h : zoneOK z = true) : ZoneFacts z := by
  simp only [zoneOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem ZoneFacts.pedge_bd (hz : ZoneFacts z) {e : ℕ} (he : e < z.pedges.length) :
    let s := z.pedges.getD e ((0, 0), (0, 0))
    s.1.1 < z.NX ∧ s.2.1 < z.NX ∧ s.1.2 < z.NY ∧ s.2.2 < z.NY := by
  intro s
  exact hz.pbd s (by simp only [s]; rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he)

/-- The facts of `rectOK`. -/
theorem rectOK_facts {k : ℕ} (h : rectOK z k = true) :
    let r := z.rects.getD k GRect.default
    let e := z.pedges.getD (z.bot.getD k 0) ((0, 0), (0, 0))
    r.1 < r.2.1 ∧ r.2.2.1 < r.2.2.2 ∧ r.2.1 < z.NX ∧ r.2.2.2 < z.NY ∧
      z.bot.getD k 0 < z.pedges.length ∧ (z.L ≤ r.1 ∧ r.2.1 ≤ z.R ∧ r.2.2.2 ≤ z.T) ∧
      onSegB (r.1, r.2.2.1) e = true ∧
      onSegB (r.2.1, r.2.2.1) e = true ∧ topOK z r (z.top.getD k none) = true ∧
      sideOK z r true (z.left.getD k none) = true ∧ sideOK z r false (z.right.getD k none) = true := by
  simp only [rectOK, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

end Unpack

/-! ### Sides -/

section Sides

variable {z : Zone} {φ ψ : ℕ → ℝ}

theorem mem_zoneUnion {r : GRect} (hr : r ∈ z.rects) (hx : r.1 < r.2.1) (hy : r.2.2.1 < r.2.2.2)
    (hφ : φ r.1 < φ r.2.1) (hψ : ψ r.2.2.1 < ψ r.2.2.2) {p : Point}
    (hp : φ r.1 ≤ p.1 ∧ p.1 ≤ φ r.2.1 ∧ ψ r.2.2.1 ≤ p.2 ∧ p.2 ≤ ψ r.2.2.2) :
    p ∈ zoneUnion φ ψ z := by
  refine mem_pieceUnion.2 ⟨grect φ ψ r, List.mem_map.2 ⟨r, hr, rfl⟩, ?_⟩
  rw [grect, piece_rectP hφ hψ]
  exact hp

theorem getD_mem_rects {k : ℕ} (hk : k < z.rects.length) : z.rects.getD k GRect.default ∈ z.rects := by
  rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

/-- A rectangle of the zone, realised, contains a quadrant of `y` near `y`. -/
def QuadCov (φ ψ : ℕ → ℝ) (z : Zone) (y : Point) (sx sy : Bool) : Prop :=
  ∃ r ∈ z.rects, φ r.1 < φ r.2.1 ∧ ψ r.2.2.1 < ψ r.2.2.2 ∧
    (if sx then φ r.1 ≤ y.1 ∧ y.1 < φ r.2.1 else φ r.1 < y.1 ∧ y.1 ≤ φ r.2.1) ∧
    (if sy then ψ r.2.2.1 ≤ y.2 ∧ y.2 < ψ r.2.2.2 else ψ r.2.2.1 < y.2 ∧ y.2 ≤ ψ r.2.2.2)

theorem interior_of_quadCov {y : Point} (h : ∀ sx sy, QuadCov φ ψ z y sx sy) :
    y ∈ interior (zoneUnion φ ψ z) := by
  apply mem_interior_of_quadrants
  intro sx sy
  obtain ⟨r, hr, h1, h2, hx, hy⟩ := h sx sy
  obtain ⟨δ, hδ, hq⟩ := quadrant_of_rect hx hy
  refine ⟨δ, hδ, fun w hw hwq => ?_⟩
  refine mem_pieceUnion.2 ⟨grect φ ψ r, List.mem_map.2 ⟨r, hr, rfl⟩, ?_⟩
  rw [grect, piece_rectP h1 h2]
  exact hq w hw hwq

end Sides

/-! ### Lateral sides -/

section Lateral

variable {z : Zone} {φ ψ : ℕ → ℝ}

/-- The conclusion of the side lemmas for a point `y`. -/
def SideConcl (φ ψ : ℕ → ℝ) (z : Zone) (y : Point) : Prop :=
  (∃ e < z.pedges.length, y ∈ gseg φ ψ (z.pedges.getD e ((0, 0), (0, 0)))) ∨
    y ∈ interior (zoneUnion φ ψ z) ∨ (y.2 = ψ z.T ∧ φ z.L ≤ y.1 ∧ y.1 ≤ φ z.R) ∨
    ((y.1 = φ z.L ∨ y.1 = φ z.R) ∧ ψ z.F ≤ y.2 ∧ y.2 ≤ ψ z.T)

theorem sideConcl_of_onSeg (hz : ZoneFacts z) (hφ : StrictMonoOn φ (Iio z.NX))
    (hψ : StrictMonoOn ψ (Iio z.NY)) {p : ℕ × ℕ} {e : ℕ} (he : e < z.pedges.length)
    (hp1 : p.1 < z.NX) (hp2 : p.2 < z.NY) (h : onSegB p (z.pedges.getD e ((0, 0), (0, 0))) = true) :
    SideConcl φ ψ z (gpt φ ψ p) := by
  obtain ⟨b1, b2, b3, b4⟩ := hz.pedge_bd he
  exact Or.inl ⟨e, he, onSegB_sound hφ hψ h hp1 hp2 b1 b2 b3 b4⟩

theorem zone_lateral (hz : ZoneFacts z) (hφ : StrictMonoOn φ (Iio z.NX))
    (hψ : StrictMonoOn ψ (Iio z.NY)) {k : ℕ} (hk : k < z.rects.length) (isLeft : Bool) {s : ℝ}
    (hs1 : ψ (z.rects.getD k GRect.default).2.2.1 ≤ s)
    (hs2 : s ≤ ψ (z.rects.getD k GRect.default).2.2.2) :
    SideConcl φ ψ z (φ (if isLeft then (z.rects.getD k GRect.default).1
      else (z.rects.getD k GRect.default).2.1), s) := by
  set r := z.rects.getD k GRect.default with hr
  obtain ⟨hr1, hr2, hr3, hr4, hb, -, hb1, hb2, htop, hsl, hsr⟩ := rectOK_facts (hz.rect k hk)
  rw [← hr] at hr1 hr2 hr3 hr4 hb1 hb2 htop hsl hsr
  set x := if isLeft then r.1 else r.2.1 with hx
  have hxN : x < z.NX := by rw [hx]; split <;> omega
  have hy0 : r.2.2.1 < z.NY := by omega
  have hxb : onSegB (x, r.2.2.1) (z.pedges.getD (z.bot.getD k 0) ((0, 0), (0, 0))) = true := by
    rw [hx]; split
    · exact hb1
    · exact hb2
  -- the two corners
  have hcorner0 : SideConcl φ ψ z (φ x, ψ r.2.2.1) :=
    sideConcl_of_onSeg hz hφ hψ hb hxN hy0 hxb
  have hcorner1 : SideConcl φ ψ z (φ x, ψ r.2.2.2) := by
    cases ht : z.top.getD k none with
    | some t =>
      rw [ht] at htop
      simp only [topOK, Bool.and_eq_true, decide_eq_true_eq] at htop
      obtain ⟨⟨htl, ht1⟩, ht2⟩ := htop
      refine sideConcl_of_onSeg (p := (x, r.2.2.2)) hz hφ hψ htl hxN hr4 ?_
      rw [hx]; split
      · exact ht1
      · exact ht2
    | none =>
      rw [ht] at htop
      simp only [topOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at htop
      obtain ⟨⟨hT, hL⟩, hR⟩ := htop
      refine Or.inr (Or.inr (Or.inl ⟨by rw [hT], ?_, ?_⟩))
      · have : z.L ≤ x := by rw [hx]; split <;> omega
        exact hφ.monotoneOn hz.box.1 hxN this
      · have : x ≤ z.R := by rw [hx]; split <;> omega
        exact hφ.monotoneOn hxN hz.box.2.1 this
  -- the side certificate
  have hside : sideOK z r isLeft (if isLeft then z.left.getD k none else z.right.getD k none) =
      true := by cases isLeft <;> simpa
  cases hc : (if isLeft then z.left.getD k none else z.right.getD k none) with
  | none =>
    rw [hc] at hside
    simp only [sideOK, Bool.and_eq_true, beq_iff_eq] at hside
    obtain ⟨⟨hxL, hF⟩, hT⟩ := hside
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
    · rw [← hx] at hxL
      cases isLeft
      · right; simp only [Bool.false_eq_true, ↓reduceIte] at hxL; rw [hxL]
      · left; simp only [↓reduceIte] at hxL; rw [hxL]
    · rw [← hF]; exact hs1
    · rw [← hT]; exact hs2
  | some c =>
    obtain ⟨items, bps⟩ := c
    rw [hc] at hside
    simp only [sideOK, Bool.and_eq_true, List.all_eq_true] at hside
    obtain ⟨⟨hch, hit⟩, hbps⟩ := hside
    rw [← hx] at hit hbps
    have hlt : ∀ it ∈ items, it.1 < it.2.1 := by
      intro it hi
      have := hit it hi
      simp only [itemOK, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    obtain ⟨-, hbd⟩ := chainItems_bounds items _ _ hch hlt
    rcases items_locate hψ items _ _ hch hlt hr4 s hs1 hs2 with
      h | h | ⟨it, hi, h1, h2⟩ | ⟨it, hi, h⟩
    · rw [h]; exact hcorner0
    · rw [h]; exact hcorner1
    · have hio := hit it hi
      have hb' := hbd it hi
      have hl := hlt it hi
      have ha : it.1 < z.NY := by omega
      have hb'' : it.2.1 < z.NY := by omega
      simp only [itemOK, Bool.and_eq_true, decide_eq_true_eq] at hio
      obtain ⟨-, hkind⟩ := hio
      cases hkd : it.2.2 with
      | edge e =>
        rw [hkd] at hkind
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hkind
        obtain ⟨⟨he, he1⟩, he2⟩ := hkind
        obtain ⟨b1, b2, b3, b4⟩ := hz.pedge_bd he
        have p1 := onSegB_sound hφ hψ he1 hxN ha b1 b2 b3 b4
        have p2 := onSegB_sound hφ hψ he2 hxN hb'' b1 b2 b3 b4
        refine Or.inl ⟨e, he, segment_subset_of_ends p1 p2 ?_⟩
        exact mem_segment_vert (min_le_left _ _ |>.trans h1.le) (h2.le.trans (le_max_right _ _))
      | rect k' =>
        rw [hkd] at hkind
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hkind
        obtain ⟨⟨⟨⟨hk', hxk⟩, hk1⟩, hk2⟩, hk3⟩ := hkind
        set r' := z.rects.getD k' GRect.default with hr'
        obtain ⟨hr1', hr2', hr3', hr4', -⟩ := rectOK_facts (hz.rect k' hk')
        rw [← hr'] at hr1' hr2' hr3' hr4'
        have hmem := getD_mem_rects hk
        have hmem' := getD_mem_rects hk'
        rw [← hr] at hmem; rw [← hr'] at hmem'
        -- the real coordinates
        have m := fun {a b : ℕ} (ha : a < z.NX) (hb : b < z.NX) (hab : a < b) => hφ ha hb hab
        have n := fun {a b : ℕ} (ha : a < z.NY) (hb : b < z.NY) (hab : a < b) => hψ ha hb hab
        have nle := fun {a b : ℕ} (ha : a < z.NY) (hb : b < z.NY) (hab : a ≤ b) =>
          hψ.monotoneOn ha hb hab
        have q0 : ψ r.2.2.1 < s := lt_of_le_of_lt (nle hy0 ha hb'.1) h1
        have q1 : s < ψ r.2.2.2 := lt_of_lt_of_le h2 (nle hb'' hr4 hb'.2)
        have hy0' : r'.2.2.1 < z.NY := lt_trans hr2' hr4'
        have hx0' : r'.1 < z.NX := lt_trans hk1 hr3'
        have q0' : ψ r'.2.2.1 < s := lt_of_le_of_lt (nle hy0' ha hk2) h1
        have q1' : s < ψ r'.2.2.2 := lt_of_lt_of_le h2 (nle hb'' hr4' hk3)
        have own : φ r.1 < φ r.2.1 := m (by omega) hr3 hr1
        have own' : φ r'.1 < φ r'.2.1 := m hx0' hr3' hk1
        have ownY : ψ r.2.2.1 < ψ r.2.2.2 := n hy0 hr4 hr2
        have ownY' : ψ r'.2.2.1 < ψ r'.2.2.2 := n hy0' hr4' hr2'
        refine Or.inr (Or.inl (interior_of_quadCov fun sx sy => ?_))
        cases isLeft
        · -- right side: own rectangle to the west, `r'` to the east (`r'.1 = x = r.2.1`)
          have e : φ r'.1 = φ r.2.1 :=
            congrArg φ (((by simpa using hxk) : r'.1 = x).trans (by simpa using hx))
          cases sx
          · refine ⟨r, hmem, own, ownY, ⟨own, le_rfl⟩, ?_⟩
            cases sy <;> simp <;> constructor <;> linarith
          · refine ⟨r', hmem', own', ownY', ⟨e.le, e ▸ own'⟩, ?_⟩
            cases sy <;> simp <;> constructor <;> linarith
        · -- left side: own rectangle to the east, `r'` to the west (`r'.2.1 = x = r.1`)
          have e : φ r'.2.1 = φ r.1 :=
            congrArg φ (((by simpa using hxk) : r'.2.1 = x).trans (by simpa using hx))
          cases sx
          · refine ⟨r', hmem', own', ownY', ⟨e ▸ own', e.ge⟩, ?_⟩
            cases sy <;> simp <;> constructor <;> linarith
          · refine ⟨r, hmem, own, ownY, ⟨le_rfl, own⟩, ?_⟩
            cases sy <;> simp <;> constructor <;> linarith
    · obtain ⟨e, he, hon⟩ := bpsOK_sound items bps hbps it hi
      have hi' : it ∈ items := List.mem_of_mem_dropLast hi
      have hb' := hbd it hi'
      rw [h]
      exact sideConcl_of_onSeg hz hφ hψ he hxN (by omega) hon

end Lateral

/-! ### The zone theorems -/

section Main

variable {z : Zone} {φ ψ : ℕ → ℝ}

theorem mem_zonePieces {K : Polygon} (hK : K ∈ zonePieces φ ψ z) :
    ∃ k < z.rects.length, K = grect φ ψ (z.rects.getD k GRect.default) := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hK
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  exact ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk]⟩

/-- **Zones: the rectangles are pieces.** -/
theorem zone_isPiece (hz : ZoneFacts z) (hφ : StrictMonoOn φ (Iio z.NX))
    (hψ : StrictMonoOn ψ (Iio z.NY)) {K : Polygon} (hK : K ∈ zonePieces φ ψ z) : IsPiece K := by
  obtain ⟨k, hk, rfl⟩ := mem_zonePieces hK
  obtain ⟨hr1, hr2, hr3, hr4, -⟩ := rectOK_facts (hz.rect k hk)
  exact isPiece_rectP (hφ (by simp only [mem_Iio]; omega) hr3 hr1)
    (hψ (by simp only [mem_Iio]; omega) hr4 hr2)

/-- **Zones: sides.** -/
theorem zone_side (hz : ZoneFacts z) (hφ : StrictMonoOn φ (Iio z.NX))
    (hψ : StrictMonoOn ψ (Iio z.NY)) {K : Polygon} (hK : K ∈ zonePieces φ ψ z) {j : ℕ}
    (hj : j < K.n) {y : Point} (hy : y ∈ K.edge j) : SideConcl φ ψ z y := by
  obtain ⟨k, hk, rfl⟩ := mem_zonePieces hK
  set r := z.rects.getD k GRect.default with hr
  obtain ⟨hr1, hr2, hr3, hr4, hb, -, hb1, hb2, htop, -, -⟩ := rectOK_facts (hz.rect k hk)
  rw [← hr] at hr1 hr2 hr3 hr4 hb1 hb2 htop
  have hj4 : j < 4 := by simpa [grect, rectP_n] using hj
  have hx0 : r.1 < z.NX := by omega
  have hy0 : r.2.2.1 < z.NY := by omega
  have hyle : ψ r.2.2.1 ≤ ψ r.2.2.2 := hψ.monotoneOn hy0 hr4 hr2.le
  have hxle : φ r.1 ≤ φ r.2.1 := hφ.monotoneOn hx0 hr3 hr1.le
  unfold grect at hy
  rw [rectP_edge hj4] at hy
  obtain ⟨b1, b2, b3, b4⟩ := hz.pedge_bd hb
  interval_cases j
  · -- bottom
    simp only [↓reduceIte] at hy
    have p1 := onSegB_sound hφ hψ hb1 hx0 hy0 b1 b2 b3 b4
    have p2 := onSegB_sound hφ hψ hb2 hr3 hy0 b1 b2 b3 b4
    exact Or.inl ⟨_, hb, segment_subset_of_ends p1 p2 hy⟩
  · -- right side
    simp only [one_ne_zero, ↓reduceIte] at hy
    have e1 := vseg_fst hy
    have e2 := vseg_snd hyle hy
    have hyy : y = (φ r.2.1, y.2) := Prod.ext e1 rfl
    rw [hyy]
    exact zone_lateral hz hφ hψ hk false e2.1 e2.2
  · -- top
    simp only [OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte] at hy
    cases ht : z.top.getD k none with
    | some t =>
      rw [ht] at htop
      simp only [topOK, Bool.and_eq_true, decide_eq_true_eq] at htop
      obtain ⟨⟨htl, ht1⟩, ht2⟩ := htop
      obtain ⟨c1, c2, c3, c4⟩ := hz.pedge_bd htl
      have p1 := onSegB_sound hφ hψ ht1 hx0 hr4 c1 c2 c3 c4
      have p2 := onSegB_sound hφ hψ ht2 hr3 hr4 c1 c2 c3 c4
      exact Or.inl ⟨_, htl, segment_subset_of_ends p2 p1 hy⟩
    | none =>
      rw [ht] at htop
      simp only [topOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at htop
      obtain ⟨⟨hT, hL⟩, hR⟩ := htop
      have e1 := seg_fst_ge hy
      have e2 := seg_fst_le hy
      have e3 := seg_snd_ge hy
      have e4 := seg_snd_le hy
      simp only [min_self, max_self] at e3 e4
      rw [min_eq_right hxle] at e1
      rw [max_eq_left hxle] at e2
      refine Or.inr (Or.inr (Or.inl ⟨by rw [← hT]; linarith, ?_, ?_⟩))
      · exact le_trans (hφ.monotoneOn hz.box.1 hx0 hL) e1
      · exact le_trans e2 (hφ.monotoneOn hr3 hz.box.2.1 hR)
  · -- left side
    rw [if_neg (by decide : (3 : ℕ) ≠ 0), if_neg (by decide : (3 : ℕ) ≠ 1),
      if_neg (by decide : (3 : ℕ) ≠ 2), Geometry.segment_comm] at hy
    have e1 := vseg_fst hy
    have e2 := vseg_snd hyle hy
    have hyy : y = (φ r.1, y.2) := Prod.ext e1 rfl
    rw [hyy]
    exact zone_lateral hz hφ hψ hk true e2.1 e2.2

/-- **Zones: the box top is tiled.**  Near every point of the box top the two lower quadrants
are covered (except beyond the box ends). -/
theorem zone_tiles (hz : ZoneFacts z) (hφ : StrictMonoOn φ (Iio z.NX))
    (hψ : StrictMonoOn ψ (Iio z.NY)) :
    ∀ (tiles : List ℕ) (c : ℕ), tilesOK z c tiles z.R = true → c < z.NX → ∀ x : ℝ, φ c ≤ x →
      x ≤ φ z.R → (x < φ z.R → QuadCov φ ψ z (x, ψ z.T) true false) ∧
        (φ c < x → QuadCov φ ψ z (x, ψ z.T) false false)
  | [], _, h, _, _, _, _ => by simp [tilesOK] at h
  | k :: rest, c, h, hc, x, h1, h2 => by
    simp only [tilesOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨hk, hc'⟩, hT⟩, hrest⟩ := h
    set r := z.rects.getD k GRect.default with hr
    obtain ⟨hr1, hr2, hr3, hr4, -⟩ := rectOK_facts (hz.rect k hk)
    rw [← hr] at hr1 hr2 hr3 hr4
    have hmem := getD_mem_rects hk
    rw [← hr] at hmem
    have own : φ r.1 < φ r.2.1 := hφ (by simp only [mem_Iio]; omega) hr3 hr1
    have ownY : ψ r.2.2.1 < ψ r.2.2.2 := hψ (by simp only [mem_Iio]; omega) hr4 hr2
    rw [hT] at ownY
    have hcov : ∀ sx, (if sx then φ r.1 ≤ x ∧ x < φ r.2.1 else φ r.1 < x ∧ x ≤ φ r.2.1) →
        QuadCov φ ψ z (x, ψ z.T) sx false := by
      intro sx hsx
      refine ⟨r, hmem, own, by rw [hT]; exact ownY, hsx, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hT]; exact ⟨ownY, le_rfl⟩
    rw [hc'] at own hcov
    by_cases hrn : rest = []
    · simp only [hrn, ↓reduceIte, beq_iff_eq] at hrest
      rw [hrest] at own hcov
      exact ⟨fun hx => hcov true ⟨h1, hx⟩, fun hx => hcov false ⟨hx, h2⟩⟩
    · simp only [hrn, ↓reduceIte] at hrest
      have ih := zone_tiles hz hφ hψ rest r.2.1 hrest hr3
      rcases lt_trichotomy x (φ r.2.1) with hx | hx | hx
      · exact ⟨fun _ => hcov true ⟨h1, hx⟩, fun hx' => hcov false ⟨hx', hx.le⟩⟩
      · refine ⟨fun hx' => (ih x hx.ge h2).1 hx', fun hx' => hcov false ⟨hx', hx.le⟩⟩
      · exact ⟨fun hx' => (ih x hx.le h2).1 hx', fun _ => (ih x hx.le h2).2 hx⟩

/-- **Zones: the left box side** is the left side of the first rectangle. -/
theorem zone_left (hz : ZoneFacts z) (hφ : StrictMonoOn φ (Iio z.NX))
    (hψ : StrictMonoOn ψ (Iio z.NY)) {s : ℝ} (h1 : ψ z.F < s) (h2 : s ≤ ψ z.T) :
    QuadCov φ ψ z (φ z.L, s) true false ∧ (s < ψ z.T → QuadCov φ ψ z (φ z.L, s) true true) := by
  have hk : 0 < z.rects.length := hz.pos
  set r := z.rects.getD 0 GRect.default with hr
  obtain ⟨hr1, hr2, hr3, hr4, -, -, -, -, -, hsl, -⟩ := rectOK_facts (hz.rect 0 hk)
  rw [← hr] at hr1 hr2 hr3 hr4 hsl
  have e0 : z.left.getD 0 none = z.left.getD 0 (some ([], [])) := by
    have : 0 < z.left.length := by rw [hz.lleft]; exact hk
    rw [List.getD_eq_getElem _ _ this, List.getD_eq_getElem _ _ this]
  rw [e0, hz.left0] at hsl
  simp only [sideOK, Bool.and_eq_true, beq_iff_eq, ↓reduceIte] at hsl
  obtain ⟨⟨hL, hF⟩, hT⟩ := hsl
  have hmem := getD_mem_rects hk
  rw [← hr] at hmem
  have own : φ r.1 < φ r.2.1 := hφ (by simp only [mem_Iio]; omega) hr3 hr1
  have ownY : ψ r.2.2.1 < ψ r.2.2.2 := hψ (by simp only [mem_Iio]; omega) hr4 hr2
  rw [hL] at own; rw [hF, hT] at ownY
  refine ⟨⟨r, hmem, by rw [hL]; exact own, by rw [hF, hT]; exact ownY, ?_, ?_⟩, fun h3 =>
    ⟨r, hmem, by rw [hL]; exact own, by rw [hF, hT]; exact ownY, ?_, ?_⟩⟩
  · simp only [↓reduceIte]; rw [hL]; exact ⟨le_rfl, own⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hF, hT]; exact ⟨h1, h2⟩
  · simp only [↓reduceIte]; rw [hL]; exact ⟨le_rfl, own⟩
  · simp only [↓reduceIte]; rw [hF, hT]; exact ⟨h1.le, h3⟩

/-- **Zones: the right box side** is the right side of the last rectangle. -/
theorem zone_right (hz : ZoneFacts z) (hφ : StrictMonoOn φ (Iio z.NX))
    (hψ : StrictMonoOn ψ (Iio z.NY)) {s : ℝ} (h1 : ψ z.F < s) (h2 : s ≤ ψ z.T) :
    QuadCov φ ψ z (φ z.R, s) false false ∧ (s < ψ z.T → QuadCov φ ψ z (φ z.R, s) false true) := by
  have hk : z.rects.length - 1 < z.rects.length := by have := hz.pos; omega
  set r := z.rects.getD (z.rects.length - 1) GRect.default with hr
  obtain ⟨hr1, hr2, hr3, hr4, -, -, -, -, -, -, hsr⟩ := rectOK_facts (hz.rect _ hk)
  rw [← hr] at hr1 hr2 hr3 hr4 hsr
  have e0 : z.right.getD (z.rects.length - 1) none =
      z.right.getD (z.rects.length - 1) (some ([], [])) := by
    have : z.rects.length - 1 < z.right.length := by rw [hz.lright]; exact hk
    rw [List.getD_eq_getElem _ _ this, List.getD_eq_getElem _ _ this]
  rw [e0, hz.rightLast] at hsr
  simp only [sideOK, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, ↓reduceIte] at hsr
  obtain ⟨⟨hR, hF⟩, hT⟩ := hsr
  have hmem := getD_mem_rects hk
  rw [← hr] at hmem
  have own : φ r.1 < φ r.2.1 := hφ (by simp only [mem_Iio]; omega) hr3 hr1
  have ownY : ψ r.2.2.1 < ψ r.2.2.2 := hψ (by simp only [mem_Iio]; omega) hr4 hr2
  rw [hR] at own; rw [hF, hT] at ownY
  refine ⟨⟨r, hmem, by rw [hR]; exact own, by rw [hF, hT]; exact ownY, ?_, ?_⟩, fun h3 =>
    ⟨r, hmem, by rw [hR]; exact own, by rw [hF, hT]; exact ownY, ?_, ?_⟩⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hR]; exact ⟨own, le_rfl⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hF, hT]; exact ⟨h1, h2⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hR]; exact ⟨own, le_rfl⟩
  · simp only [↓reduceIte]; rw [hF, hT]; exact ⟨h1.le, h3⟩

theorem coverRun_sound {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Iio N)) :
    ∀ (l : List (ℕ × ℕ)) (lo hi : ℕ), coverRun l lo hi = true → (∀ i ∈ l, i.1 < N ∧ i.2 < N) →
      lo < N → hi < N → ∀ t : ℝ, f lo ≤ t → t ≤ f hi → ∃ i ∈ l, f i.1 ≤ t ∧ t ≤ f i.2
  | [], _, _, h, _, _, _, _, _, _ => by simp [coverRun] at h
  | i :: rest, lo, hi, h, hb, hlo, hhi, t, h1, h2 => by
    simp only [coverRun, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨hi1, h'⟩ := h
    obtain ⟨b1, b2⟩ := hb i (by simp)
    by_cases ht : t ≤ f i.2
    · exact ⟨i, by simp, le_trans (hf.monotoneOn b1 hlo hi1) h1, ht⟩
    · push Not at ht
      rcases h' with h' | h'
      · exact absurd (lt_of_le_of_lt h2 (lt_of_le_of_lt (hf.monotoneOn hhi b2 h') ht)) (lt_irrefl _)
      · obtain ⟨j, hj, hj'⟩ := coverRun_sound hf rest i.2 hi h'
          (fun j hj => hb j (List.mem_cons_of_mem _ hj)) b2 hhi t ht.le h2
        exact ⟨j, List.mem_cons_of_mem _ hj, hj'⟩

theorem monotoneOn_min {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Iio N)) {a b : ℕ} (ha : a < N)
    (hb : b < N) : f (min a b) = min (f a) (f b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (hf.monotoneOn ha hb h)]
  · rw [min_eq_right h, min_eq_right (hf.monotoneOn hb ha h)]

theorem monotoneOn_max {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Iio N)) {a b : ℕ} (ha : a < N)
    (hb : b < N) : f (max a b) = max (f a) (f b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (hf.monotoneOn ha hb h)]
  · rw [max_eq_left h, max_eq_left (hf.monotoneOn hb ha h)]

/-- **Zones: the boundary segments are covered.** -/
theorem zone_cover (hz : ZoneFacts z) (hφ : StrictMonoOn φ (Iio z.NX))
    (hψ : StrictMonoOn ψ (Iio z.NY)) {e : ℕ} (he : e < z.pedges.length) :
    gseg φ ψ (z.pedges.getD e ((0, 0), (0, 0))) ⊆ zoneUnion φ ψ z := by
  have hc := hz.cover e he
  obtain ⟨c1, c2, c3, c4⟩ := hz.pedge_bd he
  set g := z.pedges.getD e ((0, 0), (0, 0)) with hg
  set ks := z.cover.getD e [] with hks
  intro y hy
  have rfacts : ∀ k < z.rects.length, let r := z.rects.getD k GRect.default
      r.1 < z.NX ∧ r.2.1 < z.NX ∧ r.2.2.1 < z.NY ∧ r.2.2.2 < z.NY ∧
        φ r.1 < φ r.2.1 ∧ ψ r.2.2.1 < ψ r.2.2.2 ∧ r.1 < r.2.1 ∧ r.2.2.1 < r.2.2.2 := by
    intro k hk
    obtain ⟨hr1, hr2, hr3, hr4, -⟩ := rectOK_facts (hz.rect k hk)
    exact ⟨by omega, hr3, by omega, hr4, hφ (by simp only [mem_Iio]; omega) hr3 hr1,
      hψ (by simp only [mem_Iio]; omega) hr4 hr2, hr1, hr2⟩
  unfold gseg gpt at hy
  unfold coverOK at hc
  split at hc
  · -- vertical
    rename_i hv
    simp only [coverV, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hall, hrun⟩ := hc
    rw [hv] at hy
    have hy1 := vseg_fst hy
    have e3 := seg_snd_ge hy
    have e4 := seg_snd_le hy
    simp only at e3 e4
    rw [← monotoneOn_min hψ c3 c4] at e3
    rw [← monotoneOn_max hψ c3 c4] at e4
    obtain ⟨i, hi, hi1, hi2⟩ := coverRun_sound hψ _ _ _ hrun (by
      intro i hi
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hi
      have := rfacts k (hall k hk).1.1
      exact ⟨this.2.2.1, this.2.2.2.1⟩) (by omega) (by omega) y.2 e3 e4
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hi
    obtain ⟨⟨hkl, hx1⟩, hx2⟩ := hall k hk
    have f := rfacts k hkl
    refine mem_zoneUnion (getD_mem_rects hkl) f.2.2.2.2.2.2.1 f.2.2.2.2.2.2.2 f.2.2.2.2.1
      f.2.2.2.2.2.1 ⟨?_, ?_, hi1, hi2⟩
    · rw [hy1]; exact hφ.monotoneOn f.1 c2 (hv ▸ hx1)
    · rw [hy1]; exact hφ.monotoneOn c2 f.2.1 (hv ▸ hx2)
  · split at hc
    · -- horizontal
      rename_i _ hh
      simp only [coverH, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hall, hrun⟩ := hc
      rw [hh] at hy
      have hy2 : y.2 = ψ g.2.2 := by
        have e3 := seg_snd_ge hy; have e4 := seg_snd_le hy
        simp only [min_self, max_self] at e3 e4; linarith
      have e3 := seg_fst_ge hy
      have e4 := seg_fst_le hy
      simp only at e3 e4
      rw [← monotoneOn_min hφ c1 c2] at e3
      rw [← monotoneOn_max hφ c1 c2] at e4
      obtain ⟨i, hi, hi1, hi2⟩ := coverRun_sound hφ _ _ _ hrun (by
        intro i hi
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hi
        have := rfacts k (hall k hk).1.1
        exact ⟨this.1, this.2.1⟩) (by omega) (by omega) y.1 e3 e4
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hi
      obtain ⟨⟨hkl, hy1'⟩, hy2'⟩ := hall k hk
      have f := rfacts k hkl
      refine mem_zoneUnion (getD_mem_rects hkl) f.2.2.2.2.2.2.1 f.2.2.2.2.2.2.2 f.2.2.2.2.1
        f.2.2.2.2.2.1 ⟨hi1, hi2, ?_, ?_⟩
      · rw [hy2]; exact hψ.monotoneOn f.2.2.1 c4 (hh ▸ hy1')
      · rw [hy2]; exact hψ.monotoneOn c4 f.2.2.2.1 (hh ▸ hy2')
    · simp at hc

/-- **Zones: the rectangles lie in the box.** -/
theorem zone_in_box (hz : ZoneFacts z) (hφ : StrictMonoOn φ (Iio z.NX))
    (hψ : StrictMonoOn ψ (Iio z.NY)) {K : Polygon} (hK : K ∈ zonePieces φ ψ z) :
    ∀ p ∈ piece K, φ z.L ≤ p.1 ∧ p.1 ≤ φ z.R ∧ p.2 ≤ ψ z.T := by
  obtain ⟨k, hk, rfl⟩ := mem_zonePieces hK
  obtain ⟨hr1, hr2, hr3, hr4, -, ⟨hL, hR, hT⟩, -⟩ := rectOK_facts (hz.rect k hk)
  intro p hp
  rw [grect, piece_rectP (hφ (by simp only [mem_Iio]; omega) hr3 hr1)
    (hψ (by simp only [mem_Iio]; omega) hr4 hr2)] at hp
  obtain ⟨p1, p2, p3, p4⟩ := hp
  exact ⟨le_trans (hφ.monotoneOn hz.box.1 (by simp only [mem_Iio]; omega) hL) p1,
    le_trans p2 (hφ.monotoneOn hr3 hz.box.2.1 hR), le_trans p4 (hψ.monotoneOn hr4 hz.box.2.2.2 hT)⟩

end Main

end

end ArtGallery.Orthogonal.Hard
