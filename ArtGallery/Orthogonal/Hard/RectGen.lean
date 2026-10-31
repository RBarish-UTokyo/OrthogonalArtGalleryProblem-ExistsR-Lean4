module

public import ArtGallery.Orthogonal.Hard.RatEq
public import ArtGallery.Stade.RegionGen

/-!
# Regions made of rectangles

Generic tools for describing the region of an orthogonal polygon as a finite union of
axis-parallel rectangles.

* `subset_filled_of_frontier`: a closed bounded set whose frontier lies in the boundary of `P`
  lies in the region (the components of the complement of the boundary are either bounded and
  interior or unbounded and exterior).  This replaces the separation of every piece from every
  edge of `P` in Stade's `filled_eq_of_sides`.
* `filled_eq_of_sides'`: a finite family of pieces covering the boundary, such that every point
  of every side is on the boundary or interior to the union, and which is bounded, has the region
  as its union.
* `rectP x₀ x₁ y₀ y₁`: the rectangle as a convex piece (`isPiece_rectP`, `piece_rectP`).
* `mem_interior_of_quadrants`, `quadrant_of_rect`: a point whose four closed quadrants are, near
  the point, covered by rectangles is an interior point of their union.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade Set Metric Filter Topology

variable {P : Polygon}

/-! ### Bounded sets with frontier on the boundary -/

/-- **A closed bounded set whose frontier lies on the boundary lies in the region.** -/
theorem subset_filled_of_frontier {U : Set Point} (hUc : IsClosed U) (hUb : IsBoundedSet U)
    (hfr : frontier U ⊆ P.boundary) : U ⊆ P.filled := by
  have hint : ∀ x ∈ U, x ∉ P.boundary → x ∈ interior U := by
    intro x hxU hxb
    by_contra hxi
    exact hxb (hfr ⟨subset_closure hxU, hxi⟩)
  intro z hz
  by_cases hzb : z ∈ P.boundary
  · exact Or.inl hzb
  refine (Jordan.mem_filled_iff_bounded P hzb).2 ?_
  have hcover : connectedComponentIn P.boundaryᶜ z ⊆ interior U ∪ Uᶜ := by
    intro x hx
    have hxb : x ∉ P.boundary := connectedComponentIn_subset _ _ hx
    by_cases hxU : x ∈ U
    · exact Or.inl (hint x hxU hxb)
    · exact Or.inr hxU
  have hC := (isPreconnected_connectedComponentIn (F := P.boundaryᶜ) (x := z)).subset_left_of_subset_union
    isOpen_interior hUc.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hcover
    ⟨z, mem_connectedComponentIn (by simpa using hzb), hint z hz hzb⟩
  obtain ⟨R, hR⟩ := hUb
  exact ⟨R, fun p hp => hR p (interior_subset (hC hp))⟩

/-- **Exact region from sides, without separation.** -/
theorem filled_eq_of_sides' (hP : P.Simple) (S : List Polygon) (hpc : ∀ K ∈ S, IsPiece K)
    (hbdd : IsBoundedSet (pieceUnion {K | K ∈ S}))
    (hbd : P.boundary ⊆ pieceUnion {K | K ∈ S})
    (hside : ∀ K ∈ S, ∀ j < K.n, ∀ y ∈ K.edge j,
      y ∈ P.boundary ∨ y ∈ interior (pieceUnion {K | K ∈ S}))
    (hne : (pieceUnion {K | K ∈ S} \ P.boundary).Nonempty) :
    P.filled = pieceUnion {K | K ∈ S} := by
  have hfin : ({K | K ∈ S} : Set Polygon).Finite := S.finite_toSet
  have hfr : frontier (pieceUnion {K | K ∈ S}) ⊆ P.boundary := by
    intro y hy
    by_contra hyb
    have hyU : y ∈ pieceUnion {K | K ∈ S} := (isClosed_pieceUnion hfin).frontier_subset hy
    obtain ⟨K, hKS, hyK⟩ := mem_pieceUnion.1 hyU
    have hnint : y ∉ interior (pieceUnion {K | K ∈ S}) := hy.2
    by_cases hyi : y ∈ interior (piece K)
    · exact hnint (interior_mono (piece_subset_pieceUnion (S := {K | K ∈ S}) hKS) hyi)
    have hyfr : y ∈ frontier (piece K) := ⟨subset_closure hyK, hyi⟩
    obtain ⟨k, hk, hyk⟩ := mem_edge_of_mem_frontier (hpc K hKS) hyfr
    rcases hside K hKS k hk y hyk with h | h
    · exact hyb h
    · exact hnint h
  have hU := subset_filled_of_frontier (isClosed_pieceUnion hfin) hbdd hfr
  exact Polygon.filled_eq_of_frontier_subset hP (isClosed_pieceUnion hfin) hbd hfr hU hne

/-! ### Rectangles -/

/-- The axis-parallel rectangle `[x₀, x₁] × [y₀, y₁]` as a polygon (counterclockwise). -/
def rectP (x₀ x₁ y₀ y₁ : ℝ) : Polygon := quad (x₀, y₀) (x₁, y₀) (x₁, y₁) (x₀, y₁)

theorem isPiece_rectP {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁) :
    IsPiece (rectP x₀ x₁ y₀ y₁) := by
  apply isPiece_quad <;> simp only [det] <;> nlinarith [mul_pos (sub_pos.2 hx) (sub_pos.2 hy)]

theorem piece_rectP {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁) :
    piece (rectP x₀ x₁ y₀ y₁) = {p | x₀ ≤ p.1 ∧ p.1 ≤ x₁ ∧ y₀ ≤ p.2 ∧ p.2 ≤ y₁} := by
  ext p
  rw [rectP, mem_piece_quad]
  simp only [det, mem_ofPred_eq]
  have hx' := sub_pos.2 hx
  have hy' := sub_pos.2 hy
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem rectP_n (x₀ x₁ y₀ y₁ : ℝ) : (rectP x₀ x₁ y₀ y₁).n = 4 := rfl

/-- The sides of a rectangle. -/
theorem rectP_edge {x₀ x₁ y₀ y₁ : ℝ} {j : ℕ} (hj : j < 4) :
    (rectP x₀ x₁ y₀ y₁).edge j =
      if j = 0 then ArtGallery.segment (x₀, y₀) (x₁, y₀)
      else if j = 1 then ArtGallery.segment (x₁, y₀) (x₁, y₁)
      else if j = 2 then ArtGallery.segment (x₁, y₁) (x₀, y₁)
      else ArtGallery.segment (x₀, y₁) (x₀, y₀) := by
  interval_cases j <;> simp [rectP, quad, Polygon.edge, Polygon.vtx, Polygon.n]

/-! ### Quadrants -/

/-- The closed quadrant of `y` with signs `(sx, sy)` (`true` = nonnegative direction). -/
def quadrant (y : Point) (sx sy : Bool) : Set Point :=
  {z | (if sx then y.1 ≤ z.1 else z.1 ≤ y.1) ∧ (if sy then y.2 ≤ z.2 else z.2 ≤ y.2)}

/-- **Quadrants.** If near `y` each of the four closed quadrants of `y` lies in `U`, then `y` is
an interior point of `U`. -/
theorem mem_interior_of_quadrants {U : Set Point} {y : Point}
    (h : ∀ sx sy : Bool, ∃ δ > 0, ∀ z, dist z y < δ → z ∈ quadrant y sx sy → z ∈ U) :
    y ∈ interior U := by
  choose δ hδ hU using h
  set ε := min (min (δ true true) (δ true false)) (min (δ false true) (δ false false))
  have hε : 0 < ε := lt_min (lt_min (hδ _ _) (hδ _ _)) (lt_min (hδ _ _) (hδ _ _))
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨ε, hε, fun z hz => ?_⟩
  rw [mem_ball] at hz
  have hq : z ∈ quadrant y (decide (y.1 ≤ z.1)) (decide (y.2 ≤ z.2)) := by
    simp only [quadrant, mem_ofPred_eq]
    constructor
    · by_cases h1 : y.1 ≤ z.1 <;> simp [h1] <;> linarith
    · by_cases h2 : y.2 ≤ z.2 <;> simp [h2] <;> linarith
  refine hU _ _ z (lt_of_lt_of_le hz ?_) hq
  cases decide (y.1 ≤ z.1) <;> cases decide (y.2 ≤ z.2) <;> simp [ε]

/-- A closed rectangle covers a quadrant of `y` near `y` when `y` lies in the rectangle, strictly
inside in the directions of the quadrant. -/
theorem quadrant_of_rect {x₀ x₁ y₀ y₁ : ℝ} {y : Point} {sx sy : Bool}
    (hx : if sx then x₀ ≤ y.1 ∧ y.1 < x₁ else x₀ < y.1 ∧ y.1 ≤ x₁)
    (hy : if sy then y₀ ≤ y.2 ∧ y.2 < y₁ else y₀ < y.2 ∧ y.2 ≤ y₁) :
    ∃ δ > 0, ∀ z, dist z y < δ → z ∈ quadrant y sx sy →
      z ∈ {p : Point | x₀ ≤ p.1 ∧ p.1 ≤ x₁ ∧ y₀ ≤ p.2 ∧ p.2 ≤ y₁} := by
  have key : ∀ (a lo hi : ℝ) (s : Bool), (if s then lo ≤ a ∧ a < hi else lo < a ∧ a ≤ hi) →
      ∃ δ > 0, ∀ b : ℝ, |b - a| < δ → (if s then a ≤ b else b ≤ a) → lo ≤ b ∧ b ≤ hi := by
    intro a lo hi s hs
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte] at hs ⊢
      refine ⟨a - lo, by linarith, fun b hb hba => ?_⟩
      have := neg_abs_le (b - a)
      constructor <;> linarith
    · simp only [↓reduceIte] at hs ⊢
      refine ⟨hi - a, by linarith, fun b hb hab => ?_⟩
      have := le_abs_self (b - a)
      constructor <;> linarith
  obtain ⟨δ₁, hδ₁, h₁⟩ := key y.1 x₀ x₁ sx hx
  obtain ⟨δ₂, hδ₂, h₂⟩ := key y.2 y₀ y₁ sy hy
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun z hz hq => ?_⟩
  have hd := hz
  rw [Prod.dist_eq] at hd
  have e1 : |z.1 - y.1| < δ₁ := by
    have := le_max_left (dist z.1 y.1) (dist z.2 y.2)
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt this (lt_of_lt_of_le hd (min_le_left _ _))
  have e2 : |z.2 - y.2| < δ₂ := by
    have := le_max_right (dist z.1 y.1) (dist z.2 y.2)
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt this (lt_of_lt_of_le hd (min_le_right _ _))
  obtain ⟨a1, a2⟩ := h₁ z.1 e1 hq.1
  obtain ⟨b1, b2⟩ := h₂ z.2 e2 hq.2
  exact ⟨a1, a2, b1, b2⟩

end

end ArtGallery.Orthogonal.Hard
