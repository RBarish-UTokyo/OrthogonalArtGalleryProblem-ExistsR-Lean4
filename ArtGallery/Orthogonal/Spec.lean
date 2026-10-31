module

public import ArtGallery.Spec

/-!
# Orthogonal galleries — specification

A polygon is *orthogonal* (rectilinear) if every edge is horizontal or vertical.  The three
orthogonal art gallery problems are the restrictions of `AGP`, `AGPPointBoundary` and
`AGPBoundaryPoint` (`ArtGallery/Spec.lean`) to orthogonal polygons: the instance format, the
notion of a simple polygon and the three guarding notions are unchanged.
-/

@[expose] public section

namespace ArtGallery

open Complexity

namespace Polygon

variable (P : Polygon)

/-- The polygon is *orthogonal* (rectilinear): every edge is horizontal or vertical, i.e. the two
endpoints of every edge have the same first or the same second coordinate. -/
def Orthogonal : Prop :=
  ∀ i, i < P.n → (P.vtx i).1 = (P.vtx ((i + 1) % P.n)).1 ∨
    (P.vtx i).2 = (P.vtx ((i + 1) % P.n)).2

end Polygon

/-- **The orthogonal art gallery problem**: the instances of `AGP` whose polygon is orthogonal. -/
def AGPOrth : Language := fun w => ∃ (V : List FracPoint) (g : ℕ),
  encodeAGP V g = w ∧ (∀ p ∈ V, p.Valid) ∧
    (Polygon.mk (V.map FracPoint.toPoint)).Simple ∧
    (Polygon.mk (V.map FracPoint.toPoint)).Orthogonal ∧
    (Polygon.mk (V.map FracPoint.toPoint)).HasGuardSetOfCard g

/-- **The orthogonal point-boundary art gallery problem**: the instances of `AGPPointBoundary`
whose polygon is orthogonal. -/
def AGPOrthPointBoundary : Language := fun w => ∃ (V : List FracPoint) (g : ℕ),
  encodeAGP V g = w ∧ (∀ p ∈ V, p.Valid) ∧
    (Polygon.mk (V.map FracPoint.toPoint)).Simple ∧
    (Polygon.mk (V.map FracPoint.toPoint)).Orthogonal ∧
    (Polygon.mk (V.map FracPoint.toPoint)).HasBoundaryGuardSetOfCard g

/-- **The orthogonal boundary-point art gallery problem**: the instances of `AGPBoundaryPoint`
whose polygon is orthogonal. -/
def AGPOrthBoundaryPoint : Language := fun w => ∃ (V : List FracPoint) (g : ℕ),
  encodeAGP V g = w ∧ (∀ p ∈ V, p.Valid) ∧
    (Polygon.mk (V.map FracPoint.toPoint)).Simple ∧
    (Polygon.mk (V.map FracPoint.toPoint)).Orthogonal ∧
    (Polygon.mk (V.map FracPoint.toPoint)).HasGuardSetOnBoundaryOfCard g

end ArtGallery

end
