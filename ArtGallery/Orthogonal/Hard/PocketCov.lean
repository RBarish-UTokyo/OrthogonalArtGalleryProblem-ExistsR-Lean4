module

public import ArtGallery.Orthogonal.Hard.RatEq
public import ArtGallery.Stade.AdditionCover
public import ArtGallery.Stade.GuardTools

/-!
# Nook pockets: coverage by two guards

A nook pocket is a strictly convex counter-clockwise quadrilateral `lo, dn, up, hi` whose side
`lo hi` lies on the nook line `x = c` and whose side `dn up` (the *mouth*) faces the guards.  If
both guards see every point of the mouth and every nook point lies between the rays from one of
the guards through `dn` and `up` (its *shadows* `π_dn`, `π_up` on the nook line), then the two
guards see the whole pocket (`pocket_cover_two`, from Stade's `pocket_cover`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade

variable {P : Polygon}

/-- **Crossing the mouth.**  A guard `g` on the far side of the mouth line `dn up` (and right of
`dn`, `up`) reaches a nook point `(c, h)` between its two shadows through the mouth. -/
theorem nook_cross {g dn up : Point} {c h : ℝ} (hd : dn.1 < g.1) (hu : up.1 < g.1)
    (hgl : det dn up g < 0) (hsl : 0 < det dn up (c, h)) (h1 : vproj g dn c ≤ h)
    (h2 : h ≤ vproj g up c) : ∃ q ∈ segment dn up, q ∈ segment g (c, h) := by
  refine add_cross hgl hsl ?_
  rw [det_vert g dn c h hd.ne, det_vert g up c h hu.ne]
  have a : (dn.1 - g.1) * (h - vproj g dn c) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have b : 0 ≤ (up.1 - g.1) * (h - vproj g up c) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  exact mul_nonpos_of_nonpos_of_nonneg a b

/-- **A pocket seen by two guards.** -/
theorem pocket_cover_two {lo dn up hi : Point} (h1 : 0 < det lo dn up) (h2 : 0 < det dn up hi)
    (h3 : 0 < det up hi lo) (h4 : 0 < det hi lo dn) (hK : piece (quad lo dn up hi) ⊆ P.filled)
    {ga gb : Point} (hma : ∀ m ∈ segment dn up, P.Sees ga m)
    (hmb : ∀ m ∈ segment dn up, P.Sees gb m)
    (hnook : ∀ s ∈ segment lo hi, (∃ q ∈ segment dn up, q ∈ segment ga s) ∨
      ∃ q ∈ segment dn up, q ∈ segment gb s) :
    ∀ z ∈ piece (quad lo dn up hi), P.Sees ga z ∨ P.Sees gb z := by
  have hcov := pocket_cover (P := P) (Gs := {ga, gb}) h1 h2 h3 h4 hK
    (fun g hg m hm => by
      rcases hg with rfl | rfl
      · exact hma m hm
      · exact hmb m hm)
    (fun s hs => by
      rcases hnook s hs with ⟨q, hq, hqs⟩ | ⟨q, hq, hqs⟩
      · exact ⟨ga, Or.inl rfl, q, hq, hqs⟩
      · exact ⟨gb, Or.inr rfl, q, hq, hqs⟩)
  intro z hz
  obtain ⟨g, hg, hgz⟩ := hcov z hz
  rcases hg with rfl | rfl
  · exact Or.inl hgz
  · exact Or.inr hgz

/-- The nook side of a pocket on a vertical line: its points are `(c, h)`, `lo.2 ≤ h ≤ hi.2`. -/
theorem nook_side_mem {lo hi s : Point} {c : ℝ} (hlo : lo.1 = c) (hhi : hi.1 = c)
    (hlh : lo.2 ≤ hi.2) (hs : s ∈ segment lo hi) : s = (c, s.2) ∧ lo.2 ≤ s.2 ∧ s.2 ≤ hi.2 := by
  have e1 : lo = (c, lo.2) := Prod.ext hlo rfl
  have e2 : hi = (c, hi.2) := Prod.ext hhi rfl
  rw [e1, e2] at hs
  obtain ⟨h1, h2, h3⟩ := (mem_segment_vert_iff hlh).1 hs
  exact ⟨Prod.ext h1 rfl, h2, h3⟩

end

end ArtGallery.Orthogonal.Hard
