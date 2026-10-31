module

public import ArtGallery.Orthogonal.Hard.SpotFar
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Spot certificate checks in parts

As for the pin checks (`PinSplit`), the kernel check `spotFarB … = true` of a large spot
certificate does not fit in memory as one declaration.  `spotFarB_of_parts` assembles it from the
head conditions (`spotHeadB`) and the certificate check `LCert.ok`, which is itself assembled from
`LCert.okBase` and propagation ranges (`LCert.ok_of_parts`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

/-- The conditions of `spotFarB` other than the certificate check. -/
def spotHeadB (D : GData) (i : ℕ) (T : TCert) : Bool :=
  decide (D.sps.getD i LR.dflt = T.A) && decide (T.cones.length = (groupLR D.gs).length) &&
    match T.C with
    | none => true
    | some K => rightOfBA T.A K (-10) (-1 / 4, 2) yMax

/-- **A spot check from its parts.** -/
theorem spotFarB_of_parts {D : GData} {i : ℕ} {T : TCert} (h : spotHeadB D i T = true)
    (hok : (T.cert D.gs).ok = true) : spotFarB D i T = true := by
  unfold spotHeadB at h
  unfold spotFarB
  rw [hok]
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨h.1.1, trivial⟩, h.1.2⟩, h.2⟩

end

end ArtGallery.Orthogonal.Hard
