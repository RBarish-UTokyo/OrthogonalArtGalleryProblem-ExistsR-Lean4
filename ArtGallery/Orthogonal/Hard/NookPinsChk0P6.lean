module

public import ArtGallery.Orthogonal.Hard.NookPinsData
public import ArtGallery.Orthogonal.Hard.GCertSplit

/-! # Copy-nook pin check: chunk 6 of `nookPB0` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPB0_p6 : nookPB0.okPart 20 19 nookOr (6 * 1) 1 = true :=
  GCert.okPart_of_H [[], [], [], [], [6], [], [6], [], [], [6]] (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
