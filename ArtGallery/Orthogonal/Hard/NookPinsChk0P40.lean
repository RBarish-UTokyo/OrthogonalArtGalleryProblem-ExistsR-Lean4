module

public import ArtGallery.Orthogonal.Hard.NookPinsData
public import ArtGallery.Orthogonal.Hard.GCertSplit

/-! # Copy-nook pin check: chunk 40 of `nookPB0` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPB0_p40 : nookPB0.okPart 20 19 nookOr (40 * 1) 1 = true :=
  GCert.okPart_of_H [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [32], [], [32]] (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
