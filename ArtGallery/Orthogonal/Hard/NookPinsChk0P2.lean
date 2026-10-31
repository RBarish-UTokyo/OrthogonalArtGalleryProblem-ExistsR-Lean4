module

public import ArtGallery.Orthogonal.Hard.NookPinsData
public import ArtGallery.Orthogonal.Hard.GCertSplit

/-! # Copy-nook pin check: chunk 2 of `nookPB0` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPB0_p2 : nookPB0.okPart 20 19 nookOr (2 * 1) 1 = true :=
  GCert.okPart_of_H [] (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
