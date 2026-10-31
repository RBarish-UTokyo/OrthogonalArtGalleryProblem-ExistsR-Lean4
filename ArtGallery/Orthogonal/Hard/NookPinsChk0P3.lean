module

public import ArtGallery.Orthogonal.Hard.NookPinsData
public import ArtGallery.Orthogonal.Hard.GCertSplit

/-! # Copy-nook pin check: chunk 3 of `nookPB0` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPB0_p3 : nookPB0.okPart 20 19 nookOr (3 * 1) 1 = true :=
  GCert.okPart_of_H [[], [2], [0], [2], [2], [0]] (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
