module

public import ArtGallery.Orthogonal.Hard.NookPinsData
public import ArtGallery.Orthogonal.Hard.GCertSplit

/-! # Copy-nook pin check: chunk 4 of `nookPB0` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPB0_p4 : nookPB0.okPart 20 19 nookOr (4 * 1) 1 = true :=
  GCert.okPart_of_H [[], [], [], [4], [4], [], [4], [1]] (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
