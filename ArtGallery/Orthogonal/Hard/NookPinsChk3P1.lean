module

public import ArtGallery.Orthogonal.Hard.NookPinsData
public import ArtGallery.Orthogonal.Hard.GCertSplit

/-! # Copy-nook pin check: chunk 1 of `nookPB1` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPB1_p1 : nookPB1.okPart 20 19 nookOr (1 * 1) 1 = true :=
  GCert.okPart_of_H [[], [32], [], [32]] (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
