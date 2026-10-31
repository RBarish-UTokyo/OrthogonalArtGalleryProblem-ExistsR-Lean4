module

public import ArtGallery.Orthogonal.Hard.NookPinsData
public import ArtGallery.Orthogonal.Hard.GCertSplit

/-! # Copy-nook pin check: chunk 3 of `nookPB1` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPB1_p3 : nookPB1.okPart 20 19 nookOr (3 * 1) 1 = true :=
  GCert.okPart_of_H [[], [30], [15], [30], [30], [15]] (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
