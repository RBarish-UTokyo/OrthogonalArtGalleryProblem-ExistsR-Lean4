module

public import ArtGallery.Orthogonal.Hard.NookPinsData
public import ArtGallery.Orthogonal.Hard.GCertSplit

/-! # Copy-nook pin check: chunk 36 of `nookPC1` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPC1_p36 : nookPC1.okPart 20 19 nookOr (36 * 1) 1 = true :=
  GCert.okPart_of_H [] (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
