module

public import ArtGallery.Orthogonal.Hard.NookPinsData
public import ArtGallery.Orthogonal.Hard.GCertSplit

/-! # Copy-nook pin check: chunk 26 of `nookPC1` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPC1_p26 : nookPC1.okPart 20 19 nookOr (26 * 1) 1 = true :=
  GCert.okPart_of_H [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [0]] (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
