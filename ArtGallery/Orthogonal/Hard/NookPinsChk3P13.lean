module

public import ArtGallery.Orthogonal.Hard.NookPinsData
public import ArtGallery.Orthogonal.Hard.GCertSplit

/-! # Copy-nook pin check: chunk 13 of `nookPB1` (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookPB1_p13 : nookPB1.okPart 20 19 nookOr (13 * 1) 1 = true :=
  GCert.okPart_of_H [[], [], [], [], [], [], [], [], [], [22], [], [], [], [22], [], [], [22]] (by decide +kernel)

end

end ArtGallery.Orthogonal.Hard
