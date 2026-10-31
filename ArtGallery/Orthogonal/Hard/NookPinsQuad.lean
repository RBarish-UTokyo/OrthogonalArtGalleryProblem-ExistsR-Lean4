module

public import ArtGallery.Orthogonal.Hard.NookPin

/-! # Quadrants of the copy-nook arm tips (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem nookQB_2 : nookQuadB nookOr 3 (4, 15) 2 = true := by decide +kernel

theorem nookTB_2 : cnG1.getD 3 (0, 0) = (18, 15) := rfl

theorem nookQB_1 : nookQuadB nookOr 8 (4, 15) 1 = true := by decide +kernel

theorem nookTB_1 : cnG1.getD 8 (0, 0) = (4, 18) := rfl

theorem nookQB_3 : nookQuadB nookOr 13 (4, 15) 3 = true := by decide +kernel

theorem nookTB_3 : cnG1.getD 13 (0, 0) = (1, 15) := rfl

theorem nookQB_0 : nookQuadB nookOr 18 (4, 15) 0 = true := by decide +kernel

theorem nookTB_0 : cnG1.getD 18 (0, 0) = (4, 4) := rfl

theorem nookQC_3 : nookQuadB nookOr 24 (11, 8) 3 = true := by decide +kernel

theorem nookTC_3 : cnG1.getD 24 (0, 0) = (14, 8) := rfl

theorem nookQC_0 : nookQuadB nookOr 29 (11, 8) 0 = true := by decide +kernel

theorem nookTC_0 : cnG1.getD 29 (0, 0) = (11, 11) := rfl

theorem nookQC_2 : nookQuadB nookOr 34 (11, 8) 2 = true := by decide +kernel

theorem nookTC_2 : cnG1.getD 34 (0, 0) = (8, 8) := rfl

theorem nookQC_1 : nookQuadB nookOr 39 (11, 8) 1 = true := by decide +kernel

theorem nookTC_1 : cnG1.getD 39 (0, 0) = (11, 2) := rfl

end

end ArtGallery.Orthogonal.Hard
