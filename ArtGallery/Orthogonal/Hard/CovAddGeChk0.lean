module

public import ArtGallery.Orthogonal.Hard.CovAddGeData
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddGe`, part 0 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddGe_fsegs : gCovAddGe.frame.segsB = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz0h : (gCovAddGe.frame.zones.getD 0 zoneD).headB = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz0c0 : idxAll (gCovAddGe.frame.zones.getD 0 zoneD).colB 0 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz0c1 : idxAll (gCovAddGe.frame.zones.getD 0 zoneD).colB 8 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz0c2 : idxAll (gCovAddGe.frame.zones.getD 0 zoneD).colB 16 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz0c3 : idxAll (gCovAddGe.frame.zones.getD 0 zoneD).colB 24 32 = true := by decide +kernel

end

end ArtGallery.Orthogonal.Hard
