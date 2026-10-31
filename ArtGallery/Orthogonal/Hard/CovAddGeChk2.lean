module

public import ArtGallery.Orthogonal.Hard.CovAddGeData
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddGe`, part 2 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz0c10 : idxAll (gCovAddGe.frame.zones.getD 0 zoneD).colB 80 86 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz1 : idxAll (fun k => (gCovAddGe.frame.zones.getD k zoneD).ok) 1 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz2 : idxAll (fun k => (gCovAddGe.frame.zones.getD k zoneD).ok) 2 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz3 : idxAll (fun k => (gCovAddGe.frame.zones.getD k zoneD).ok) 3 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz4 : idxAll (fun k => (gCovAddGe.frame.zones.getD k zoneD).ok) 4 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddGe_fz5 : idxAll (fun k => (gCovAddGe.frame.zones.getD k zoneD).ok) 5 6 = true := by
  decide +kernel

end

end ArtGallery.Orthogonal.Hard
