module

public import ArtGallery.Orthogonal.Hard.CovAddLeData
public import ArtGallery.Orthogonal.Hard.CovSplit

/-! # Coverage certificate checks of `gCovAddLe`, part 2 (generated) -/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gCovAddLe_fz1 : idxAll (fun k => (gCovAddLe.frame.zones.getD k zoneD).ok) 1 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddLe_fz2 : idxAll (fun k => (gCovAddLe.frame.zones.getD k zoneD).ok) 2 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddLe_fz3 : idxAll (fun k => (gCovAddLe.frame.zones.getD k zoneD).ok) 3 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddLe_fz4 : idxAll (fun k => (gCovAddLe.frame.zones.getD k zoneD).ok) 4 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddLe_fz5 : idxAll (fun k => (gCovAddLe.frame.zones.getD k zoneD).ok) 5 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gCovAddLe_fz6 : idxAll (fun k => (gCovAddLe.frame.zones.getD k zoneD).ok) 6 7 = true := by
  decide +kernel

end

end ArtGallery.Orthogonal.Hard
