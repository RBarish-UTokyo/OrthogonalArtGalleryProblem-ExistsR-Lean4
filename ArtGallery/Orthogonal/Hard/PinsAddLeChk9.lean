module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 9 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP22_b : (gAddLeP22.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP22_n : (gAddLeP22.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP22_p0 : (gAddLeP22.T.cert (slotZ .addLe)).okPropR 0 397 = true :=
  TCertI.okPropR_of_K gAddLeP22I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP22H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP22_h : pinHeadB (slotZ .addLe) gAddLeP22 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP22_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP22_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP22 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP22_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP22 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP22_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP22 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP22_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP22 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP22_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP22 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP22_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP22 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP22`, from its parts. -/
theorem gAddLeP22_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP22 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP22_b gAddLeP22_n (gAddLeP22_p0)) gAddLeP22_h gAddLeP22_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP22_j0) gAddLeP22_j1) gAddLeP22_j2) gAddLeP22_j3) gAddLeP22_j4) gAddLeP22_j5)

end

end ArtGallery.Orthogonal.Hard
