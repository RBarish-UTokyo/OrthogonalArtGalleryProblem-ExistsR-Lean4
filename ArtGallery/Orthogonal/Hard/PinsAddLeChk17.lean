module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 17 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP41_b : (gAddLeP41.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP41_n : (gAddLeP41.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP41_p0 : (gAddLeP41.T.cert (slotZ .addLe)).okPropR 0 318 = true :=
  TCertI.okPropR_of_K gAddLeP41I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP41H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP41_p1 : (gAddLeP41.T.cert (slotZ .addLe)).okPropR 318 397 = true :=
  TCertI.okPropR_of_K gAddLeP41I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP41H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP41_h : pinHeadB (slotZ .addLe) gAddLeP41 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP41_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP41_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP41 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP41_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP41 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP41_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP41 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP41_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP41 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP41_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP41 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP41_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP41 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP41`, from its parts. -/
theorem gAddLeP41_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP41 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP41_b gAddLeP41_n (allR_join (by norm_num) (by norm_num) (gAddLeP41_p0) gAddLeP41_p1)) gAddLeP41_h gAddLeP41_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP41_j0) gAddLeP41_j1) gAddLeP41_j2) gAddLeP41_j3) gAddLeP41_j4) gAddLeP41_j5)

end

end ArtGallery.Orthogonal.Hard
