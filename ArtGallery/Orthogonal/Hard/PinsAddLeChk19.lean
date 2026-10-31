module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 19 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP44_b : (gAddLeP44.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP44_n : (gAddLeP44.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP44_p0 : (gAddLeP44.T.cert (slotZ .addLe)).okPropR 0 335 = true :=
  TCertI.okPropR_of_K gAddLeP44I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP44H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP44_p1 : (gAddLeP44.T.cert (slotZ .addLe)).okPropR 335 397 = true :=
  TCertI.okPropR_of_K gAddLeP44I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP44H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP44_h : pinHeadB (slotZ .addLe) gAddLeP44 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP44_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP44_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP44 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP44_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP44 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP44_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP44 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP44_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP44 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP44_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP44 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP44_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP44 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP44`, from its parts. -/
theorem gAddLeP44_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP44 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP44_b gAddLeP44_n (allR_join (by norm_num) (by norm_num) (gAddLeP44_p0) gAddLeP44_p1)) gAddLeP44_h gAddLeP44_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP44_j0) gAddLeP44_j1) gAddLeP44_j2) gAddLeP44_j3) gAddLeP44_j4) gAddLeP44_j5)

end

end ArtGallery.Orthogonal.Hard
