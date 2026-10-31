module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 12 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP25_b : (gAddLeP25.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP25_n : (gAddLeP25.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP25_p0 : (gAddLeP25.T.cert (slotZ .addLe)).okPropR 0 86 = true :=
  TCertI.okPropR_of_K gAddLeP25I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP25_p1 : (gAddLeP25.T.cert (slotZ .addLe)).okPropR 86 140 = true :=
  TCertI.okPropR_of_K gAddLeP25I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP25_p2 : (gAddLeP25.T.cert (slotZ .addLe)).okPropR 140 182 = true :=
  TCertI.okPropR_of_K gAddLeP25I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP25_p3 : (gAddLeP25.T.cert (slotZ .addLe)).okPropR 182 217 = true :=
  TCertI.okPropR_of_K gAddLeP25I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP25_p4 : (gAddLeP25.T.cert (slotZ .addLe)).okPropR 217 250 = true :=
  TCertI.okPropR_of_K gAddLeP25I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP25_p5 : (gAddLeP25.T.cert (slotZ .addLe)).okPropR 250 269 = true :=
  TCertI.okPropR_of_K gAddLeP25I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP25_p6 : (gAddLeP25.T.cert (slotZ .addLe)).okPropR 269 397 = true :=
  TCertI.okPropR_of_K gAddLeP25I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP25_h : pinHeadB (slotZ .addLe) gAddLeP25 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP25_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP25_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP25 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP25_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP25 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP25_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP25 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP25_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP25 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP25_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP25 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP25_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP25 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP25`, from its parts. -/
theorem gAddLeP25_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP25 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP25_b gAddLeP25_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP25_p0) gAddLeP25_p1) gAddLeP25_p2) gAddLeP25_p3) gAddLeP25_p4) gAddLeP25_p5) gAddLeP25_p6)) gAddLeP25_h gAddLeP25_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP25_j0) gAddLeP25_j1) gAddLeP25_j2) gAddLeP25_j3) gAddLeP25_j4) gAddLeP25_j5)

end

end ArtGallery.Orthogonal.Hard
