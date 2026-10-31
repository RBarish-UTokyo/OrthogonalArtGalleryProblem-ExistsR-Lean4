module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 11 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP24_b : (gAddLeP24.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP24_n : (gAddLeP24.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP24_p0 : (gAddLeP24.T.cert (slotZ .addLe)).okPropR 0 15 = true :=
  TCertI.okPropR_of_K gAddLeP24I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP24_p1 : (gAddLeP24.T.cert (slotZ .addLe)).okPropR 15 35 = true :=
  TCertI.okPropR_of_K gAddLeP24I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP24_p2 : (gAddLeP24.T.cert (slotZ .addLe)).okPropR 35 55 = true :=
  TCertI.okPropR_of_K gAddLeP24I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP24_p3 : (gAddLeP24.T.cert (slotZ .addLe)).okPropR 55 80 = true :=
  TCertI.okPropR_of_K gAddLeP24I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP24_p4 : (gAddLeP24.T.cert (slotZ .addLe)).okPropR 80 124 = true :=
  TCertI.okPropR_of_K gAddLeP24I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP24_p5 : (gAddLeP24.T.cert (slotZ .addLe)).okPropR 124 217 = true :=
  TCertI.okPropR_of_K gAddLeP24I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP24_p6 : (gAddLeP24.T.cert (slotZ .addLe)).okPropR 217 397 = true :=
  TCertI.okPropR_of_K gAddLeP24I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP24_h : pinHeadB (slotZ .addLe) gAddLeP24 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP24_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP24_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP24 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP24_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP24 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP24_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP24 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP24_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP24 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP24_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP24 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP24_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP24 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP24`, from its parts. -/
theorem gAddLeP24_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP24 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP24_b gAddLeP24_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP24_p0) gAddLeP24_p1) gAddLeP24_p2) gAddLeP24_p3) gAddLeP24_p4) gAddLeP24_p5) gAddLeP24_p6)) gAddLeP24_h gAddLeP24_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP24_j0) gAddLeP24_j1) gAddLeP24_j2) gAddLeP24_j3) gAddLeP24_j4) gAddLeP24_j5)

end

end ArtGallery.Orthogonal.Hard
