module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 5 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP18_b : (gAddLeP18.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP18_n : (gAddLeP18.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP18_p0 : (gAddLeP18.T.cert (slotZ .addLe)).okPropR 0 21 = true :=
  TCertI.okPropR_of_K gAddLeP18I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP18_p1 : (gAddLeP18.T.cert (slotZ .addLe)).okPropR 21 41 = true :=
  TCertI.okPropR_of_K gAddLeP18I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP18_p2 : (gAddLeP18.T.cert (slotZ .addLe)).okPropR 41 61 = true :=
  TCertI.okPropR_of_K gAddLeP18I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP18_p3 : (gAddLeP18.T.cert (slotZ .addLe)).okPropR 61 87 = true :=
  TCertI.okPropR_of_K gAddLeP18I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP18_p4 : (gAddLeP18.T.cert (slotZ .addLe)).okPropR 87 142 = true :=
  TCertI.okPropR_of_K gAddLeP18I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP18_p5 : (gAddLeP18.T.cert (slotZ .addLe)).okPropR 142 397 = true :=
  TCertI.okPropR_of_K gAddLeP18I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP18_h : pinHeadB (slotZ .addLe) gAddLeP18 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP18_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP18_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP18 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP18_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP18 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP18_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP18 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP18_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP18 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP18_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP18 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP18_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP18 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP18`, from its parts. -/
theorem gAddLeP18_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP18 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP18_b gAddLeP18_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP18_p0) gAddLeP18_p1) gAddLeP18_p2) gAddLeP18_p3) gAddLeP18_p4) gAddLeP18_p5)) gAddLeP18_h gAddLeP18_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP18_j0) gAddLeP18_j1) gAddLeP18_j2) gAddLeP18_j3) gAddLeP18_j4) gAddLeP18_j5)

end

end ArtGallery.Orthogonal.Hard
