module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 3 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP13_b : (gAddLeP13.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP13_n : (gAddLeP13.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP13_p0 : (gAddLeP13.T.cert (slotZ .addLe)).okPropR 0 104 = true :=
  TCertI.okPropR_of_K gAddLeP13I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP13H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP13_p1 : (gAddLeP13.T.cert (slotZ .addLe)).okPropR 104 160 = true :=
  TCertI.okPropR_of_K gAddLeP13I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP13H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP13_p2 : (gAddLeP13.T.cert (slotZ .addLe)).okPropR 160 205 = true :=
  TCertI.okPropR_of_K gAddLeP13I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP13H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP13_p3 : (gAddLeP13.T.cert (slotZ .addLe)).okPropR 205 238 = true :=
  TCertI.okPropR_of_K gAddLeP13I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP13H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP13_p4 : (gAddLeP13.T.cert (slotZ .addLe)).okPropR 238 266 = true :=
  TCertI.okPropR_of_K gAddLeP13I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP13H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP13_p5 : (gAddLeP13.T.cert (slotZ .addLe)).okPropR 266 397 = true :=
  TCertI.okPropR_of_K gAddLeP13I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP13H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP13_h : pinHeadB (slotZ .addLe) gAddLeP13 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP13_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP13_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP13 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP13_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP13 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP13_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP13 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP13_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP13 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP13_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP13 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP13_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP13 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP13`, from its parts. -/
theorem gAddLeP13_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP13 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP13_b gAddLeP13_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP13_p0) gAddLeP13_p1) gAddLeP13_p2) gAddLeP13_p3) gAddLeP13_p4) gAddLeP13_p5)) gAddLeP13_h gAddLeP13_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP13_j0) gAddLeP13_j1) gAddLeP13_j2) gAddLeP13_j3) gAddLeP13_j4) gAddLeP13_j5)

end

end ArtGallery.Orthogonal.Hard
