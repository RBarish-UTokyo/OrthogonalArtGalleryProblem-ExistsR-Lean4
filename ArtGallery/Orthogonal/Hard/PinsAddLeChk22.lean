module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 22 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP47_b : (gAddLeP47.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP47_n : (gAddLeP47.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP47_p0 : (gAddLeP47.T.cert (slotZ .addLe)).okPropR 0 301 = true :=
  TCertI.okPropR_of_K gAddLeP47I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP47_p1 : (gAddLeP47.T.cert (slotZ .addLe)).okPropR 301 313 = true :=
  TCertI.okPropR_of_K gAddLeP47I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP47_p2 : (gAddLeP47.T.cert (slotZ .addLe)).okPropR 313 321 = true :=
  TCertI.okPropR_of_K gAddLeP47I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP47_p3 : (gAddLeP47.T.cert (slotZ .addLe)).okPropR 321 328 = true :=
  TCertI.okPropR_of_K gAddLeP47I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP47_p4 : (gAddLeP47.T.cert (slotZ .addLe)).okPropR 328 335 = true :=
  TCertI.okPropR_of_K gAddLeP47I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP47_p5 : (gAddLeP47.T.cert (slotZ .addLe)).okPropR 335 397 = true :=
  TCertI.okPropR_of_K gAddLeP47I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP47_h : pinHeadB (slotZ .addLe) gAddLeP47 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP47_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP47_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP47 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP47_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP47 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP47_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP47 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP47_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP47 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP47_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP47 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP47_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP47 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP47`, from its parts. -/
theorem gAddLeP47_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP47 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP47_b gAddLeP47_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP47_p0) gAddLeP47_p1) gAddLeP47_p2) gAddLeP47_p3) gAddLeP47_p4) gAddLeP47_p5)) gAddLeP47_h gAddLeP47_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP47_j0) gAddLeP47_j1) gAddLeP47_j2) gAddLeP47_j3) gAddLeP47_j4) gAddLeP47_j5)

end

end ArtGallery.Orthogonal.Hard
