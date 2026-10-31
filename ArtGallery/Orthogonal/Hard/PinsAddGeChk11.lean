module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 11 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP25_b : (gAddGeP25.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP25_n : (gAddGeP25.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP25_p0 : (gAddGeP25.T.cert (slotZ .addGe)).okPropR 0 76 = true :=
  TCertI.okPropR_of_K gAddGeP25I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP25_p1 : (gAddGeP25.T.cert (slotZ .addGe)).okPropR 76 119 = true :=
  TCertI.okPropR_of_K gAddGeP25I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP25_p2 : (gAddGeP25.T.cert (slotZ .addGe)).okPropR 119 158 = true :=
  TCertI.okPropR_of_K gAddGeP25I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP25_p3 : (gAddGeP25.T.cert (slotZ .addGe)).okPropR 158 190 = true :=
  TCertI.okPropR_of_K gAddGeP25I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP25_p4 : (gAddGeP25.T.cert (slotZ .addGe)).okPropR 190 226 = true :=
  TCertI.okPropR_of_K gAddGeP25I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP25_p5 : (gAddGeP25.T.cert (slotZ .addGe)).okPropR 226 245 = true :=
  TCertI.okPropR_of_K gAddGeP25I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP25_p6 : (gAddGeP25.T.cert (slotZ .addGe)).okPropR 245 261 = true :=
  TCertI.okPropR_of_K gAddGeP25I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP25_p7 : (gAddGeP25.T.cert (slotZ .addGe)).okPropR 261 279 = true :=
  TCertI.okPropR_of_K gAddGeP25I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP25_p8 : (gAddGeP25.T.cert (slotZ .addGe)).okPropR 279 411 = true :=
  TCertI.okPropR_of_K gAddGeP25I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP25H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP25_h : pinHeadB (slotZ .addGe) gAddGeP25 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP25_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP25_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP25 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP25_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP25 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP25_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP25 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP25_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP25 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP25_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP25 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP25_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP25 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP25`, from its parts. -/
theorem gAddGeP25_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP25 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP25_b gAddGeP25_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP25_p0) gAddGeP25_p1) gAddGeP25_p2) gAddGeP25_p3) gAddGeP25_p4) gAddGeP25_p5) gAddGeP25_p6) gAddGeP25_p7) gAddGeP25_p8)) gAddGeP25_h gAddGeP25_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP25_j0) gAddGeP25_j1) gAddGeP25_j2) gAddGeP25_j3) gAddGeP25_j4) gAddGeP25_j5)

end

end ArtGallery.Orthogonal.Hard
