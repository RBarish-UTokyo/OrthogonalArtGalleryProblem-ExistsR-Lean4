module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 10 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP24_b : (gAddGeP24.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP24_n : (gAddGeP24.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP24_p0 : (gAddGeP24.T.cert (slotZ .addGe)).okPropR 0 14 = true :=
  TCertI.okPropR_of_K gAddGeP24I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP24_p1 : (gAddGeP24.T.cert (slotZ .addGe)).okPropR 14 26 = true :=
  TCertI.okPropR_of_K gAddGeP24I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP24_p2 : (gAddGeP24.T.cert (slotZ .addGe)).okPropR 26 38 = true :=
  TCertI.okPropR_of_K gAddGeP24I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP24_p3 : (gAddGeP24.T.cert (slotZ .addGe)).okPropR 38 56 = true :=
  TCertI.okPropR_of_K gAddGeP24I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP24_p4 : (gAddGeP24.T.cert (slotZ .addGe)).okPropR 56 76 = true :=
  TCertI.okPropR_of_K gAddGeP24I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP24_p5 : (gAddGeP24.T.cert (slotZ .addGe)).okPropR 76 106 = true :=
  TCertI.okPropR_of_K gAddGeP24I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP24_p6 : (gAddGeP24.T.cert (slotZ .addGe)).okPropR 106 150 = true :=
  TCertI.okPropR_of_K gAddGeP24I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP24_p7 : (gAddGeP24.T.cert (slotZ .addGe)).okPropR 150 234 = true :=
  TCertI.okPropR_of_K gAddGeP24I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP24_p8 : (gAddGeP24.T.cert (slotZ .addGe)).okPropR 234 411 = true :=
  TCertI.okPropR_of_K gAddGeP24I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP24H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP24_h : pinHeadB (slotZ .addGe) gAddGeP24 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP24_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP24_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP24 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP24_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP24 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP24_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP24 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP24_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP24 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP24_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP24 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP24_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP24 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP24`, from its parts. -/
theorem gAddGeP24_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP24 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP24_b gAddGeP24_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP24_p0) gAddGeP24_p1) gAddGeP24_p2) gAddGeP24_p3) gAddGeP24_p4) gAddGeP24_p5) gAddGeP24_p6) gAddGeP24_p7) gAddGeP24_p8)) gAddGeP24_h gAddGeP24_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP24_j0) gAddGeP24_j1) gAddGeP24_j2) gAddGeP24_j3) gAddGeP24_j4) gAddGeP24_j5)

end

end ArtGallery.Orthogonal.Hard
