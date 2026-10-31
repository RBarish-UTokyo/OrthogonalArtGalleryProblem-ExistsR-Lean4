module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 18 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP44_b : (gAddGeP44.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP44_n : (gAddGeP44.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP44_p0 : (gAddGeP44.T.cert (slotZ .addGe)).okPropR 0 394 = true :=
  TCertI.okPropR_of_K gAddGeP44I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP44H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP44_p1 : (gAddGeP44.T.cert (slotZ .addGe)).okPropR 394 411 = true :=
  TCertI.okPropR_of_K gAddGeP44I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP44H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP44_h : pinHeadB (slotZ .addGe) gAddGeP44 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP44_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP44_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP44 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP44_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP44 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP44_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP44 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP44_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP44 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP44_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP44 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP44_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP44 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP44`, from its parts. -/
theorem gAddGeP44_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP44 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP44_b gAddGeP44_n (allR_join (by norm_num) (by norm_num) (gAddGeP44_p0) gAddGeP44_p1)) gAddGeP44_h gAddGeP44_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP44_j0) gAddGeP44_j1) gAddGeP44_j2) gAddGeP44_j3) gAddGeP44_j4) gAddGeP44_j5)

end

end ArtGallery.Orthogonal.Hard
