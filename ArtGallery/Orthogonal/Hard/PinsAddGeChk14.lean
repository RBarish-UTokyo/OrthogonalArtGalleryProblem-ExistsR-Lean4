module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 14 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP38_b : (gAddGeP38.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP38_n : (gAddGeP38.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP38_p0 : (gAddGeP38.T.cert (slotZ .addGe)).okPropR 0 354 = true :=
  TCertI.okPropR_of_K gAddGeP38I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP38H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP38_p1 : (gAddGeP38.T.cert (slotZ .addGe)).okPropR 354 411 = true :=
  TCertI.okPropR_of_K gAddGeP38I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP38H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP38_h : pinHeadB (slotZ .addGe) gAddGeP38 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP38_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP38_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP38 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP38_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP38 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP38_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP38 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP38_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP38 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP38_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP38 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP38_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP38 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP38`, from its parts. -/
theorem gAddGeP38_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP38 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP38_b gAddGeP38_n (allR_join (by norm_num) (by norm_num) (gAddGeP38_p0) gAddGeP38_p1)) gAddGeP38_h gAddGeP38_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP38_j0) gAddGeP38_j1) gAddGeP38_j2) gAddGeP38_j3) gAddGeP38_j4) gAddGeP38_j5)

end

end ArtGallery.Orthogonal.Hard
