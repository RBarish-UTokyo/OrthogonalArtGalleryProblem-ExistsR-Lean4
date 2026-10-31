module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 4 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP12_b : (gAddGeP12.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP12_n : (gAddGeP12.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP12_p0 : (gAddGeP12.T.cert (slotZ .addGe)).okPropR 0 68 = true :=
  TCertI.okPropR_of_K gAddGeP12I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP12H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP12_p1 : (gAddGeP12.T.cert (slotZ .addGe)).okPropR 68 96 = true :=
  TCertI.okPropR_of_K gAddGeP12I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP12H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP12_p2 : (gAddGeP12.T.cert (slotZ .addGe)).okPropR 96 146 = true :=
  TCertI.okPropR_of_K gAddGeP12I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP12H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP12_p3 : (gAddGeP12.T.cert (slotZ .addGe)).okPropR 146 411 = true :=
  TCertI.okPropR_of_K gAddGeP12I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP12H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP12_h : pinHeadB (slotZ .addGe) gAddGeP12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP12_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP12_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP12 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP12_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP12 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP12_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP12 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP12_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP12 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP12_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP12 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP12_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP12 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP12`, from its parts. -/
theorem gAddGeP12_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP12 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP12_b gAddGeP12_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP12_p0) gAddGeP12_p1) gAddGeP12_p2) gAddGeP12_p3)) gAddGeP12_h gAddGeP12_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP12_j0) gAddGeP12_j1) gAddGeP12_j2) gAddGeP12_j3) gAddGeP12_j4) gAddGeP12_j5)

end

end ArtGallery.Orthogonal.Hard
