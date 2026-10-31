module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 5 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP13_b : (gAddGeP13.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP13_n : (gAddGeP13.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP13_p0 : (gAddGeP13.T.cert (slotZ .addGe)).okPropR 0 154 = true :=
  TCertI.okPropR_of_K gAddGeP13I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP13H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP13_p1 : (gAddGeP13.T.cert (slotZ .addGe)).okPropR 154 213 = true :=
  TCertI.okPropR_of_K gAddGeP13I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP13H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP13_p2 : (gAddGeP13.T.cert (slotZ .addGe)).okPropR 213 247 = true :=
  TCertI.okPropR_of_K gAddGeP13I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP13H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP13_p3 : (gAddGeP13.T.cert (slotZ .addGe)).okPropR 247 411 = true :=
  TCertI.okPropR_of_K gAddGeP13I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP13H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP13_h : pinHeadB (slotZ .addGe) gAddGeP13 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP13_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP13_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP13 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP13_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP13 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP13_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP13 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP13_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP13 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP13_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP13 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP13_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP13 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP13`, from its parts. -/
theorem gAddGeP13_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP13 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP13_b gAddGeP13_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP13_p0) gAddGeP13_p1) gAddGeP13_p2) gAddGeP13_p3)) gAddGeP13_h gAddGeP13_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP13_j0) gAddGeP13_j1) gAddGeP13_j2) gAddGeP13_j3) gAddGeP13_j4) gAddGeP13_j5)

end

end ArtGallery.Orthogonal.Hard
