module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 2 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP10_b : (gAddGeP10.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP10_n : (gAddGeP10.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP10_p0 : (gAddGeP10.T.cert (slotZ .addGe)).okPropR 0 204 = true :=
  TCertI.okPropR_of_K gAddGeP10I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP10_p1 : (gAddGeP10.T.cert (slotZ .addGe)).okPropR 204 252 = true :=
  TCertI.okPropR_of_K gAddGeP10I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP10_p2 : (gAddGeP10.T.cert (slotZ .addGe)).okPropR 252 411 = true :=
  TCertI.okPropR_of_K gAddGeP10I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP10H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP10_h : pinHeadB (slotZ .addGe) gAddGeP10 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP10_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP10_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP10 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP10_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP10 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP10_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP10 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP10_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP10 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP10_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP10 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP10_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP10 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP10`, from its parts. -/
theorem gAddGeP10_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP10 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP10_b gAddGeP10_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP10_p0) gAddGeP10_p1) gAddGeP10_p2)) gAddGeP10_h gAddGeP10_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP10_j0) gAddGeP10_j1) gAddGeP10_j2) gAddGeP10_j3) gAddGeP10_j4) gAddGeP10_j5)

end

end ArtGallery.Orthogonal.Hard
