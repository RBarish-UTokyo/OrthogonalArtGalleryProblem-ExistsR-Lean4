module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 16 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP41_b : (gAddGeP41.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP41_n : (gAddGeP41.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP41_p0 : (gAddGeP41.T.cert (slotZ .addGe)).okPropR 0 374 = true :=
  TCertI.okPropR_of_K gAddGeP41I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP41H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP41_p1 : (gAddGeP41.T.cert (slotZ .addGe)).okPropR 374 411 = true :=
  TCertI.okPropR_of_K gAddGeP41I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP41H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP41_h : pinHeadB (slotZ .addGe) gAddGeP41 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP41_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP41_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP41 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP41_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP41 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP41_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP41 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP41_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP41 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP41_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP41 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP41_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP41 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP41`, from its parts. -/
theorem gAddGeP41_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP41 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP41_b gAddGeP41_n (allR_join (by norm_num) (by norm_num) (gAddGeP41_p0) gAddGeP41_p1)) gAddGeP41_h gAddGeP41_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP41_j0) gAddGeP41_j1) gAddGeP41_j2) gAddGeP41_j3) gAddGeP41_j4) gAddGeP41_j5)

end

end ArtGallery.Orthogonal.Hard
