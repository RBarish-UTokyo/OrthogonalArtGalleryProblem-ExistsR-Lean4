module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 21 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP47_b : (gAddGeP47.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP47_n : (gAddGeP47.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP47_p0 : (gAddGeP47.T.cert (slotZ .addGe)).okPropR 0 304 = true :=
  TCertI.okPropR_of_K gAddGeP47I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP47_p1 : (gAddGeP47.T.cert (slotZ .addGe)).okPropR 304 316 = true :=
  TCertI.okPropR_of_K gAddGeP47I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP47_p2 : (gAddGeP47.T.cert (slotZ .addGe)).okPropR 316 325 = true :=
  TCertI.okPropR_of_K gAddGeP47I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP47_p3 : (gAddGeP47.T.cert (slotZ .addGe)).okPropR 325 332 = true :=
  TCertI.okPropR_of_K gAddGeP47I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP47_p4 : (gAddGeP47.T.cert (slotZ .addGe)).okPropR 332 338 = true :=
  TCertI.okPropR_of_K gAddGeP47I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP47_p5 : (gAddGeP47.T.cert (slotZ .addGe)).okPropR 338 344 = true :=
  TCertI.okPropR_of_K gAddGeP47I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP47_p6 : (gAddGeP47.T.cert (slotZ .addGe)).okPropR 344 349 = true :=
  TCertI.okPropR_of_K gAddGeP47I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP47_p7 : (gAddGeP47.T.cert (slotZ .addGe)).okPropR 349 411 = true :=
  TCertI.okPropR_of_K gAddGeP47I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP47H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP47_h : pinHeadB (slotZ .addGe) gAddGeP47 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP47_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP47_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP47 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP47_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP47 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP47_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP47 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP47_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP47 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP47_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP47 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP47_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP47 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP47`, from its parts. -/
theorem gAddGeP47_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP47 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP47_b gAddGeP47_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP47_p0) gAddGeP47_p1) gAddGeP47_p2) gAddGeP47_p3) gAddGeP47_p4) gAddGeP47_p5) gAddGeP47_p6) gAddGeP47_p7)) gAddGeP47_h gAddGeP47_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP47_j0) gAddGeP47_j1) gAddGeP47_j2) gAddGeP47_j3) gAddGeP47_j4) gAddGeP47_j5)

end

end ArtGallery.Orthogonal.Hard
