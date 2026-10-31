module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 7 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP18_b : (gAddGeP18.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP18_n : (gAddGeP18.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP18_p0 : (gAddGeP18.T.cert (slotZ .addGe)).okPropR 0 19 = true :=
  TCertI.okPropR_of_K gAddGeP18I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP18_p1 : (gAddGeP18.T.cert (slotZ .addGe)).okPropR 19 31 = true :=
  TCertI.okPropR_of_K gAddGeP18I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP18_p2 : (gAddGeP18.T.cert (slotZ .addGe)).okPropR 31 43 = true :=
  TCertI.okPropR_of_K gAddGeP18I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP18_p3 : (gAddGeP18.T.cert (slotZ .addGe)).okPropR 43 62 = true :=
  TCertI.okPropR_of_K gAddGeP18I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP18_p4 : (gAddGeP18.T.cert (slotZ .addGe)).okPropR 62 83 = true :=
  TCertI.okPropR_of_K gAddGeP18I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP18_p5 : (gAddGeP18.T.cert (slotZ .addGe)).okPropR 83 114 = true :=
  TCertI.okPropR_of_K gAddGeP18I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP18_p6 : (gAddGeP18.T.cert (slotZ .addGe)).okPropR 114 160 = true :=
  TCertI.okPropR_of_K gAddGeP18I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP18_p7 : (gAddGeP18.T.cert (slotZ .addGe)).okPropR 160 246 = true :=
  TCertI.okPropR_of_K gAddGeP18I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP18_p8 : (gAddGeP18.T.cert (slotZ .addGe)).okPropR 246 411 = true :=
  TCertI.okPropR_of_K gAddGeP18I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP18H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP18_h : pinHeadB (slotZ .addGe) gAddGeP18 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP18_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP18_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP18 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP18_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP18 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP18_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP18 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP18_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP18 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP18_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP18 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP18_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP18 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP18`, from its parts. -/
theorem gAddGeP18_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP18 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP18_b gAddGeP18_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP18_p0) gAddGeP18_p1) gAddGeP18_p2) gAddGeP18_p3) gAddGeP18_p4) gAddGeP18_p5) gAddGeP18_p6) gAddGeP18_p7) gAddGeP18_p8)) gAddGeP18_h gAddGeP18_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP18_j0) gAddGeP18_j1) gAddGeP18_j2) gAddGeP18_j3) gAddGeP18_j4) gAddGeP18_j5)

end

end ArtGallery.Orthogonal.Hard
