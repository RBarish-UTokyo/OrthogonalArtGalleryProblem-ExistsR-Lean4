module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 8 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP19_b : (gAddGeP19.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP19_n : (gAddGeP19.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP19_p0 : (gAddGeP19.T.cert (slotZ .addGe)).okPropR 0 83 = true :=
  TCertI.okPropR_of_K gAddGeP19I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP19_p1 : (gAddGeP19.T.cert (slotZ .addGe)).okPropR 83 128 = true :=
  TCertI.okPropR_of_K gAddGeP19I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP19_p2 : (gAddGeP19.T.cert (slotZ .addGe)).okPropR 128 168 = true :=
  TCertI.okPropR_of_K gAddGeP19I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP19_p3 : (gAddGeP19.T.cert (slotZ .addGe)).okPropR 168 200 = true :=
  TCertI.okPropR_of_K gAddGeP19I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP19_p4 : (gAddGeP19.T.cert (slotZ .addGe)).okPropR 200 235 = true :=
  TCertI.okPropR_of_K gAddGeP19I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP19_p5 : (gAddGeP19.T.cert (slotZ .addGe)).okPropR 235 251 = true :=
  TCertI.okPropR_of_K gAddGeP19I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP19_p6 : (gAddGeP19.T.cert (slotZ .addGe)).okPropR 251 270 = true :=
  TCertI.okPropR_of_K gAddGeP19I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP19_p7 : (gAddGeP19.T.cert (slotZ .addGe)).okPropR 270 286 = true :=
  TCertI.okPropR_of_K gAddGeP19I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP19_p8 : (gAddGeP19.T.cert (slotZ .addGe)).okPropR 286 411 = true :=
  TCertI.okPropR_of_K gAddGeP19I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP19_h : pinHeadB (slotZ .addGe) gAddGeP19 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP19_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP19_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP19 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP19_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP19 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP19_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP19 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP19_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP19 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP19_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP19 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP19_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP19 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP19`, from its parts. -/
theorem gAddGeP19_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP19 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP19_b gAddGeP19_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP19_p0) gAddGeP19_p1) gAddGeP19_p2) gAddGeP19_p3) gAddGeP19_p4) gAddGeP19_p5) gAddGeP19_p6) gAddGeP19_p7) gAddGeP19_p8)) gAddGeP19_h gAddGeP19_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP19_j0) gAddGeP19_j1) gAddGeP19_j2) gAddGeP19_j3) gAddGeP19_j4) gAddGeP19_j5)

end

end ArtGallery.Orthogonal.Hard
