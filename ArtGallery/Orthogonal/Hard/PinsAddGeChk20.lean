module

public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addGe`, part 20 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddGeP46_b : (gAddGeP46.T.cert (slotZ .addGe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP46_n : (gAddGeP46.T.cert (slotZ .addGe)).cs.length ≤ 411 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP46_p0 : (gAddGeP46.T.cert (slotZ .addGe)).okPropR 0 310 = true :=
  TCertI.okPropR_of_K gAddGeP46I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP46_p1 : (gAddGeP46.T.cert (slotZ .addGe)).okPropR 310 321 = true :=
  TCertI.okPropR_of_K gAddGeP46I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP46_p2 : (gAddGeP46.T.cert (slotZ .addGe)).okPropR 321 331 = true :=
  TCertI.okPropR_of_K gAddGeP46I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP46_p3 : (gAddGeP46.T.cert (slotZ .addGe)).okPropR 331 336 = true :=
  TCertI.okPropR_of_K gAddGeP46I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP46_p4 : (gAddGeP46.T.cert (slotZ .addGe)).okPropR 336 344 = true :=
  TCertI.okPropR_of_K gAddGeP46I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP46_p5 : (gAddGeP46.T.cert (slotZ .addGe)).okPropR 344 349 = true :=
  TCertI.okPropR_of_K gAddGeP46I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP46_p6 : (gAddGeP46.T.cert (slotZ .addGe)).okPropR 349 411 = true :=
  TCertI.okPropR_of_K gAddGeP46I rfl (slotZ .addGe) keysZAddGe_ok gAddGeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddGeP46_h : pinHeadB (slotZ .addGe) gAddGeP46 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP46_w : gAddGeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP46_j0 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP46 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP46_j1 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP46 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP46_j2 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP46 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP46_j3 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP46 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP46_j4 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP46 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddGeP46_j5 : pinJR (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP46 15 18 = true := by decide +kernel

/-- The pin check of `gAddGeP46`, from its parts. -/
theorem gAddGeP46_ok : pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps gAddGeP46 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddGeP46_b gAddGeP46_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP46_p0) gAddGeP46_p1) gAddGeP46_p2) gAddGeP46_p3) gAddGeP46_p4) gAddGeP46_p5) gAddGeP46_p6)) gAddGeP46_h gAddGeP46_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddGeP46_j0) gAddGeP46_j1) gAddGeP46_j2) gAddGeP46_j3) gAddGeP46_j4) gAddGeP46_j5)

end

end ArtGallery.Orthogonal.Hard
