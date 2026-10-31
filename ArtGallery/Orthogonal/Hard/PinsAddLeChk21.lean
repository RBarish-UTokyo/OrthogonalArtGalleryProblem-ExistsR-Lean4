module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 21 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP46_b : (gAddLeP46.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP46_n : (gAddLeP46.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP46_p0 : (gAddLeP46.T.cert (slotZ .addLe)).okPropR 0 301 = true :=
  TCertI.okPropR_of_K gAddLeP46I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP46_p1 : (gAddLeP46.T.cert (slotZ .addLe)).okPropR 301 313 = true :=
  TCertI.okPropR_of_K gAddLeP46I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP46_p2 : (gAddLeP46.T.cert (slotZ .addLe)).okPropR 313 321 = true :=
  TCertI.okPropR_of_K gAddLeP46I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP46_p3 : (gAddLeP46.T.cert (slotZ .addLe)).okPropR 321 328 = true :=
  TCertI.okPropR_of_K gAddLeP46I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP46_p4 : (gAddLeP46.T.cert (slotZ .addLe)).okPropR 328 335 = true :=
  TCertI.okPropR_of_K gAddLeP46I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP46_p5 : (gAddLeP46.T.cert (slotZ .addLe)).okPropR 335 397 = true :=
  TCertI.okPropR_of_K gAddLeP46I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP46H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP46_h : pinHeadB (slotZ .addLe) gAddLeP46 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP46_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP46_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP46 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP46_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP46 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP46_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP46 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP46_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP46 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP46_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP46 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP46_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP46 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP46`, from its parts. -/
theorem gAddLeP46_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP46 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP46_b gAddLeP46_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP46_p0) gAddLeP46_p1) gAddLeP46_p2) gAddLeP46_p3) gAddLeP46_p4) gAddLeP46_p5)) gAddLeP46_h gAddLeP46_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP46_j0) gAddLeP46_j1) gAddLeP46_j2) gAddLeP46_j3) gAddLeP46_j4) gAddLeP46_j5)

end

end ArtGallery.Orthogonal.Hard
