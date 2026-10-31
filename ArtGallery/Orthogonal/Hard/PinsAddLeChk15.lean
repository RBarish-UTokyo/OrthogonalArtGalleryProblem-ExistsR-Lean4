module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 15 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP38_b : (gAddLeP38.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP38_n : (gAddLeP38.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP38_p0 : (gAddLeP38.T.cert (slotZ .addLe)).okPropR 0 299 = true :=
  TCertI.okPropR_of_K gAddLeP38I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP38H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP38_p1 : (gAddLeP38.T.cert (slotZ .addLe)).okPropR 299 397 = true :=
  TCertI.okPropR_of_K gAddLeP38I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP38H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP38_h : pinHeadB (slotZ .addLe) gAddLeP38 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP38_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP38_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP38 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP38_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP38 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP38_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP38 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP38_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP38 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP38_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP38 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP38_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP38 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP38`, from its parts. -/
theorem gAddLeP38_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP38 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP38_b gAddLeP38_n (allR_join (by norm_num) (by norm_num) (gAddLeP38_p0) gAddLeP38_p1)) gAddLeP38_h gAddLeP38_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP38_j0) gAddLeP38_j1) gAddLeP38_j2) gAddLeP38_j3) gAddLeP38_j4) gAddLeP38_j5)

end

end ArtGallery.Orthogonal.Hard
