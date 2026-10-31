module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 8 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP21_b : (gAddLeP21.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP21_n : (gAddLeP21.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP21_p0 : (gAddLeP21.T.cert (slotZ .addLe)).okPropR 0 397 = true :=
  TCertI.okPropR_of_K gAddLeP21I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP21H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP21_h : pinHeadB (slotZ .addLe) gAddLeP21 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP21_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP21_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP21 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP21_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP21 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP21_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP21 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP21_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP21 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP21_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP21 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP21_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP21 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP21`, from its parts. -/
theorem gAddLeP21_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP21 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP21_b gAddLeP21_n (gAddLeP21_p0)) gAddLeP21_h gAddLeP21_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP21_j0) gAddLeP21_j1) gAddLeP21_j2) gAddLeP21_j3) gAddLeP21_j4) gAddLeP21_j5)

end

end ArtGallery.Orthogonal.Hard
