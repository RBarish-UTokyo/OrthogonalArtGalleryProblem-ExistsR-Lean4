module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 2 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP12_b : (gAddLeP12.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP12_n : (gAddLeP12.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP12_p0 : (gAddLeP12.T.cert (slotZ .addLe)).okPropR 0 32 = true :=
  TCertI.okPropR_of_K gAddLeP12I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP12H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP12_p1 : (gAddLeP12.T.cert (slotZ .addLe)).okPropR 32 52 = true :=
  TCertI.okPropR_of_K gAddLeP12I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP12H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP12_p2 : (gAddLeP12.T.cert (slotZ .addLe)).okPropR 52 77 = true :=
  TCertI.okPropR_of_K gAddLeP12I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP12H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP12_p3 : (gAddLeP12.T.cert (slotZ .addLe)).okPropR 77 120 = true :=
  TCertI.okPropR_of_K gAddLeP12I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP12H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP12_p4 : (gAddLeP12.T.cert (slotZ .addLe)).okPropR 120 205 = true :=
  TCertI.okPropR_of_K gAddLeP12I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP12H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP12_p5 : (gAddLeP12.T.cert (slotZ .addLe)).okPropR 205 397 = true :=
  TCertI.okPropR_of_K gAddLeP12I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP12H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP12_h : pinHeadB (slotZ .addLe) gAddLeP12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP12_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP12_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP12 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP12_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP12 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP12_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP12 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP12_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP12 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP12_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP12 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP12_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP12 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP12`, from its parts. -/
theorem gAddLeP12_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP12 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP12_b gAddLeP12_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP12_p0) gAddLeP12_p1) gAddLeP12_p2) gAddLeP12_p3) gAddLeP12_p4) gAddLeP12_p5)) gAddLeP12_h gAddLeP12_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP12_j0) gAddLeP12_j1) gAddLeP12_j2) gAddLeP12_j3) gAddLeP12_j4) gAddLeP12_j5)

end

end ArtGallery.Orthogonal.Hard
