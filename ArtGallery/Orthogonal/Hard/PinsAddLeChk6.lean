module

public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ
public import ArtGallery.Orthogonal.Hard.PinSplit

/-!
# Pin checks of the group `slot addLe`, part 6 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
theorem gAddLeP19_b : (gAddLeP19.T.cert (slotZ .addLe)).okBase = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP19_n : (gAddLeP19.T.cert (slotZ .addLe)).cs.length ≤ 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP19_p0 : (gAddLeP19.T.cert (slotZ .addLe)).okPropR 0 94 = true :=
  TCertI.okPropR_of_K gAddLeP19I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP19_p1 : (gAddLeP19.T.cert (slotZ .addLe)).okPropR 94 150 = true :=
  TCertI.okPropR_of_K gAddLeP19I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP19_p2 : (gAddLeP19.T.cert (slotZ .addLe)).okPropR 150 194 = true :=
  TCertI.okPropR_of_K gAddLeP19I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP19_p3 : (gAddLeP19.T.cert (slotZ .addLe)).okPropR 194 227 = true :=
  TCertI.okPropR_of_K gAddLeP19I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP19_p4 : (gAddLeP19.T.cert (slotZ .addLe)).okPropR 227 257 = true :=
  TCertI.okPropR_of_K gAddLeP19I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP19_p5 : (gAddLeP19.T.cert (slotZ .addLe)).okPropR 257 397 = true :=
  TCertI.okPropR_of_K gAddLeP19I rfl (slotZ .addLe) keysZAddLe_ok gAddLeP19H (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gAddLeP19_h : pinHeadB (slotZ .addLe) gAddLeP19 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP19_w : gAddLeWs.length ≤ 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP19_j0 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP19 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP19_j1 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP19 3 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP19_j2 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP19 6 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP19_j3 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP19 9 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP19_j4 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP19 12 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gAddLeP19_j5 : pinJR (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP19 15 18 = true := by decide +kernel

/-- The pin check of `gAddLeP19`, from its parts. -/
theorem gAddLeP19_ok : pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps gAddLeP19 = true :=
  pinB_of_parts (LCert.ok_of_parts gAddLeP19_b gAddLeP19_n (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP19_p0) gAddLeP19_p1) gAddLeP19_p2) gAddLeP19_p3) gAddLeP19_p4) gAddLeP19_p5)) gAddLeP19_h gAddLeP19_w
    (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (allR_join (by norm_num) (by norm_num) (gAddLeP19_j0) gAddLeP19_j1) gAddLeP19_j2) gAddLeP19_j3) gAddLeP19_j4) gAddLeP19_j5)

end

end ArtGallery.Orthogonal.Hard
