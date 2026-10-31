module

public import ArtGallery.Orthogonal.Hard.PinsVar
public import ArtGallery.Orthogonal.Hard.PinSplit
public import ArtGallery.Orthogonal.Hard.PinsVarHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ

/-!
# Pin checks of the group `var`, part 0 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gVarP0_b : (gVarP0.T.cert (varZ)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gVarP0_p : (gVarP0.T.cert (varZ)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gVarP0I rfl (varZ) keysZVar_ok gVarP0H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gVarP0_j : pinJR varZ gVarWs gVarRks gVarSps gVarP0 0 1000 = true := by decide +kernel
/-- The pin check of `gVarP0`, from its parts. -/
theorem gVarP0_ok : pinB varZ gVarWs gVarRks gVarSps gVarP0 = true :=
  pinB_of_parts (LCert.ok_of_parts gVarP0_b (n := 100000) (by decide +kernel) gVarP0_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gVarP0_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gVarP1_b : (gVarP1.T.cert (varZ)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gVarP1_p : (gVarP1.T.cert (varZ)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gVarP1I rfl (varZ) keysZVar_ok gVarP1H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gVarP1_j : pinJR varZ gVarWs gVarRks gVarSps gVarP1 0 1000 = true := by decide +kernel
/-- The pin check of `gVarP1`, from its parts. -/
theorem gVarP1_ok : pinB varZ gVarWs gVarRks gVarSps gVarP1 = true :=
  pinB_of_parts (LCert.ok_of_parts gVarP1_b (n := 100000) (by decide +kernel) gVarP1_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gVarP1_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gVarP2_b : (gVarP2.T.cert (varZ)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gVarP2_p : (gVarP2.T.cert (varZ)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gVarP2I rfl (varZ) keysZVar_ok gVarP2H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gVarP2_j : pinJR varZ gVarWs gVarRks gVarSps gVarP2 0 1000 = true := by decide +kernel
/-- The pin check of `gVarP2`, from its parts. -/
theorem gVarP2_ok : pinB varZ gVarWs gVarRks gVarSps gVarP2 = true :=
  pinB_of_parts (LCert.ok_of_parts gVarP2_b (n := 100000) (by decide +kernel) gVarP2_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gVarP2_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gVarP3_b : (gVarP3.T.cert (varZ)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gVarP3_p : (gVarP3.T.cert (varZ)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gVarP3I rfl (varZ) keysZVar_ok gVarP3H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gVarP3_j : pinJR varZ gVarWs gVarRks gVarSps gVarP3 0 1000 = true := by decide +kernel
/-- The pin check of `gVarP3`, from its parts. -/
theorem gVarP3_ok : pinB varZ gVarWs gVarRks gVarSps gVarP3 = true :=
  pinB_of_parts (LCert.ok_of_parts gVarP3_b (n := 100000) (by decide +kernel) gVarP3_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gVarP3_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gVarP4_b : (gVarP4.T.cert (varZ)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gVarP4_p : (gVarP4.T.cert (varZ)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gVarP4I rfl (varZ) keysZVar_ok gVarP4H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gVarP4_j : pinJR varZ gVarWs gVarRks gVarSps gVarP4 0 1000 = true := by decide +kernel
/-- The pin check of `gVarP4`, from its parts. -/
theorem gVarP4_ok : pinB varZ gVarWs gVarRks gVarSps gVarP4 = true :=
  pinB_of_parts (LCert.ok_of_parts gVarP4_b (n := 100000) (by decide +kernel) gVarP4_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gVarP4_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gVarP5_b : (gVarP5.T.cert (varZ)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gVarP5_p : (gVarP5.T.cert (varZ)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gVarP5I rfl (varZ) keysZVar_ok gVarP5H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gVarP5_j : pinJR varZ gVarWs gVarRks gVarSps gVarP5 0 1000 = true := by decide +kernel
/-- The pin check of `gVarP5`, from its parts. -/
theorem gVarP5_ok : pinB varZ gVarWs gVarRks gVarSps gVarP5 = true :=
  pinB_of_parts (LCert.ok_of_parts gVarP5_b (n := 100000) (by decide +kernel) gVarP5_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gVarP5_j


end

end ArtGallery.Orthogonal.Hard
