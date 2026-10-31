module

public import ArtGallery.Orthogonal.Hard.PinsVar
public import ArtGallery.Orthogonal.Hard.PinSplit
public import ArtGallery.Orthogonal.Hard.PinsVarHints
public import ArtGallery.Orthogonal.Hard.PropKeysZ

/-!
# Pin checks of the group `var`, part 1 (generated)
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gVarP6_b : (gVarP6.T.cert (varZ)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gVarP6_p : (gVarP6.T.cert (varZ)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gVarP6I rfl (varZ) keysZVar_ok gVarP6H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gVarP6_j : pinJR varZ gVarWs gVarRks gVarSps gVarP6 0 1000 = true := by decide +kernel
/-- The pin check of `gVarP6`, from its parts. -/
theorem gVarP6_ok : pinB varZ gVarWs gVarRks gVarSps gVarP6 = true :=
  pinB_of_parts (LCert.ok_of_parts gVarP6_b (n := 100000) (by decide +kernel) gVarP6_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gVarP6_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gVarP7_b : (gVarP7.T.cert (varZ)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gVarP7_p : (gVarP7.T.cert (varZ)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gVarP7I rfl (varZ) keysZVar_ok gVarP7H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gVarP7_j : pinJR varZ gVarWs gVarRks gVarSps gVarP7 0 1000 = true := by decide +kernel
/-- The pin check of `gVarP7`, from its parts. -/
theorem gVarP7_ok : pinB varZ gVarWs gVarRks gVarSps gVarP7 = true :=
  pinB_of_parts (LCert.ok_of_parts gVarP7_b (n := 100000) (by decide +kernel) gVarP7_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gVarP7_j


set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem gVarP8_b : (gVarP8.T.cert (varZ)).okBase = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem gVarP8_p : (gVarP8.T.cert (varZ)).okPropR 0 100000 = true :=
  TCertI.okPropR_of_K gVarP8I rfl (varZ) keysZVar_ok gVarP8H (by decide +kernel)
set_option maxRecDepth 100000 in
theorem gVarP8_j : pinJR varZ gVarWs gVarRks gVarSps gVarP8 0 1000 = true := by decide +kernel
/-- The pin check of `gVarP8`, from its parts. -/
theorem gVarP8_ok : pinB varZ gVarWs gVarRks gVarSps gVarP8 = true :=
  pinB_of_parts (LCert.ok_of_parts gVarP8_b (n := 100000) (by decide +kernel) gVarP8_p)
    (by decide +kernel) (n := 1000) (by decide +kernel) gVarP8_j


set_option maxRecDepth 100000 in
theorem gVarHQ_ok : gVarHQ.all (hqB varZ gVarWs gVarPs gVarSps) = true := by decide +kernel

end

end ArtGallery.Orthogonal.Hard
