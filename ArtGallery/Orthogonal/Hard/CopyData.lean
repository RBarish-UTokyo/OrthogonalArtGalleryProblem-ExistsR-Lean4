module

public import ArtGallery.Orthogonal.Hard.PosO
public import ArtGallery.Orthogonal.Hard.SpotCertsInvGeChk0
public import ArtGallery.Orthogonal.Hard.SpotCertsInvGeChk1
public import ArtGallery.Orthogonal.Hard.SpotCertsInvGeChk2
public import ArtGallery.Orthogonal.Hard.SpotCertsInvGeChk3
public import ArtGallery.Orthogonal.Hard.SpotCertsInvRevLeChk0
public import ArtGallery.Orthogonal.Hard.SpotCertsInvRevLeChk1
public import ArtGallery.Orthogonal.Hard.SpotCertsInvRevLeChk2
public import ArtGallery.Orthogonal.Hard.SpotCertsInvRevLeChk3
public import ArtGallery.Orthogonal.Hard.SpotCertsInvRevLeChk4
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk0
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk1
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk2
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk3
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk4
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk5
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk6
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk7
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk8
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk9
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk10
public import ArtGallery.Orthogonal.Hard.SpotCertsAddLeChk11
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk0
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk1
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk2
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk3
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk4
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk5
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk6
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk7
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk8
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk9
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk10
public import ArtGallery.Orthogonal.Hard.SpotCertsAddGeChk11

/-!
# The witnesses of a slot, for the copy exclusion

Every witness of a slot is an input (witness `2m`), a helper with a spot certificate
(`slotSCs`, `spotFarB`), or a box below the floor robustly outside the partial-visibility region
of the copy nook of every input of the slot (`boxPVB`: by `x ≥ b − 14 − (9/10) y`, or for an LE
copy `x ≥ b − y`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade

/-- The spot certificates of the helpers of a slot. -/
def slotSCs : TKind → List (ℕ × TCert)
  | .invGe => gInvGeSCs
  | .invRevLe => gInvRevLeSCs
  | .addLe => gAddLeSCs
  | .addGe => gAddGeSCs

theorem slotSCs_ok (k : TKind) : ∀ p ∈ slotSCs k, spotFarB (slotD k) p.1 p.2 = true := by
  cases k
  · simp only [slotSCs, gInvGeSCs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    exact ⟨gInvGeSC0T_ok, gInvGeSC1T_ok, gInvGeSC2T_ok, gInvGeSC3T_ok⟩
  · simp only [slotSCs, gInvRevLeSCs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    exact ⟨gInvRevLeSC0T_ok, gInvRevLeSC1T_ok, gInvRevLeSC2T_ok, gInvRevLeSC3T_ok,
      gInvRevLeSC4T_ok⟩
  · simp only [slotSCs, gAddLeSCs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    exact ⟨gAddLeSC0T_ok, gAddLeSC1T_ok, gAddLeSC2T_ok, gAddLeSC3T_ok, gAddLeSC4T_ok,
      gAddLeSC5T_ok, gAddLeSC6T_ok, gAddLeSC7T_ok, gAddLeSC8T_ok, gAddLeSC9T_ok, gAddLeSC10T_ok,
      gAddLeSC11T_ok⟩
  · simp only [slotSCs, gAddGeSCs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    exact ⟨gAddGeSC0T_ok, gAddGeSC1T_ok, gAddGeSC2T_ok, gAddGeSC3T_ok, gAddGeSC4T_ok,
      gAddGeSC5T_ok, gAddGeSC6T_ok, gAddGeSC7T_ok, gAddGeSC8T_ok, gAddGeSC9T_ok, gAddGeSC10T_ok,
      gAddGeSC11T_ok⟩

/-- A box spot below the floor, robustly outside the partial-visibility region of the copy nook
of every input of the slot. -/
def boxPVB (D : GData) (ins : List TInput) (i : ℕ) : Bool :=
  let r := D.sps.getD i LR.dflt
  decide (r.y0.2 = 0 ∧ r.y1.2 = 0 ∧ -140 ≤ r.y0.1 ∧ r.y1.1 ≤ 0 ∧ -100 ≤ r.x0 ∧ r.x1 ≤ 560) &&
    ins.all fun t => decide (r.x1 < t.lx - 14 - 9 / 10 * r.y1.1 ∨ (t.ge = false ∧ r.x1 < t.lx - r.y1.1))

/-- **The classification of the witnesses of a slot.** -/
def slotClassB (k : TKind) : Bool :=
  (List.range (slotD k).Ws.length).all fun i =>
    decide (i % 2 = 0 ∧ i / 2 < (oTmplInputs k).length) || (slotSCs k).any (fun p => decide (p.1 = i)) ||
      boxPVB (slotD k) (oTmplInputs k) i

theorem slotClass_ok (k : TKind) : slotClassB k = true := by cases k <;> decide +kernel

/-- The inputs of a slot are spaced by at least `44` and lie in `[30, 600]`. -/
theorem oTmplInputs_sep (k : TKind) :
    (List.range (oTmplInputs k).length).all (fun m => (List.range (oTmplInputs k).length).all
      fun m' => decide (m = m') || decide (44 ≤ |((oTmplInputs k).getD m ⟨0, false, 0, false⟩).lx -
        ((oTmplInputs k).getD m' ⟨0, false, 0, false⟩).lx|)) = true := by
  cases k <;> decide +kernel

/-- The spots of the variable helpers: above the ceiling, and below the floor near the line. -/
theorem gVarSps_helpers : gVarSps.getD 1 LR.dflt = ⟨-11 / 4, -11 / 4, (-2 / 3, 20 / 9), (-2 / 3, 20 / 9)⟩ ∧
    (gVarSps.getD 2 LR.dflt).x1 = 11 / 4 ∧ (gVarSps.getD 2 LR.dflt).y1.2 ≤ 0 ∧
    (gVarSps.getD 2 LR.dflt).y1.1 ≤ 0 := by decide +kernel

end

end ArtGallery.Orthogonal.Hard
