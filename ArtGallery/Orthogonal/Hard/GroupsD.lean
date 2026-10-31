module

public import ArtGallery.Orthogonal.Hard.PinValid

/-!
# The pin data of all template groups

The group data of the slots by kind (`slotD`) and of the basin (`gBasinD`, no pins), their checks,
and two facts about the pin targets `D.W ox H i` of a witness of a valid group instance: they are
boundary points (`GData.W_bd`), and their viewers lie in the strip of the group (`GData.W_viewer`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-- The pin data of a slot of kind `k`. -/
def slotD : TKind → GData
  | .invGe => gInvGeD
  | .invRevLe => gInvRevLeD
  | .addLe => gAddLeD
  | .addGe => gAddGeD

/-- The spot kinds of a slot of kind `k`. -/
def slotSK : TKind → List SpotK
  | .invGe => gInvGeSK
  | .invRevLe => gInvRevLeSK
  | .addLe => gAddLeSK
  | .addGe => gAddGeSK

theorem slotD_valid (k : TKind) : (slotD k).Valid := by
  cases k
  · exact gInvGeD_valid
  · exact gInvRevLeD_valid
  · exact gAddLeD_valid
  · exact gAddGeD_valid

theorem slotD_spots (k : TKind) : spotsB (slotD k) (slotSK k) = true := by
  cases k
  · exact gInvGeD_spots
  · exact gInvRevLeD_spots
  · exact gAddLeD_spots
  · exact gAddGeD_spots

theorem slotD_gs (k : TKind) : (slotD k).gs = slotZ k := by cases k <;> rfl

theorem slotD_Ws (k : TKind) : (slotD k).Ws = slotWs k := by cases k <;> rfl

theorem slotD_x0 (k : TKind) : (slotD k).x0 = -460 := by cases k <;> rfl

theorem slotD_x1 (k : TKind) : (slotD k).x1 = 560 := by cases k <;> rfl

/-- The basin group: no pins. -/
def gBasinD : GData := ⟨basinZ, gBasinWs, gBasinTs, [], [], [], [], [], [], 0, 40⟩

theorem gBasinD_valid : gBasinD.Valid where
  group := gBasin_ok
  pins := by simp [gBasinD]
  hq := rfl
  ext := (Bool.and_eq_true _ _ ▸ basin_ext).1
  pext := rfl
  ex := by decide
  bd := by decide

theorem gVarD_vtx : gVarD.Ws.all (vtxB gVarD.gs) = true := (Bool.and_eq_true _ _ ▸ var_ext).2

theorem slotD_vtx (k : TKind) : (slotD k).Ws.all (vtxB (slotD k).gs) = true := by
  rw [slotD_Ws, slotD_gs]; exact (Bool.and_eq_true _ _ ▸ slot_ext k).2

theorem gBasinD_vtx : gBasinD.Ws.all (vtxB gBasinD.gs) = true := (Bool.and_eq_true _ _ ▸ basin_ext).2

variable {n : ℕ} {Φ : List Constraint}

/-- **The pin targets are boundary points.** -/
theorem GData.W_bd {D : GData} (hD : D.Valid) {ox : ℚ} (hgs : ∀ g ∈ D.gs, g.InPoly n Φ ox)
    (hv : D.Ws.all (vtxB D.gs) = true) {i : ℕ} (hi : i < D.Ws.length) {w : Point}
    (hw : w ∈ D.W ox (Hr n Φ) i) : w ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  rcases hw with hw | ⟨k, hk, -, hwk⟩
  · rw [mem_singleton_iff] at hw
    subst hw
    rw [List.getD_eq_getElem _ _ hi]
    exact witness_boundary hgs (List.all_eq_true.1 hv _ (List.getElem_mem hi))
  · exact GData.pin_bd hD hgs hk hwk

/-- **The viewers of the pin targets lie in the strip of the group.** -/
theorem GData.W_viewer {D : GData} (hD : D.Valid) {ox : ℚ} (hgs : ∀ g ∈ D.gs, g.InPoly n Φ ox)
    {i : ℕ} (hi : i < D.Ws.length) {w p : Point} (hw : w ∈ D.W ox (Hr n Φ) i)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p) :
    (ox : ℝ) + D.x0 < p.1 ∧ p.1 < (ox : ℝ) + D.x1 := by
  rcases hw with hw | ⟨k, hk, -, hwk⟩
  · rw [mem_singleton_iff] at hw
    subst hw
    rw [List.getD_eq_getElem _ _ hi] at hs
    exact group_viewer_x hD.group hD.ext hgs (List.getElem_mem hi) hs
  · exact GData.pin_x hD hgs hk hwk hs

end

end ArtGallery.Orthogonal.Hard
