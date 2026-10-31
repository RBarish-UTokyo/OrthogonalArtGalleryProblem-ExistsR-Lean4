module

public import ArtGallery.Orthogonal.Hard.CopyData
public import ArtGallery.Orthogonal.Hard.SpotLow
public import ArtGallery.Orthogonal.Hard.SpotCertsVar

/-!
# Guards that see no gadget nook

Tools for the exclusion arguments of the gadget nooks (which lie in the low strip
`−400 ≤ y ≤ 0` of their slot):

* `AssignO.sc_low`: a helper of a slot (a witness with a spot certificate) sees no point of the
  low strip outside `g − 1050 < x < g + 1150` (`slotLowB`: the escaping cones of the spot
  certificates on the low strip);
* `AssignO.sc_unseen`: a helper of a slot sees no point of a nook segment of its own slot
  (`slotUnseenB`: `rectUnseenB` on the spot certificates), except for the listed pairs
  `nookExempt` (helpers whose wall line ends at an end of the nook segment);
* `AssignO.varh_low`: a helper of a variable sees no point of the low strip outside
  `a − 100 < x < a + 100` (`SpotCertsVar.lean`);
* `AssignO.basin_low`: the basin guard lies below the floor.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-! ### Data -/

/-- The escaping cones of the spot certificates of the helpers of a slot stay in
`−1050 < x < 1150` on the low strip. -/
def slotLowB (k : TKind) : Bool := (slotSCs k).all fun p => lowSlabB p.2 (-1050) 1150

theorem slotLow_ok (k : TKind) : slotLowB k = true := by cases k <;> decide +kernel

/-- The nook segments of the gadgets of a slot kind (local frame): Stade's segments of the
inversion gadgets; the parts of the nook lines of the addition gadgets that are edges of the
polygon, in the order `x, y, z`. -/
def oNooks : TKind → List LR
  | .invGe => [⟨61, 79, (-78, 0), (-78, 0)⟩]
  | .invRevLe => [⟨38, 56, (-22, 0), (-22, 0)⟩]
  | .addLe => [⟨30, 30, (-3327 / 32, 0), (-6627 / 64, 0)⟩, ⟨30, 30, (-174, 0), (-11085 / 64, 0)⟩,
      ⟨30, 30, (-3049 / 24, 0), (-24335 / 192, 0)⟩]
  | .addGe => [⟨30, 30, (-2649 / 64, 0), (-2595 / 64, 0)⟩, ⟨30, 30, (-855 / 8, 0), (-3381 / 32, 0)⟩,
      ⟨30, 30, (-6001 / 96, 0), (-2975 / 48, 0)⟩]

/-- The pairs (helper witness, nook) not covered by `slotUnseenB`: the helper's wall line ends
at an end of the nook segment. -/
def nookExempt : TKind → List (ℕ × ℕ)
  | .invRevLe => [(4, 0)]
  | .addLe => [(7, 0), (11, 1), (9, 2)]
  | .addGe => [(7, 0), (10, 1), (11, 1), (9, 2)]
  | _ => []

/-- The helpers of a slot see no point of the nook segments of the slot. -/
def slotUnseenB (k : TKind) : Bool :=
  (slotSCs k).all fun p => (List.range (oNooks k).length).all fun j =>
    decide ((p.1, j) ∈ nookExempt k) || rectUnseenB (p.2.cert (slotD k).gs) ((oNooks k).getD j LR.dflt)

theorem slotUnseen_ok (k : TKind) : slotUnseenB k = true := by cases k <;> decide +kernel

variable {n : ℕ} {Φ : List Constraint} {G : Finset Point} (A : AssignO n Φ G)

/-- The spot certificate data of a helper of a slot, at the guard. -/
theorem AssignO.sc_data {c : Fin (paramC Φ)} {i : Fin (slotWs (cKind (gadAt Φ c))).length}
    {p : ℕ × TCert} (hp : p ∈ slotSCs (cKind (gadAt Φ c))) (hpi : p.1 = i.1) :
    (p.2.cert (slotD (cKind (gadAt Φ c))).gs).ok = true ∧
      p.2.cones.length = (groupLR (slotD (cKind (gadAt Φ c))).gs).length ∧
      A.γ (.inl (.inr (.inl ⟨c, i⟩))) ∈ (p.2.A.real (slotG n Φ c : ℚ) (Hr n Φ)).set := by
  have hsc := slotSCs_ok _ p hp
  simp only [spotFarB, Bool.and_eq_true, decide_eq_true_eq] at hsc
  obtain ⟨⟨⟨hA, ok⟩, l⟩, -⟩ := hsc
  have hsp := A.tspot (t := .inr (.inl ⟨c, i⟩)) (by simp [tgrp])
  simp only [tinst] at hsp
  rw [← hpi, hA] at hsp
  exact ⟨ok, l, hsp⟩

/-- **A slot helper sees nothing of the low strip far from its slot.** -/
theorem AssignO.sc_low {c : Fin (paramC Φ)} {i : Fin (slotWs (cKind (gadAt Φ c))).length}
    {p : ℕ × TCert} (hp : p ∈ slotSCs (cKind (gadAt Φ c))) (hpi : p.1 = i.1) {s : Point}
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ (.inl (.inr (.inl ⟨c, i⟩)))) s)
    (h1 : -400 ≤ s.2) (h2 : s.2 ≤ 0) :
    (slotG n Φ c : ℝ) - 1050 < s.1 ∧ s.1 < (slotG n Φ c : ℝ) + 1150 := by
  obtain ⟨ok, l, hw⟩ := A.sc_data hp hpi
  have hlow := List.all_eq_true.1 (slotLow_ok _) p hp
  have := spot_low_x (slotD_valid _) (by rw [slotD_gs]; exact slotZ_in c.isLt) ok l hlow hw hs h1 h2
  rw [slotD_x0, slotD_x1] at this
  have e1 : min ((-460 : ℚ) : ℝ) ((-1050 : ℚ) : ℝ) = -1050 := by norm_num
  have e2 : max ((560 : ℚ) : ℝ) ((1150 : ℚ) : ℝ) = 1150 := by norm_num
  push_cast at this e1 e2
  rw [e1, e2] at this
  constructor <;> linarith [this.1, this.2]

/-- **A slot helper sees no point of a nook segment of its slot** (non-exempt pairs). -/
theorem AssignO.sc_unseen {c : Fin (paramC Φ)} {i : Fin (slotWs (cKind (gadAt Φ c))).length}
    {p : ℕ × TCert} (hp : p ∈ slotSCs (cKind (gadAt Φ c))) (hpi : p.1 = i.1) {j : ℕ}
    (hj : j < (oNooks (cKind (gadAt Φ c))).length) (hex : (p.1, j) ∉ nookExempt (cKind (gadAt Φ c)))
    {z : Point} (hz : z ∈ (((oNooks (cKind (gadAt Φ c)))[j]).real (slotG n Φ c : ℚ) (Hr n Φ)).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ (.inl (.inr (.inl ⟨c, i⟩)))) z) :
    False := by
  obtain ⟨ok, l, hw⟩ := A.sc_data hp hpi
  have hu := List.all_eq_true.1 (slotUnseen_ok _) p hp
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hu
  rcases hu j hj with h | h
  · exact hex h
  rw [List.getD_eq_getElem _ _ hj] at h
  have hb := (groupOK_parts (slotD_valid (cKind (gadAt Φ c))).group).1
  exact rectUnseen_sound (by rw [slotD_gs]; exact slotZ_in c.isLt) hb ok l h hw hz hs

/-- **A variable helper sees nothing of the low strip far from its variable.** -/
theorem AssignO.varh_low (k : Fin n) (i : Fin gVarWs.length) (hi : i.1 ≠ 0) {s : Point}
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ (.inl (.inl (k, i)))) s)
    (h1 : -400 ≤ s.2) (h2 : s.2 ≤ 0) :
    ((varA Φ k : ℚ) : ℝ) - 100 < s.1 ∧ s.1 < ((varA Φ k : ℚ) : ℝ) + 100 := by
  have hsp := A.tspot (t := .inl (k, i)) (by simp [tgrp])
  simp only [tinst] at hsp
  have hi' : i.1 = 1 ∨ i.1 = 2 := by have := i.isLt; have := gVarWs_len; omega
  obtain ⟨T, hT⟩ : ∃ T, spotVarB i.1 T = true := by
    rcases hi' with h | h
    · exact ⟨_, h ▸ gVarSC0T_ok⟩
    · exact ⟨_, h ▸ gVarSC1T_ok⟩
  simp only [spotVarB, Bool.and_eq_true, decide_eq_true_eq] at hT
  obtain ⟨⟨⟨hA, ok⟩, l⟩, low⟩ := hT
  rw [hA] at hsp
  have := spot_low_x gVarD_valid (varZ_in k.isLt) ok l low hsp hs h1 h2
  have e0 : gVarD.x0 = -16 := rfl
  have e1 : gVarD.x1 = 16 := rfl
  rw [e0, e1] at this
  have e2 : min ((-16 : ℚ) : ℝ) ((-100 : ℚ) : ℝ) = -100 := by norm_num
  have e3 : max ((16 : ℚ) : ℝ) ((100 : ℚ) : ℝ) = 100 := by norm_num
  push_cast at this e2 e3
  rw [e2, e3] at this
  push_cast
  constructor <;> linarith [this.1, this.2]

/-- **The basin guard lies below the floor.** -/
theorem AssignO.basin_low (i : Fin gBasinWs.length) : (A.γ (.inl (.inr (.inr i)))).2 < -1 / 4 := by
  have hs := sees_symm (A.spot _ _ (cwit_mem_WO (n := n) (Φ := Φ) (.inl (.inr (.inr i)))))
  have hi : i.1 = 0 := by have := i.isLt; simp [gBasinWs] at this; omega
  have hW : gBasinWs[i] = gBasinW0 := by
    obtain ⟨_ | m, h⟩ := i
    · rfl
    · simp [gBasinWs] at h
  simp only [cwit, twit, hW] at hs
  have hok := (groupOK_parts gBasin_ok).2.1 gBasinW0 (by simp [gBasinWs])
  rcases WCert.sees basinZ_in hok.1 hok.2.1 (groupOK_parts gBasin_ok).1 hs with
    ⟨q, hq, -, -, hpU⟩ | ⟨hC, -⟩
  · have hk' : q.2.1 < (basinZ.map GZ.box).length := LCert.box_lt hok.1 hq
    have hk1 : q.2.1 = 0 := by simp [basinZ] at hk'; omega
    rw [hk1] at hpU
    obtain ⟨-, -, -, hy⟩ := hpU
    have := hy (-1 / 4, 0) (by simp [basinZ, GZ.box, floorBoxL, LBox.shift])
    simpa [AH.ev] using this
  · simp [gBasinW0, optCone] at hC

end

end ArtGallery.Orthogonal.Hard
