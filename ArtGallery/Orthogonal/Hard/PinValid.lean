module

public import ArtGallery.Orthogonal.Hard.PinsVar
public import ArtGallery.Orthogonal.Hard.PinsVarChk0
public import ArtGallery.Orthogonal.Hard.PinsVarChk1
public import ArtGallery.Orthogonal.Hard.PinsInvGe
public import ArtGallery.Orthogonal.Hard.PinsInvGeChk0
public import ArtGallery.Orthogonal.Hard.PinsInvGeChk1
public import ArtGallery.Orthogonal.Hard.PinsInvGeChk2
public import ArtGallery.Orthogonal.Hard.PinsInvGeChk3
public import ArtGallery.Orthogonal.Hard.PinsInvRevLe
public import ArtGallery.Orthogonal.Hard.PinsInvRevLeChk0
public import ArtGallery.Orthogonal.Hard.PinsInvRevLeChk1
public import ArtGallery.Orthogonal.Hard.PinsInvRevLeChk2
public import ArtGallery.Orthogonal.Hard.PinsInvRevLeChk3
public import ArtGallery.Orthogonal.Hard.PinsAddLe
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk0
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk1
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk10
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk11
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk12
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk13
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk14
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk15
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk16
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk17
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk18
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk19
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk2
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk20
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk21
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk22
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk23
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk3
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk4
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk5
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk6
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk7
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk8
public import ArtGallery.Orthogonal.Hard.PinsAddLeChk9
public import ArtGallery.Orthogonal.Hard.PinsAddGe
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk0
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk1
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk10
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk11
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk12
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk13
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk14
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk15
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk16
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk17
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk18
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk19
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk2
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk20
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk21
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk22
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk3
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk4
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk5
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk6
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk7
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk8
public import ArtGallery.Orthogonal.Hard.PinsAddGeChk9
public import ArtGallery.Orthogonal.Hard.SpotBox

/-!
# The pin data of the template groups (generated)

For every template group: the exterior boxes of the exempt pins, the boundary edges of the pins,
the group data `GData`, its checks (`GData.Valid`), the segment spot data of the variable and
input guards (`spotSegB`) and the spot kinds of all witnesses (`spotsB`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational

/-- The exterior boxes of the exempt pins of the group `var`. -/
def gVarEx : List (ℕ × FBox × Bool) := [(7, ⟨(-21 / 8), (-5 / 2), ((-4 / 3), (19 / 9)), ((-1 / 3), (19 / 9))⟩, true), (8, ⟨(5 / 2), (21 / 8), ((-10 / 9), (-1 / 9)), ((-1 / 9), (-1 / 9))⟩, false)]

/-- The boundary edges of the pins of the group `var`. -/
def gVarBd : List (ℕ × ℕ) := [(1, 2), (1, 12), (1, 18), (3, 2), (3, 12), (3, 18), (2, 2), (1, 20), (3, 20)]

/-- The pin data of the group `var`. -/
def gVarD : GData := ⟨varZ, gVarWs, gVarTs, gVarPs, gVarRks, gVarSps, gVarHQ, gVarEx, gVarBd, (-16), 16⟩

set_option maxRecDepth 100000 in
/-- The checks of the group `var`. -/
theorem gVarD_valid : gVarD.Valid where
  group := gVar_ok
  pins := by
    have h : gVarPs.all (pinB varZ gVarWs gVarRks gVarSps) = true := by
      simp only [gVarPs, List.all_cons, List.all_nil, gVarP0_ok, gVarP1_ok, gVarP2_ok, gVarP3_ok, gVarP4_ok, gVarP5_ok, gVarP6_ok, gVarP7_ok, gVarP8_ok, Bool.and_true]
    exact List.all_eq_true.1 h
  hq := gVarHQ_ok
  ext := by decide +kernel
  pext := by decide +kernel
  ex := by decide +kernel
  bd := by decide +kernel

/-- The spot kinds of the witnesses of the group `var`. -/
def gVarSK : List SpotK := [.seg 0 (0, 2, 1) (2, 2, 0) 6 8 7 (0, 1) (3, 1), .helper 0, .helper 1]

set_option maxRecDepth 100000 in
theorem gVarD_spots : spotsB gVarD gVarSK = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The segment spot of witness 0 of the group `var`. -/
theorem gVarSeg0_ok : spotSegB gVarD 0 0 (0, 2, 1) (2, 2, 0) 6 8 7 (0, 1) (3, 1) = true := by
  decide +kernel

/-- The exterior boxes of the exempt pins of the group `slot invGe`. -/
def gInvGeEx : List (ℕ × FBox × Bool) := [(13, ⟨(315 / 8), (79 / 2), ((-2), (-2)), ((-7 / 4), (-2))⟩, true), (14, ⟨(299 / 8), (75 / 2), ((-5 / 3), (20 / 9)), ((-2 / 3), (20 / 9))⟩, true), (16, ⟨(201 / 2), (805 / 8), ((-2), (-2)), ((-7 / 4), (-2))⟩, false), (17, ⟨(205 / 2), (821 / 8), ((-5 / 3), (20 / 9)), ((-2 / 3), (20 / 9))⟩, false)]

/-- The boundary edges of the pins of the group `slot invGe`. -/
def gInvGeBd : List (ℕ × ℕ) := [(4, 2), (4, 12), (4, 18), (5, 18), (5, 8), (5, 2), (0, 18), (0, 8), (0, 2), (2, 4), (2, 14), (2, 20), (0, 22), (0, 0), (4, 20), (2, 0), (2, 22), (5, 0)]

/-- The pin data of the group `slot invGe`. -/
def gInvGeD : GData := ⟨(slotZ .invGe), (slotWs .invGe), (slotTs .invGe), gInvGePs, gInvGeRks, gInvGeSps, gInvGeHQ, gInvGeEx, gInvGeBd, (-460), 560⟩

set_option maxRecDepth 100000 in
/-- The checks of the group `slot invGe`. -/
theorem gInvGeD_valid : gInvGeD.Valid where
  group := slot_ok .invGe
  pins := by
    have h : gInvGePs.all (pinB (slotZ .invGe) gInvGeWs gInvGeRks gInvGeSps) = true := by
      simp only [gInvGePs, List.all_cons, List.all_nil, gInvGeP0_ok, gInvGeP1_ok, gInvGeP2_ok, gInvGeP3_ok, gInvGeP4_ok, gInvGeP5_ok, gInvGeP6_ok, gInvGeP7_ok, gInvGeP8_ok, gInvGeP9_ok, gInvGeP10_ok, gInvGeP11_ok, gInvGeP12_ok, gInvGeP13_ok, gInvGeP14_ok, gInvGeP15_ok, gInvGeP16_ok, gInvGeP17_ok, Bool.and_true]
    exact List.all_eq_true.1 h
  hq := gInvGeHQ_ok
  ext := (Bool.and_eq_true _ _ ▸ slot_ext .invGe).1
  pext := by decide +kernel
  ex := by decide +kernel
  bd := by decide +kernel

/-- The spot kinds of the witnesses of the group `slot invGe`. -/
def gInvGeSK : List SpotK := [.seg 40 (3, 2, 1) (0, 22, 0) 12 13 14 (0, 0) (6, 0), .helper 0, .seg 100 (6, 1, 0) (2, 1, 1) 15 16 17 (0, 0) (6, 0), .helper 1, .helper 2, .helper 3]

set_option maxRecDepth 100000 in
theorem gInvGeD_spots : spotsB gInvGeD gInvGeSK = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The segment spot of witness 0 of the group `slot invGe`. -/
theorem gInvGeSeg0_ok : spotSegB gInvGeD 0 40 (3, 2, 1) (0, 22, 0) 12 13 14 (0, 0) (6, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The segment spot of witness 2 of the group `slot invGe`. -/
theorem gInvGeSeg1_ok : spotSegB gInvGeD 2 100 (6, 1, 0) (2, 1, 1) 15 16 17 (0, 0) (6, 0) = true := by
  decide +kernel

/-- The exterior boxes of the exempt pins of the group `slot invRevLe`. -/
def gInvRevLeEx : List (ℕ × FBox × Bool) := [(16, ⟨(121 / 2), (485 / 8), ((-44), (-2)), ((-175 / 4), (-2))⟩, false), (17, ⟨(125 / 2), (501 / 8), ((-5 / 3), (20 / 9)), ((-2 / 3), (20 / 9))⟩, false), (19, ⟨(209 / 2), (837 / 8), ((-2), (-2)), ((-7 / 4), (-2))⟩, false), (20, ⟨(213 / 2), (853 / 8), ((-5 / 3), (20 / 9)), ((-2 / 3), (20 / 9))⟩, false)]

/-- The boundary edges of the pins of the group `slot invRevLe`. -/
def gInvRevLeBd : List (ℕ × ℕ) := [(2, 18), (2, 8), (2, 2), (4, 18), (4, 8), (4, 2), (0, 6), (0, 16), (0, 20), (0, 28), (0, 38), (0, 44), (1, 4), (1, 14), (1, 20), (0, 24), (0, 46), (2, 0), (1, 0), (1, 22), (4, 0)]

/-- The pin data of the group `slot invRevLe`. -/
def gInvRevLeD : GData := ⟨(slotZ .invRevLe), (slotWs .invRevLe), (slotTs .invRevLe), gInvRevLePs, gInvRevLeRks, gInvRevLeSps, gInvRevLeHQ, gInvRevLeEx, gInvRevLeBd, (-460), 560⟩

set_option maxRecDepth 100000 in
/-- The checks of the group `slot invRevLe`. -/
theorem gInvRevLeD_valid : gInvRevLeD.Valid where
  group := slot_ok .invRevLe
  pins := by
    have h : gInvRevLePs.all (pinB (slotZ .invRevLe) gInvRevLeWs gInvRevLeRks gInvRevLeSps) = true := by
      simp only [gInvRevLePs, List.all_cons, List.all_nil, gInvRevLeP0_ok, gInvRevLeP1_ok, gInvRevLeP2_ok, gInvRevLeP3_ok, gInvRevLeP4_ok, gInvRevLeP5_ok, gInvRevLeP6_ok, gInvRevLeP7_ok, gInvRevLeP8_ok, gInvRevLeP9_ok, gInvRevLeP10_ok, gInvRevLeP11_ok, gInvRevLeP12_ok, gInvRevLeP13_ok, gInvRevLeP14_ok, gInvRevLeP15_ok, gInvRevLeP16_ok, gInvRevLeP17_ok, gInvRevLeP18_ok, gInvRevLeP19_ok, gInvRevLeP20_ok, Bool.and_true]
    exact List.all_eq_true.1 h
  hq := gInvRevLeHQ_ok
  ext := (Bool.and_eq_true _ _ ▸ slot_ext .invRevLe).1
  pext := by decide +kernel
  ex := by decide +kernel
  bd := by decide +kernel

/-- The spot kinds of the witnesses of the group `slot invRevLe`. -/
def gInvRevLeSK : List SpotK := [.seg 60 (3, 1, 0) (0, 25, 1) 15 16 17 (0, 0) (6, 0), .helper 0, .seg 104 (5, 1, 0) (1, 1, 1) 18 19 20 (0, 0) (6, 0), .helper 1, .helper 2, .helper 3, .helper 4]

set_option maxRecDepth 100000 in
theorem gInvRevLeD_spots : spotsB gInvRevLeD gInvRevLeSK = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The segment spot of witness 0 of the group `slot invRevLe`. -/
theorem gInvRevLeSeg0_ok : spotSegB gInvRevLeD 0 60 (3, 1, 0) (0, 25, 1) 15 16 17 (0, 0) (6, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The segment spot of witness 2 of the group `slot invRevLe`. -/
theorem gInvRevLeSeg1_ok : spotSegB gInvRevLeD 2 104 (5, 1, 0) (1, 1, 1) 18 19 20 (0, 0) (6, 0) = true := by
  decide +kernel

/-- The exterior boxes of the exempt pins of the group `slot addLe`. -/
def gAddLeEx : List (ℕ × FBox × Bool) := [(37, ⟨(421 / 2), (1685 / 8), ((-324), (-2)), ((-1295 / 4), (-2))⟩, false), (38, ⟨(425 / 2), (1701 / 8), ((-5 / 3), (20 / 9)), ((-2 / 3), (20 / 9))⟩, false), (40, ⟨(741 / 2), (2965 / 8), ((-324), (-2)), ((-1295 / 4), (-2))⟩, false), (41, ⟨(745 / 2), (2981 / 8), ((-5 / 3), (20 / 9)), ((-2 / 3), (20 / 9))⟩, false), (43, ⟨(1061 / 2), (4245 / 8), ((-324), (-2)), ((-1295 / 4), (-2))⟩, false), (44, ⟨(1065 / 2), (4261 / 8), ((-5 / 3), (20 / 9)), ((-2 / 3), (20 / 9))⟩, false)]

/-- The boundary edges of the pins of the group `slot addLe`. -/
def gAddLeBd : List (ℕ × ℕ) := [(1, 18), (1, 8), (1, 2), (3, 18), (3, 8), (3, 2), (5, 18), (5, 8), (5, 2), (0, 24), (0, 14), (0, 10), (0, 46), (0, 36), (0, 30), (0, 76), (0, 66), (0, 62), (0, 98), (0, 88), (0, 82), (0, 128), (0, 118), (0, 114), (0, 150), (0, 140), (0, 134), (0, 186), (0, 196), (0, 202), (0, 158), (0, 168), (0, 174), (0, 210), (0, 220), (0, 226), (0, 154), (0, 176), (1, 0), (0, 182), (0, 204), (3, 0), (0, 206), (0, 228), (5, 0), (0, 4), (0, 56), (0, 108)]

/-- The pin data of the group `slot addLe`. -/
def gAddLeD : GData := ⟨(slotZ .addLe), (slotWs .addLe), (slotTs .addLe), gAddLePs, gAddLeRks, gAddLeSps, gAddLeHQ, gAddLeEx, gAddLeBd, (-460), 560⟩

set_option maxRecDepth 100000 in
/-- The checks of the group `slot addLe`. -/
theorem gAddLeD_valid : gAddLeD.Valid where
  group := slot_ok .addLe
  pins := by
    have h : gAddLePs.all (pinB (slotZ .addLe) gAddLeWs gAddLeRks gAddLeSps) = true := by
      simp only [gAddLePs, List.all_cons, List.all_nil, gAddLeP0_ok, gAddLeP1_ok, gAddLeP2_ok, gAddLeP3_ok, gAddLeP4_ok, gAddLeP5_ok, gAddLeP6_ok, gAddLeP7_ok, gAddLeP8_ok, gAddLeP9_ok, gAddLeP10_ok, gAddLeP11_ok, gAddLeP12_ok, gAddLeP13_ok, gAddLeP14_ok, gAddLeP15_ok, gAddLeP16_ok, gAddLeP17_ok, gAddLeP18_ok, gAddLeP19_ok, gAddLeP20_ok, gAddLeP21_ok, gAddLeP22_ok, gAddLeP23_ok, gAddLeP24_ok, gAddLeP25_ok, gAddLeP26_ok, gAddLeP27_ok, gAddLeP28_ok, gAddLeP29_ok, gAddLeP30_ok, gAddLeP31_ok, gAddLeP32_ok, gAddLeP33_ok, gAddLeP34_ok, gAddLeP35_ok, gAddLeP36_ok, gAddLeP37_ok, gAddLeP38_ok, gAddLeP39_ok, gAddLeP40_ok, gAddLeP41_ok, gAddLeP42_ok, gAddLeP43_ok, gAddLeP44_ok, gAddLeP45_ok, gAddLeP46_ok, gAddLeP47_ok, Bool.and_true]
    exact List.all_eq_true.1 h
  hq := gAddLeHQ_ok
  ext := (Bool.and_eq_true _ _ ▸ slot_ext .addLe).1
  pext := by decide +kernel
  ex := by decide +kernel
  bd := by decide +kernel

/-- The spot kinds of the witnesses of the group `slot addLe`. -/
def gAddLeSK : List SpotK := [.seg 210 (2, 1, 0) (0, 155, 1) 36 37 38 (0, 0) (6, 0), .helper 0, .seg 370 (4, 1, 0) (0, 183, 1) 39 40 41 (0, 0) (6, 0), .helper 1, .seg 530 (6, 1, 0) (0, 207, 1) 42 43 44 (0, 0) (6, 0), .helper 2, .helper 3, .helper 4, .helper 5, .helper 6, .helper 7, .helper 8, .helper 9, .helper 10, .helper 11, .box 45, .box 46, .box 47]

set_option maxRecDepth 100000 in
theorem gAddLeD_spots : spotsB gAddLeD gAddLeSK = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The segment spot of witness 0 of the group `slot addLe`. -/
theorem gAddLeSeg0_ok : spotSegB gAddLeD 0 210 (2, 1, 0) (0, 155, 1) 36 37 38 (0, 0) (6, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The segment spot of witness 2 of the group `slot addLe`. -/
theorem gAddLeSeg1_ok : spotSegB gAddLeD 2 370 (4, 1, 0) (0, 183, 1) 39 40 41 (0, 0) (6, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The segment spot of witness 4 of the group `slot addLe`. -/
theorem gAddLeSeg2_ok : spotSegB gAddLeD 4 530 (6, 1, 0) (0, 207, 1) 42 43 44 (0, 0) (6, 0) = true := by
  decide +kernel

/-- The exterior boxes of the exempt pins of the group `slot addGe`. -/
def gAddGeEx : List (ℕ × FBox × Bool) := [(37, ⟨93, (745 / 8), ((-188), (-2)), ((-751 / 4), (-2))⟩, false), (38, ⟨95, (761 / 8), ((-5 / 3), (20 / 9)), ((-2 / 3), (20 / 9))⟩, false), (40, ⟨(421 / 2), (1685 / 8), ((-188), (-2)), ((-751 / 4), (-2))⟩, false), (41, ⟨(425 / 2), (1701 / 8), ((-5 / 3), (20 / 9)), ((-2 / 3), (20 / 9))⟩, false), (43, ⟨(639 / 2), (2557 / 8), ((-188), (-2)), ((-751 / 4), (-2))⟩, false), (44, ⟨(643 / 2), (2573 / 8), ((-5 / 3), (20 / 9)), ((-2 / 3), (20 / 9))⟩, false)]

/-- The boundary edges of the pins of the group `slot addGe`. -/
def gAddGeBd : List (ℕ × ℕ) := [(1, 18), (1, 8), (1, 2), (3, 18), (3, 8), (3, 2), (5, 18), (5, 8), (5, 2), (0, 24), (0, 14), (0, 10), (0, 46), (0, 36), (0, 30), (0, 76), (0, 66), (0, 62), (0, 98), (0, 88), (0, 82), (0, 128), (0, 118), (0, 114), (0, 150), (0, 140), (0, 134), (0, 210), (0, 220), (0, 226), (0, 186), (0, 196), (0, 202), (0, 162), (0, 172), (0, 178), (0, 158), (0, 180), (1, 0), (0, 182), (0, 204), (3, 0), (0, 206), (0, 228), (5, 0), (0, 4), (0, 108), (0, 56)]

/-- The pin data of the group `slot addGe`. -/
def gAddGeD : GData := ⟨(slotZ .addGe), (slotWs .addGe), (slotTs .addGe), gAddGePs, gAddGeRks, gAddGeSps, gAddGeHQ, gAddGeEx, gAddGeBd, (-460), 560⟩

set_option maxRecDepth 100000 in
/-- The checks of the group `slot addGe`. -/
theorem gAddGeD_valid : gAddGeD.Valid where
  group := slot_ok .addGe
  pins := by
    have h : gAddGePs.all (pinB (slotZ .addGe) gAddGeWs gAddGeRks gAddGeSps) = true := by
      simp only [gAddGePs, List.all_cons, List.all_nil, gAddGeP0_ok, gAddGeP1_ok, gAddGeP2_ok, gAddGeP3_ok, gAddGeP4_ok, gAddGeP5_ok, gAddGeP6_ok, gAddGeP7_ok, gAddGeP8_ok, gAddGeP9_ok, gAddGeP10_ok, gAddGeP11_ok, gAddGeP12_ok, gAddGeP13_ok, gAddGeP14_ok, gAddGeP15_ok, gAddGeP16_ok, gAddGeP17_ok, gAddGeP18_ok, gAddGeP19_ok, gAddGeP20_ok, gAddGeP21_ok, gAddGeP22_ok, gAddGeP23_ok, gAddGeP24_ok, gAddGeP25_ok, gAddGeP26_ok, gAddGeP27_ok, gAddGeP28_ok, gAddGeP29_ok, gAddGeP30_ok, gAddGeP31_ok, gAddGeP32_ok, gAddGeP33_ok, gAddGeP34_ok, gAddGeP35_ok, gAddGeP36_ok, gAddGeP37_ok, gAddGeP38_ok, gAddGeP39_ok, gAddGeP40_ok, gAddGeP41_ok, gAddGeP42_ok, gAddGeP43_ok, gAddGeP44_ok, gAddGeP45_ok, gAddGeP46_ok, gAddGeP47_ok, Bool.and_true]
    exact List.all_eq_true.1 h
  hq := gAddGeHQ_ok
  ext := (Bool.and_eq_true _ _ ▸ slot_ext .addGe).1
  pext := by decide +kernel
  ex := by decide +kernel
  bd := by decide +kernel

/-- The spot kinds of the witnesses of the group `slot addGe`. -/
def gAddGeSK : List SpotK := [.seg (185 / 2) (2, 1, 0) (0, 159, 1) 36 37 38 (0, 0) (6, 0), .helper 0, .seg 210 (4, 1, 0) (0, 183, 1) 39 40 41 (0, 0) (6, 0), .helper 1, .seg 319 (6, 1, 0) (0, 207, 1) 42 43 44 (0, 0) (6, 0), .helper 2, .helper 3, .helper 4, .helper 5, .helper 6, .helper 7, .helper 8, .helper 9, .helper 10, .helper 11, .box 45, .box 46, .box 47]

set_option maxRecDepth 100000 in
theorem gAddGeD_spots : spotsB gAddGeD gAddGeSK = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The segment spot of witness 0 of the group `slot addGe`. -/
theorem gAddGeSeg0_ok : spotSegB gAddGeD 0 (185 / 2) (2, 1, 0) (0, 159, 1) 36 37 38 (0, 0) (6, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The segment spot of witness 2 of the group `slot addGe`. -/
theorem gAddGeSeg1_ok : spotSegB gAddGeD 2 210 (4, 1, 0) (0, 183, 1) 39 40 41 (0, 0) (6, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The segment spot of witness 4 of the group `slot addGe`. -/
theorem gAddGeSeg2_ok : spotSegB gAddGeD 4 319 (6, 1, 0) (0, 207, 1) 42 43 44 (0, 0) (6, 0) = true := by
  decide +kernel

end

end ArtGallery.Orthogonal.Hard