module

public import ArtGallery.Orthogonal.Hard.TmplRoom
public import ArtGallery.Stade.Inversion
public import ArtGallery.Orthogonal.Hard.QuadO
public import ArtGallery.Orthogonal.Hard.GroupsO

/-!
# The rooms of the inversion gadgets

`invGe` (slot origin `g`): the pocket of Stade's gadget is the rectangle
`[g + 43, g + 97] × [−78, −6]` of the orthogonal polygon (the four walls got fillers); it is a
room whose door is Stade's mouth `[P, Q]` (`igO_room`, from the zone of the template by
`tmplRoom`), and Stade's nook segment `[J, I]` lies on its floor (`ig_nook_bd`).

`invRevLe`: the part of the zone of the pocket template below the floor (the pocket, the
corridor, the hung needle and the attached wall helper) is a room whose door is the corridor
opening `[g + 59, g + 101] × {−1}`; cut by the half-plane `det(P, Q, ·) ≤ 0` it is a room with
Stade's door `[P, Q]` (`irO_room`, by `isRoom_cut`).  The open box below the nook segment is
empty (`ir_below_empty`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-! ### The pocket template and its room -/

/-- The pocket template of `invGe`. -/
def igT : ITmpl := oSlotFloor_invGe[1]

theorem igT_mem : igT ∈ oSlotFloor .invGe := List.getElem_mem _

theorem igT_fz : fz igT = zone_slot_invGe_1 := by rfl

/-- The room: the pocket below the mouth row. -/
def igRR : List GRect := [(2, 3, 0, 1)]

/-- The rest of the zone: the corridor, the strip above the floor. -/
def igNR : List GRect := [(0, 1, 2, 3), (1, 2, 1, 3), (2, 3, 1, 3), (3, 4, 1, 3), (4, 5, 2, 3)]

theorem ig_roomB : tmplRoomB (fz igT).zone igRR igNR 1 2 3 = true := by rw [igT_fz]; decide

theorem igT_X (ox : ℝ) : tzX igT (fz igT) ox 2 = ox + 43 ∧ tzX igT (fz igT) ox 3 = ox + 97 := by
  rw [igT_fz]
  simp only [tzX, zone_slot_invGe_1, igT, oSlotFloor_invGe]
  norm_num

theorem igT_Y (H : ℝ) : tzY igT (fz igT) H 0 = -78 ∧ tzY igT (fz igT) H 1 = -6 := by
  rw [igT_fz]
  simp only [tzY, zone_slot_invGe_1, igT, oSlotFloor_invGe]
  norm_num

variable {n : ℕ} {Φ : List Constraint}

section Slot

variable {c : ℕ} (hc : c < paramC Φ) (hk : cKind (gadAt Φ c) = .invGe)
include hc hk

theorem igT_zone : fzone igT (paramH n Φ) (slotG n Φ c) ∈ zfO n Φ := by
  simp only [zfO, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inr ⟨c, hc, igT, by rw [hk]; exact igT_mem, rfl⟩

/-- The room of the pocket. -/
noncomputable def igRoom (n : ℕ) (Φ : List Constraint) (c : ℕ) : Set Point :=
  gridRoomSet (tzX igT (fz igT) ((slotG n Φ c : ℚ) : ℝ)) (tzY igT (fz igT) ((paramH n Φ : ℚ) : ℝ))
    igRR

omit hc hk in
theorem mem_igRoom {z : Point} :
    z ∈ igRoom n Φ c ↔ (slotG n Φ c : ℝ) + 43 ≤ z.1 ∧ z.1 ≤ (slotG n Φ c : ℝ) + 97 ∧
      -78 ≤ z.2 ∧ z.2 ≤ -6 := by
  have hX := igT_X ((slotG n Φ c : ℚ) : ℝ)
  have hY := igT_Y ((paramH n Φ : ℚ) : ℝ)
  have e : ((slotG n Φ c : ℚ) : ℝ) = (slotG n Φ c : ℝ) := by push_cast; rfl
  simp only [igRoom, mem_gridRoomSet, igRR, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_left, realR, Rect.set, mem_ofPred_eq]
  rw [hX.1, hX.2, hY.1, hY.2, e]

/-- **The pocket is a room with door `[P, Q]`.** -/
theorem igO_room :
    (Polygon.mk ((polyO n Φ).map ratPoint)).IsRoom (igRoom n Φ c)
      (segment (igP (slotG n Φ c : ℝ)) (igQ (slotG n Φ c : ℝ))) := by
  have h := tmplRoom (n := n) (ox := (slotG n Φ c : ℚ)) (mem_allFloorTmpls_slot igT_mem)
    (igT_zone (n := n) hc hk) ig_roomB
  have hX := igT_X ((slotG n Φ c : ℚ) : ℝ)
  have hY := igT_Y ((paramH n Φ : ℚ) : ℝ)
  have e : ((slotG n Φ c : ℚ) : ℝ) = (slotG n Φ c : ℝ) := by push_cast; rfl
  rw [hX.1, hX.2, hY.2, e] at h
  exact h

omit hc hk in
theorem ig_nook_room : segment (igJ (slotG n Φ c : ℝ)) (igI (slotG n Φ c : ℝ)) ⊆ igRoom n Φ c := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := ig_nook_iff.1 hs
  rw [mem_igRoom]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The nook segment lies on the boundary (the floor edge `(43, −78) → (97, −78)` of the
template). -/
theorem ig_nook_bd :
    segment (igJ (slotG n Φ c : ℝ)) (igI (slotG n Φ c : ℝ)) ⊆
      (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  have hg : (⟨igT, false, 0⟩ : GZ) ∈ slotZ (cKind (gadAt Φ c)) := by
    rw [hk]; simp only [slotZ, List.mem_append, List.mem_map]; exact Or.inl ⟨igT, igT_mem, rfl⟩
  have hinf := GZ.infix (slotZ_in (n := n) hc _ hg)
  have hseg := seg_subset_boundary hinf (j := 3) (by simp [igT, oSlotFloor_invGe, ITmpl.inst])
  intro s hs
  apply hseg
  obtain ⟨h1, h2, h3⟩ := ig_nook_iff.1 hs
  simp only [igT, oSlotFloor_invGe, ITmpl.inst, List.map_cons, List.getElem_cons_succ,
    List.getElem_cons_zero, ratPoint]
  push_cast
  rw [mem_segment_horiz_iff (by norm_num)]
  norm_num
  refine ⟨h1, by linarith, by linarith⟩

end Slot

/-! ### `invRevLe` -/

/-- The pocket template of `invRevLe`. -/
def irT : ITmpl := oSlotFloor_invRevLe[0]

theorem irT_mem : irT ∈ oSlotFloor .invRevLe := List.getElem_mem _

theorem irT_fz : fz irT = zone_slot_invRevLe_0 := by rfl

/-- The part of the zone below the floor (and the up arm of the wall helper). -/
def irRR : List GRect :=
  [(1, 2, 12, 13), (2, 3, 12, 13), (3, 4, 10, 14), (4, 5, 9, 14), (5, 6, 10, 19), (6, 7, 10, 18),
    (7, 8, 11, 18), (8, 9, 11, 12), (8, 9, 15, 18), (9, 10, 15, 18), (10, 11, 15, 18),
    (11, 12, 8, 18), (12, 13, 3, 4), (12, 13, 8, 18), (13, 14, 3, 18), (14, 15, 3, 6),
    (14, 15, 16, 18), (15, 16, 1, 6), (15, 16, 16, 18), (16, 17, 0, 6), (16, 17, 16, 18),
    (17, 18, 1, 7), (17, 18, 16, 18), (18, 19, 1, 5), (18, 19, 16, 18), (19, 20, 2, 3),
    (19, 20, 16, 18), (20, 21, 16, 18), (21, 22, 17, 18)]

/-- The strip above the floor. -/
def irNR : List GRect :=
  [(0, 1, 18, 21), (1, 2, 18, 21), (2, 3, 20, 21), (3, 4, 20, 21), (4, 5, 20, 21), (5, 6, 20, 21),
    (6, 7, 20, 21), (7, 8, 20, 21), (8, 9, 20, 21), (9, 10, 20, 21), (10, 11, 18, 21),
    (11, 12, 18, 21), (12, 13, 18, 21), (13, 14, 18, 21), (14, 15, 18, 21), (15, 16, 18, 21),
    (16, 17, 18, 21), (17, 18, 18, 21), (18, 19, 18, 21), (19, 20, 18, 21), (20, 21, 18, 21),
    (21, 22, 18, 21), (22, 23, 18, 21)]

theorem ir_roomB : tmplRoomB (fz irT).zone irRR irNR 18 10 22 = true := by rw [irT_fz]; decide

/-- The bounds of the room rectangles used for the cut (indices). -/
theorem irRR_cut : ∀ r ∈ irRR, (r.2.2.2 ≤ 18 ∨ 10 ≤ r.1 ∨ (r.2.1 ≤ 6 ∧ r.2.2.2 ≤ 19)) ∧
    (r.2.1 ≤ 21 ∨ 17 ≤ r.2.2.1) ∧ 1 ≤ r.1 ∧ r.2.1 ≤ 22 ∧ r.2.2.2 ≤ 19 ∧
    r.1 ≤ r.2.1 ∧ r.2.2.1 ≤ r.2.2.2 := by decide

theorem ir_belowB : zoneBoxEmptyB (fz irT).zone 8 10 14 15 = true := by rw [irT_fz]; decide

theorem irT_X (ox : ℝ) : tzX irT (fz irT) ox 1 = ox + 199 / 8 ∧ tzX irT (fz irT) ox 6 < ox + 33 ∧
    tzX irT (fz irT) ox 8 = ox + 38 ∧ tzX irT (fz irT) ox 9 = ox + 325 / 8 ∧
    tzX irT (fz irT) ox 10 = ox + 59 ∧ tzX irT (fz irT) ox 21 = ox + 80 ∧
    tzX irT (fz irT) ox 22 = ox + 101 := by
  rw [irT_fz]
  simp only [tzX, zone_slot_invRevLe_0, irT, oSlotFloor_invRevLe]
  norm_num

theorem irT_Y (H : ℝ) : tzY irT (fz irT) H 14 = -415 / 16 ∧ tzY irT (fz irT) H 15 = -22 ∧
    tzY irT (fz irT) H 17 = -8 ∧ tzY irT (fz irT) H 18 = -1 ∧ tzY irT (fz irT) H 19 = -3 / 4 := by
  rw [irT_fz]
  simp only [tzY, zone_slot_invRevLe_0, irT, oSlotFloor_invRevLe]
  norm_num

section SlotR

variable {c : ℕ} (hc : c < paramC Φ) (hk : cKind (gadAt Φ c) = .invRevLe)
include hc hk

theorem irT_zone : fzone irT (paramH n Φ) (slotG n Φ c) ∈ zfO n Φ := by
  simp only [zfO, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inr ⟨c, hc, irT, by rw [hk]; exact irT_mem, rfl⟩

/-- The feature room of the pocket (door: the corridor opening). -/
noncomputable def irBig (n : ℕ) (Φ : List Constraint) (c : ℕ) : Set Point :=
  gridRoomSet (tzX irT (fz irT) ((slotG n Φ c : ℚ) : ℝ)) (tzY irT (fz irT) ((paramH n Φ : ℚ) : ℝ))
    irRR

/-- The room of Stade's pocket: the feature room cut by the mouth line. -/
noncomputable def irRoom (n : ℕ) (Φ : List Constraint) (c : ℕ) : Set Point :=
  irBig n Φ c ∩ {z | det (irP (slotG n Φ c : ℝ)) (irQ (slotG n Φ c : ℝ)) z ≤ 0}

omit hc hk in
/-- The feature room lies in `g + 199/8 ≤ x ≤ g + 101`, `y ≤ −3/4`; its points left of `g + 33`
lie below `y = −3/4`, the others with `x < g + 59` below the floor, and those right of `g + 80`
above `y = −8`. -/
theorem irBig_bounds {z : Point} (hz : z ∈ irBig n Φ c) :
    (slotG n Φ c : ℝ) + 199 / 8 ≤ z.1 ∧ z.1 ≤ (slotG n Φ c : ℝ) + 101 ∧ z.2 ≤ -3 / 4 ∧
      (z.2 ≤ -1 ∨ (slotG n Φ c : ℝ) + 59 ≤ z.1 ∨ z.1 < (slotG n Φ c : ℝ) + 33) ∧
      (z.1 ≤ (slotG n Φ c : ℝ) + 80 ∨ -8 ≤ z.2) := by
  have hf := fz_facts (mem_allFloorTmpls_slot irT_mem)
  have hD := floorTmpl_D (mem_allFloorTmpls_slot irT_mem)
  have hH : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := by exact_mod_cast paramH_ge_q n Φ
  have hφ := tz_monoX hf hD ((slotG n Φ c : ℚ) : ℝ)
  have hψ := tz_monoY hf hD hH
  have hNX : (fz irT).zone.NX = 24 := by rw [irT_fz]; rfl
  have hNY : (fz irT).zone.NY = 22 := by rw [irT_fz]; rfl
  rw [hNX] at hφ; rw [hNY] at hψ
  obtain ⟨X1, X6, -, -, X10, X21, X22⟩ := irT_X ((slotG n Φ c : ℚ) : ℝ)
  obtain ⟨-, -, Y17, Y18, Y19⟩ := irT_Y ((paramH n Φ : ℚ) : ℝ)
  have e : ((slotG n Φ c : ℚ) : ℝ) = (slotG n Φ c : ℝ) := by push_cast; rfl
  rw [← e]
  obtain ⟨r, hr, hzr⟩ := mem_gridRoomSet.1 hz
  obtain ⟨c1, c2, c5, c6, c7, c8, c9⟩ := irRR_cut r hr
  obtain ⟨y1, y2, y3, y4⟩ := hzr
  simp only [realR] at y1 y2 y3 y4
  have m := fun {i j : ℕ} (hi : i < 24) (hj : j < 24) (h : i ≤ j) =>
    hφ.monotoneOn (a := i) (b := j) (by simpa using hi) (by simpa using hj) h
  have my := fun {i j : ℕ} (hi : i < 22) (hj : j < 22) (h : i ≤ j) =>
    hψ.monotoneOn (a := i) (b := j) (by simpa using hi) (by simpa using hj) h
  have hr0 : r.1 < 24 := by omega
  have hr1 : r.2.1 < 24 := by omega
  have hr3 : r.2.2.2 < 22 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := m (by norm_num : 1 < 24) hr0 c5; linarith
  · have := m hr1 (by norm_num : 22 < 24) c6; linarith
  · have := my hr3 (by norm_num : 19 < 22) c7; linarith
  · rcases c1 with h | h | ⟨h, -⟩
    · left; have := my hr3 (by norm_num : 18 < 22) h; linarith
    · right; left; have := m (by norm_num : 10 < 24) hr0 h; linarith
    · right; right; have := m hr1 (by norm_num : 6 < 24) h; linarith
  · rcases c2 with h | h
    · left; have := m hr1 (by norm_num : 21 < 24) h; linarith
    · right; have := my (by norm_num : 17 < 22) (by omega) h; linarith

omit hc hk in
/-- A point of the mouth line in the feature room lies on the mouth. -/
theorem ir_line_mem {z : Point} (hz : z ∈ irBig n Φ c)
    (hd : det (irP (slotG n Φ c : ℝ)) (irQ (slotG n Φ c : ℝ)) z = 0) :
    z ∈ segment (irP (slotG n Φ c : ℝ)) (irQ (slotG n Φ c : ℝ)) := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := irBig_bounds hz
  set g : ℝ := (slotG n Φ c : ℝ)
  simp only [det, irP, irQ] at hd
  have hlo : g + 59 ≤ z.1 := by
    rcases b4 with h | h | h
    · linarith
    · exact h
    · nlinarith
  have hhi : z.1 ≤ g + 80 := by rcases b5 with h | h <;> linarith
  refine mem_segment_iff_lerp.2 ⟨(z.1 - g - 59) / 21, by linarith [div_nonneg (by linarith : (0:ℝ) ≤ z.1 - g - 59) (by norm_num : (0:ℝ) ≤ 21)], ?_, ?_⟩
  · rw [div_le_one (by norm_num)]; linarith
  · simp only [lerp, irP, irQ]
    refine Prod.ext ?_ ?_
    · simp only; field_simp; ring
    · simp only; field_simp; linarith

/-- **The room of Stade's `invRevLe` pocket, with door `[P, Q]`.** -/
theorem irO_room :
    (Polygon.mk ((polyO n Φ).map ratPoint)).IsRoom (irRoom n Φ c)
      (segment (irP (slotG n Φ c : ℝ)) (irQ (slotG n Φ c : ℝ))) := by
  have h := tmplRoom (n := n) (ox := (slotG n Φ c : ℚ)) (mem_allFloorTmpls_slot irT_mem)
    (irT_zone (n := n) hc hk) ir_roomB
  obtain ⟨-, -, -, -, X10, -, X22⟩ := irT_X ((slotG n Φ c : ℚ) : ℝ)
  obtain ⟨-, -, -, Y18, -⟩ := irT_Y ((paramH n Φ : ℚ) : ℝ)
  have e : ((slotG n Φ c : ℚ) : ℝ) = (slotG n Φ c : ℝ) := by push_cast; rfl
  rw [X10, X22, Y18, e] at h
  refine isRoom_cut h (f := fun z => det (irP (slotG n Φ c : ℝ)) (irQ (slotG n Φ c : ℝ)) z)
    (by unfold det; fun_prop) (fun y hy hyD hf => ?_) (fun y hy _ hf => ir_line_mem hy hf)
  rw [mem_segment_horiz_iff (by linarith)] at hyD
  obtain ⟨hy2, hy1, -⟩ := hyD
  simp only [det, irP, irQ] at hf
  have : y = irP (slotG n Φ c : ℝ) := by
    refine Prod.ext ?_ hy2
    simp only [irP]; rw [hy2] at hf; linarith
  rw [this]; exact left_mem_segment _ _

omit hc hk in
theorem ir_nook_room :
    segment (irJ (slotG n Φ c : ℝ)) (irI (slotG n Φ c : ℝ)) ⊆ irRoom n Φ c := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := ir_nook_iff.1 hs
  obtain ⟨-, -, X8, X9, X10, -, -⟩ := irT_X ((slotG n Φ c : ℚ) : ℝ)
  obtain ⟨-, Y15, -, Y18, -⟩ := irT_Y ((paramH n Φ : ℚ) : ℝ)
  have e : ((slotG n Φ c : ℚ) : ℝ) = (slotG n Φ c : ℝ) := by push_cast; rfl
  refine ⟨?_, ?_⟩
  · by_cases hx : s.1 ≤ (slotG n Φ c : ℝ) + 325 / 8
    · exact mem_gridRoomSet.2 ⟨(8, 9, 15, 18), by simp [irRR], by
        simp only [realR, Rect.set, mem_ofPred_eq]; rw [X8, X9, Y15, Y18, e]
        refine ⟨by linarith, hx, by linarith, by linarith⟩⟩
    · exact mem_gridRoomSet.2 ⟨(9, 10, 15, 18), by simp [irRR], by
        simp only [realR, Rect.set, mem_ofPred_eq]; rw [X9, X10, Y15, Y18, e]
        refine ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  · show det _ _ s ≤ 0
    simp only [det, irP, irQ]; rw [h1]; linarith

/-- **No point below the nook line sees an interior point of the nook segment.** -/
theorem ir_below {s z : Point} (hs : s ∈ segment (irJ (slotG n Φ c : ℝ)) (irI (slotG n Φ c : ℝ)))
    (hs1 : (slotG n Φ c : ℝ) + 38 < s.1) (hz : z.2 < -22)
    (hsees : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees z s) : False := by
  obtain ⟨h1, h2, h3⟩ := ir_nook_iff.1 hs
  obtain ⟨-, -, X8, -, X10, -, -⟩ := irT_X ((slotG n Φ c : ℚ) : ℝ)
  obtain ⟨Y14, Y15, -, -, -⟩ := irT_Y ((paramH n Φ : ℚ) : ℝ)
  have e : ((slotG n Φ c : ℚ) : ℝ) = (slotG n Φ c : ℝ) := by push_cast; rfl
  refine not_sees_of_empty_box_below (x0 := (slotG n Φ c : ℝ) + 38) (x1 := (slotG n Φ c : ℝ) + 59)
    (y0 := -415 / 16) (y1 := -22) (by norm_num) (fun w w1 w2 w3 w4 => ?_) h1 hs1 (by linarith) hz
    hsees
  have := zone_box_empty (n := n) (ox := (slotG n Φ c : ℚ)) (mem_allFloorTmpls_slot irT_mem)
    (irT_zone (n := n) hc hk) ir_belowB (z := w)
  rw [X8, X10, Y14, Y15, e] at this
  exact this w1 w2 w3 w4

/-- The nook segment lies on the boundary (the floor edge `(38, −22) → (60, −22)` of the
template). -/
theorem ir_nook_bd :
    segment (irJ (slotG n Φ c : ℝ)) (irI (slotG n Φ c : ℝ)) ⊆
      (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  have hg : (⟨irT, false, 0⟩ : GZ) ∈ slotZ (cKind (gadAt Φ c)) := by
    rw [hk]; simp only [slotZ, List.mem_append, List.mem_map]; exact Or.inl ⟨irT, irT_mem, rfl⟩
  have hinf := GZ.infix (slotZ_in (n := n) hc _ hg)
  have hseg := seg_subset_boundary hinf (j := 23) (by simp [irT, oSlotFloor_invRevLe, ITmpl.inst])
  intro s hs
  apply hseg
  obtain ⟨h1, h2, h3⟩ := ir_nook_iff.1 hs
  simp only [irT, oSlotFloor_invRevLe, ITmpl.inst, List.cons_append, List.nil_append,
    List.map_cons, List.getElem_cons_succ, List.getElem_cons_zero, ratPoint]
  push_cast
  rw [mem_segment_horiz_iff (by norm_num)]
  norm_num
  refine ⟨h1, by linarith, by linarith⟩

end SlotR

end

end ArtGallery.Orthogonal.Hard
