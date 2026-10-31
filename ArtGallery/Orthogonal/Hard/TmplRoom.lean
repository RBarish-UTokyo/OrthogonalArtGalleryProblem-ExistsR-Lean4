module

public import ArtGallery.Orthogonal.Hard.GridRoom
public import ArtGallery.Orthogonal.Hard.CertZone

/-!
# Rooms inside the zone of a floor template

For a floor template `t` placed at `ox` (its zone `fzone t H ox` is a zone of `polyO`), a list `RR`
of grid rectangles of its zone below the box top is a room of `polyO` with a horizontal door on
row `j` (`tmplRoom`), provided:

* every rectangle of the zone is a rectangle of `RR ++ NR` or is cut by a row into two of them
  (`splitB`);
* the room rectangles meet the rectangles of `NR` only on the door (`gridRoomB`);
* the room rectangles lie strictly inside the box (`inFloorBoxB`).

The other rectangles of the region avoid the open box `L < x < R`, `y < −1/4`
(`region_rect_floor`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Geometry Set

/-- Every zone rectangle is one of `RR ++ NR` or is cut by a row into two of them. -/
def splitB (NY : ℕ) (zr RR NR : List GRect) : Bool :=
  zr.all fun r => decide (r ∈ RR ++ NR) ||
    (List.range NY).any fun m =>
      decide ((r.1, r.2.1, r.2.2.1, m) ∈ RR ++ NR ∧ (r.1, r.2.1, m, r.2.2.2) ∈ RR ++ NR)

theorem split_cover {φ ψ : ℕ → ℝ} {NY : ℕ} {zr RR NR : List GRect} (h : splitB NY zr RR NR = true)
    {r : GRect} (hr : r ∈ zr) {z : Point} (hz : z ∈ (realR φ ψ r).set) :
    ∃ s ∈ RR ++ NR, z ∈ (realR φ ψ s).set := by
  have h' := List.all_eq_true.1 h r hr
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range] at h'
  rcases h' with h' | ⟨m, -, h1, h2⟩
  · exact ⟨r, h', hz⟩
  · obtain ⟨z1, z2, z3, z4⟩ := hz
    simp only [realR] at z1 z2 z3 z4
    by_cases hm : z.2 ≤ ψ m
    · exact ⟨_, h1, by simp only [realR]; exact ⟨z1, z2, z3, hm⟩⟩
    · exact ⟨_, h2, by simp only [realR]; exact ⟨z1, z2, (not_le.1 hm).le, z4⟩⟩

/-- The full room check of a floor zone. -/
def tmplRoomB (z : Zone) (RR NR : List GRect) (j a b : ℕ) : Bool :=
  gridRoomB z.NX z.NY RR NR j a b && inFloorBoxB RR z.L z.R z.T && splitB z.NY z.rects RR NR &&
    decide (z.R < z.NX ∧ z.T < z.NY)

variable {n : ℕ} {Φ : List Constraint}

/-- **Rooms inside a floor zone.** -/
theorem tmplRoom {t : ITmpl} (ht : t ∈ allFloorTmpls) {ox : ℚ}
    (hZ : fzone t (paramH n Φ) ox ∈ zfO n Φ) {RR NR : List GRect} {j a b : ℕ}
    (h : tmplRoomB (fz t).zone RR NR j a b = true) :
    (Polygon.mk ((polyO n Φ).map ratPoint)).IsRoom
      (gridRoomSet (tzX t (fz t) (ox : ℝ)) (tzY t (fz t) ((paramH n Φ : ℚ) : ℝ)) RR)
      (ArtGallery.segment (tzX t (fz t) (ox : ℝ) a, tzY t (fz t) ((paramH n Φ : ℚ) : ℝ) j)
        (tzX t (fz t) (ox : ℝ) b, tzY t (fz t) ((paramH n Φ : ℚ) : ℝ) j)) := by
  classical
  simp only [tmplRoomB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, hRN, hTN⟩ := h
  have hf := fz_facts ht
  have hD := floorTmpl_D ht
  have hH : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := by exact_mod_cast paramH_ge_q n Φ
  have hφ := tz_monoX hf hD (ox : ℝ)
  have hψ := tz_monoY hf hD hH
  set Z := fzone t (paramH n Φ) ox with hZdef
  set φ := tzX t (fz t) (ox : ℝ)
  set ψ := tzY t (fz t) ((paramH n Φ : ℚ) : ℝ)
  have hwf : (RR ++ NR).all (GRect.wf (fz t).zone.NX (fz t).zone.NY) = true := by
    simp only [gridRoomB, Bool.and_eq_true] at h1; exact h1.1.1
  have hT : ψ (fz t).zone.T = -1 / 4 := by
    have := tz_T hf hD ((paramH n Φ : ℚ) : ℝ)
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    exact this
  have hZrs : Z.rs = (fz t).zone.rects.map (realR φ ψ) := rfl
  have hZL : Z.L = φ (fz t).zone.L := rfl
  have hZR : Z.R = φ (fz t).zone.R := rfl
  let rest : List (Set Point) :=
    ((regionRectsO n Φ).filter fun r => decide (r ∉ Z.rs)).map Rect.set
  refine gridRoom hφ hψ h1 (rest := rest)
    (U := {z | φ (fz t).zone.L < z.1 ∧ z.1 < φ (fz t).zone.R ∧ z.2 < ψ (fz t).zone.T}) ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hA
    exact isClosed_rect_set r
  · intro z hz
    rw [filledO] at hz
    obtain ⟨r, hr, hzr⟩ := hz
    by_cases hrZ : r ∈ Z.rs
    · left
      rw [hZrs] at hrZ
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hrZ
      exact split_cover h3 hs hzr
    · right
      exact ⟨r.set, List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by simpa using hrZ⟩, rfl⟩, hzr⟩
  · intro r hr z hz
    exact inFloorBox hφ hψ hRN hTN (List.all_eq_true.2 fun s hs =>
      List.all_eq_true.1 hwf s (List.mem_append_left _ hs)) h2 r hr z hz
  · intro A hA z hzA hzU
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hA
    obtain ⟨hr, hrZ⟩ := List.mem_filter.1 hr
    simp only [decide_eq_true_eq] at hrZ
    rcases region_rect_floor hZ r hr with h' | h'
    · exact hrZ h'
    · obtain ⟨u1, u2, u3⟩ := hzU
      rw [hT] at u3
      exact h' z hzA ⟨by rw [hZL]; exact u1, by rw [hZR]; exact u2, u3⟩

/-- The full room check of a floor zone with a vertical door on column `i` between rows `a ≤ b`. -/
def tmplRoomVB (z : Zone) (RR NR : List GRect) (i a b : ℕ) : Bool :=
  gridRoomVB z.NX z.NY RR NR i a b && inFloorBoxB RR z.L z.R z.T && splitB z.NY z.rects RR NR &&
    decide (z.R < z.NX ∧ z.T < z.NY)

/-- **Rooms inside a floor zone, vertical door.** -/
theorem tmplRoomV {t : ITmpl} (ht : t ∈ allFloorTmpls) {ox : ℚ}
    (hZ : fzone t (paramH n Φ) ox ∈ zfO n Φ) {RR NR : List GRect} {i a b : ℕ}
    (h : tmplRoomVB (fz t).zone RR NR i a b = true) :
    (Polygon.mk ((polyO n Φ).map ratPoint)).IsRoom
      (gridRoomSet (tzX t (fz t) (ox : ℝ)) (tzY t (fz t) ((paramH n Φ : ℚ) : ℝ)) RR)
      (ArtGallery.segment (tzX t (fz t) (ox : ℝ) i, tzY t (fz t) ((paramH n Φ : ℚ) : ℝ) a)
        (tzX t (fz t) (ox : ℝ) i, tzY t (fz t) ((paramH n Φ : ℚ) : ℝ) b)) := by
  classical
  simp only [tmplRoomVB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, hRN, hTN⟩ := h
  have hf := fz_facts ht
  have hD := floorTmpl_D ht
  have hH : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := by exact_mod_cast paramH_ge_q n Φ
  have hφ := tz_monoX hf hD (ox : ℝ)
  have hψ := tz_monoY hf hD hH
  set Z := fzone t (paramH n Φ) ox with hZdef
  set φ := tzX t (fz t) (ox : ℝ)
  set ψ := tzY t (fz t) ((paramH n Φ : ℚ) : ℝ)
  have hwf : (RR ++ NR).all (GRect.wf (fz t).zone.NX (fz t).zone.NY) = true := by
    simp only [gridRoomVB, Bool.and_eq_true] at h1; exact h1.1.1
  have hT : ψ (fz t).zone.T = -1 / 4 := by
    have := tz_T hf hD ((paramH n Φ : ℚ) : ℝ)
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    exact this
  have hZrs : Z.rs = (fz t).zone.rects.map (realR φ ψ) := rfl
  have hZL : Z.L = φ (fz t).zone.L := rfl
  have hZR : Z.R = φ (fz t).zone.R := rfl
  let rest : List (Set Point) :=
    ((regionRectsO n Φ).filter fun r => decide (r ∉ Z.rs)).map Rect.set
  refine gridRoomV hφ hψ h1 (rest := rest)
    (U := {z | φ (fz t).zone.L < z.1 ∧ z.1 < φ (fz t).zone.R ∧ z.2 < ψ (fz t).zone.T}) ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hA
    exact isClosed_rect_set r
  · intro z hz
    rw [filledO] at hz
    obtain ⟨r, hr, hzr⟩ := hz
    by_cases hrZ : r ∈ Z.rs
    · left
      rw [hZrs] at hrZ
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hrZ
      exact split_cover h3 hs hzr
    · right
      exact ⟨r.set, List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by simpa using hrZ⟩, rfl⟩, hzr⟩
  · intro r hr z hz
    exact inFloorBox hφ hψ hRN hTN (List.all_eq_true.2 fun s hs =>
      List.all_eq_true.1 hwf s (List.mem_append_left _ hs)) h2 r hr z hz
  · intro A hA z hzA hzU
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hA
    obtain ⟨hr, hrZ⟩ := List.mem_filter.1 hr
    simp only [decide_eq_true_eq] at hrZ
    rcases region_rect_floor hZ r hr with h' | h'
    · exact hrZ h'
    · obtain ⟨u1, u2, u3⟩ := hzU
      rw [hT] at u3
      exact h' z hzA ⟨by rw [hZL]; exact u1, by rw [hZR]; exact u2, u3⟩

/-- An open grid box (columns `i₀ < i₁`, rows `j₀ < j₁`) inside the floor box that meets no
rectangle of the zone. -/
def zoneBoxEmptyB (z : Zone) (i0 i1 j0 j1 : ℕ) : Bool :=
  decide (z.L ≤ i0 ∧ i0 < i1 ∧ i1 ≤ z.R ∧ j0 < j1 ∧ j1 ≤ z.T ∧ z.R < z.NX ∧ z.T < z.NY) &&
  z.rects.all fun r => GRect.wf z.NX z.NY r &&
    decide (r.2.1 ≤ i0 ∨ i1 ≤ r.1 ∨ r.2.2.2 ≤ j0 ∨ j1 ≤ r.2.2.1)

/-- **Empty boxes of a floor zone**: no point of the region lies in the open box. -/
theorem zone_box_empty {t : ITmpl} (ht : t ∈ allFloorTmpls) {ox : ℚ}
    (hZ : fzone t (paramH n Φ) ox ∈ zfO n Φ) {i0 i1 j0 j1 : ℕ}
    (h : zoneBoxEmptyB (fz t).zone i0 i1 j0 j1 = true) {z : Point}
    (h1 : tzX t (fz t) (ox : ℝ) i0 < z.1) (h2 : z.1 < tzX t (fz t) (ox : ℝ) i1)
    (h3 : tzY t (fz t) ((paramH n Φ : ℚ) : ℝ) j0 < z.2)
    (h4 : z.2 < tzY t (fz t) ((paramH n Φ : ℚ) : ℝ) j1) :
    z ∉ (Polygon.mk ((polyO n Φ).map ratPoint)).filled := by
  simp only [zoneBoxEmptyB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hL, hi, hR, hj, hT, hRN, hTN⟩, hr⟩ := h
  have hf := fz_facts ht
  have hD := floorTmpl_D ht
  have hH : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := by exact_mod_cast paramH_ge_q n Φ
  have hφ := tz_monoX hf hD (ox : ℝ)
  have hψ := tz_monoY hf hD hH
  set φ := tzX t (fz t) (ox : ℝ)
  set ψ := tzY t (fz t) ((paramH n Φ : ℚ) : ℝ)
  have hT' : ψ (fz t).zone.T = -1 / 4 := by
    have := tz_T hf hD ((paramH n Φ : ℚ) : ℝ)
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    exact this
  intro hz
  rw [filledO] at hz
  obtain ⟨r, hrm, hzr⟩ := hz
  rcases region_rect_floor hZ r hrm with h' | h'
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h'
    obtain ⟨hw, hsep⟩ := hr s hs
    simp only [GRect.wf, decide_eq_true_eq] at hw
    obtain ⟨y1, y2, y3, y4⟩ := hzr
    simp only [realR] at y1 y2 y3 y4
    rcases hsep with c | c | c | c
    · have := hφ.monotoneOn (by simp; omega) (by simp; omega) c; linarith
    · have := hφ.monotoneOn (by simp; omega) (by simp; omega) c; linarith
    · have := hψ.monotoneOn (by simp; omega) (by simp; omega) c; linarith
    · have := hψ.monotoneOn (by simp; omega) (by simp; omega) c; linarith
  · refine h' z hzr ⟨?_, ?_, ?_⟩
    · show φ (fz t).zone.L < z.1
      exact lt_of_le_of_lt (hφ.monotoneOn (by simp; omega) (by simp; omega) hL) h1
    · show z.1 < φ (fz t).zone.R
      exact lt_of_lt_of_le h2 (hφ.monotoneOn (by simp; omega) (by simp; omega) hR)
    · rw [← hT']
      exact lt_of_lt_of_le h4 (hψ.monotoneOn (by simp; omega) (by simp; omega) hT)

end

end ArtGallery.Orthogonal.Hard
