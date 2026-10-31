module

public import ArtGallery.Orthogonal.Hard.ZonesData

/-!
# Orthogonal construction: the template zones pass their checks

`floorZones_ok`, `ceilZones_ok`: every template zone passes `tzoneOK` (by `decide +kernel`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade

theorem floorZones_len : floorZones.length = allFloorTmpls.length := by decide

theorem ceilZones_len : ceilZones.length = allCeilTmpls.length := by decide

/-! ### The checks in parts

The zone checks of the two large templates are split into ranges of rectangles and of boundary
segments, proved as separate declarations (a kernel evaluation keeps its intermediate results for
the whole declaration). -/

/-- The conditions of `zoneOK` other than the rectangles, the tiles and the cover. -/
def zoneHead (z : Zone) : Bool :=
  z.bot.length == z.rects.length && z.top.length == z.rects.length &&
  z.left.length == z.rects.length && z.right.length == z.rects.length &&
  z.cover.length == z.pedges.length &&
  z.pedges.all (fun e => decide (e.1.1 < z.NX ∧ e.2.1 < z.NX ∧ e.1.2 < z.NY ∧ e.2.2 < z.NY)) &&
  decide (z.L < z.NX ∧ z.R < z.NX ∧ z.F < z.NY ∧ z.T < z.NY) &&
  decide (0 < z.rects.length) && z.left.getD 0 (some ([], [])) == none &&
  z.right.getD (z.rects.length - 1) (some ([], [])) == none

/-- The cover condition of the boundary segment `e`. -/
def coverAt (z : Zone) (e : ℕ) : Bool :=
  coverOK z (z.pedges.getD e ((0, 0), (0, 0))) (z.cover.getD e [])

theorem zoneOK_of_parts {z : Zone} (h0 : zoneHead z = true)
    (h1 : rangeAll (rectOK z) 0 z.rects.length = true) (h2 : tilesOK z z.L z.topTiles z.R = true)
    (h3 : rangeAll (coverAt z) 0 z.pedges.length = true) : zoneOK z = true := by
  have e : ∀ (p : ℕ → Bool) n, (List.range n).all p = rangeAll p 0 n := fun p n => by
    simp [rangeAll, List.range_eq_range']
  show (((zoneHead z && (List.range z.rects.length).all (rectOK z)) && tilesOK z z.L z.topTiles z.R) &&
    (List.range z.pedges.length).all (coverAt z)) = true
  rw [e, e, h0, h1, h2, h3]; rfl

/-- The conditions of `tzoneOK` other than `zoneOK`. -/
def tzoneRest (t : ITmpl) (mirror : Bool) (zt : TZone) : Bool :=
  let z := zt.zone
  let sg : ℤ := if mirror then -1 else 1
  z.NX == zt.xs.length && z.NY == zt.ys.length &&
  chainB (fun a b => decide (a < b)) zt.xs &&
  chainB (fun p q => decide (q.2 ≤ p.2 ∧ 0 < (q.1 - p.1) + (p.2 - q.2) * 1000)) zt.ys &&
  zt.idx.length == t.pts.length &&
  (t.pts.zip zt.idx).all (fun pi =>
    decide (pi.2.1 < z.NX ∧ pi.2.2 < z.NY) && zt.xs.getD pi.2.1 0 == sg * pi.1.1 &&
    zt.ys.getD pi.2.2 (0, 0) == (sg * pi.1.2.1, sg * pi.1.2.2)) &&
  featOK z zt.idx zt.src &&
  zt.ys.getD z.F (0, 0) == (if mirror then (0, 2 * (t.D : ℤ)) else (-(t.D : ℤ), 0)) &&
  zt.ys.getD z.T (0, 0) ==
    (if mirror then ((t.D : ℤ) / 4, 2 * (t.D : ℤ)) else (-(t.D : ℤ) / 4, 0)) &&
  decide ((t.D : ℤ) % 8 = 0) &&
  decide ((zt.xs.getD z.L 0 : ℚ) / t.D = (if mirror then -t.xmax else t.xmin) - 1 / 8) &&
  decide ((zt.xs.getD z.R 0 : ℚ) / t.D = (if mirror then -t.xmin else t.xmax) + 1 / 8)

theorem tzoneOK_of_parts {t : ITmpl} {mirror : Bool} {zt : TZone} (hz : zoneOK zt.zone = true)
    (hr : tzoneRest t mirror zt = true) : tzoneOK t mirror zt = true := by
  simp only [tzoneRest, Bool.and_eq_true] at hr
  simp only [tzoneOK, Bool.and_eq_true, hz, true_and]
  exact hr

/-- The default template zone. -/
def TZone.dflt : TZone := ⟨[], [], [], [], ⟨0, 0, 0, 0, 0, 0, [], [], [], [], [], [], [], []⟩⟩

set_option maxRecDepth 100000 in
theorem floorZones_ok0 : (List.range 8).all (fun i =>
    tzoneOK (allFloorTmpls.getD i ITmpl.dflt) false (floorZones.getD i TZone.dflt)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem floorZone_head8 : zoneHead (floorZones.getD 8 TZone.dflt).zone = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_tiles8 : tilesOK (floorZones.getD 8 TZone.dflt).zone (floorZones.getD 8 TZone.dflt).zone.L (floorZones.getD 8 TZone.dflt).zone.topTiles (floorZones.getD 8 TZone.dflt).zone.R = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rest8 :
    tzoneRest (allFloorTmpls.getD 8 ITmpl.dflt) false (floorZones.getD 8 TZone.dflt) = true := by
  decide +kernel
theorem floorZone_nr8 : (floorZones.getD 8 TZone.dflt).zone.rects.length = 337 := by decide +kernel
theorem floorZone_ne8 : (floorZones.getD 8 TZone.dflt).zone.pedges.length = 233 := by decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects8_0 : rangeAll (rectOK (floorZones.getD 8 TZone.dflt).zone) 0 45 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects8_45 : rangeAll (rectOK (floorZones.getD 8 TZone.dflt).zone) 45 90 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects8_90 : rangeAll (rectOK (floorZones.getD 8 TZone.dflt).zone) 90 135 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects8_135 : rangeAll (rectOK (floorZones.getD 8 TZone.dflt).zone) 135 180 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects8_180 : rangeAll (rectOK (floorZones.getD 8 TZone.dflt).zone) 180 225 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects8_225 : rangeAll (rectOK (floorZones.getD 8 TZone.dflt).zone) 225 270 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects8_270 : rangeAll (rectOK (floorZones.getD 8 TZone.dflt).zone) 270 315 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects8_315 : rangeAll (rectOK (floorZones.getD 8 TZone.dflt).zone) 315 337 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_cover8_0 : rangeAll (coverAt (floorZones.getD 8 TZone.dflt).zone) 0 60 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_cover8_60 : rangeAll (coverAt (floorZones.getD 8 TZone.dflt).zone) 60 120 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_cover8_120 : rangeAll (coverAt (floorZones.getD 8 TZone.dflt).zone) 120 180 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_cover8_180 : rangeAll (coverAt (floorZones.getD 8 TZone.dflt).zone) 180 233 = true := by
  decide +kernel

theorem floorZone_ok8 :
    tzoneOK (allFloorTmpls.getD 8 ITmpl.dflt) false (floorZones.getD 8 TZone.dflt) = true :=
  tzoneOK_of_parts (zoneOK_of_parts floorZone_head8
    (floorZone_nr8 ▸ (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) floorZone_rects8_0 floorZone_rects8_45) floorZone_rects8_90) floorZone_rects8_135) floorZone_rects8_180) floorZone_rects8_225) floorZone_rects8_270) floorZone_rects8_315)) floorZone_tiles8
    (floorZone_ne8 ▸ (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) floorZone_cover8_0 floorZone_cover8_60) floorZone_cover8_120) floorZone_cover8_180))) floorZone_rest8

set_option maxRecDepth 100000 in
theorem floorZone_head9 : zoneHead (floorZones.getD 9 TZone.dflt).zone = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_tiles9 : tilesOK (floorZones.getD 9 TZone.dflt).zone (floorZones.getD 9 TZone.dflt).zone.L (floorZones.getD 9 TZone.dflt).zone.topTiles (floorZones.getD 9 TZone.dflt).zone.R = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rest9 :
    tzoneRest (allFloorTmpls.getD 9 ITmpl.dflt) false (floorZones.getD 9 TZone.dflt) = true := by
  decide +kernel
theorem floorZone_nr9 : (floorZones.getD 9 TZone.dflt).zone.rects.length = 351 := by decide +kernel
theorem floorZone_ne9 : (floorZones.getD 9 TZone.dflt).zone.pedges.length = 233 := by decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects9_0 : rangeAll (rectOK (floorZones.getD 9 TZone.dflt).zone) 0 45 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects9_45 : rangeAll (rectOK (floorZones.getD 9 TZone.dflt).zone) 45 90 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects9_90 : rangeAll (rectOK (floorZones.getD 9 TZone.dflt).zone) 90 135 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects9_135 : rangeAll (rectOK (floorZones.getD 9 TZone.dflt).zone) 135 180 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects9_180 : rangeAll (rectOK (floorZones.getD 9 TZone.dflt).zone) 180 225 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects9_225 : rangeAll (rectOK (floorZones.getD 9 TZone.dflt).zone) 225 270 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects9_270 : rangeAll (rectOK (floorZones.getD 9 TZone.dflt).zone) 270 315 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_rects9_315 : rangeAll (rectOK (floorZones.getD 9 TZone.dflt).zone) 315 351 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_cover9_0 : rangeAll (coverAt (floorZones.getD 9 TZone.dflt).zone) 0 60 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_cover9_60 : rangeAll (coverAt (floorZones.getD 9 TZone.dflt).zone) 60 120 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_cover9_120 : rangeAll (coverAt (floorZones.getD 9 TZone.dflt).zone) 120 180 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem floorZone_cover9_180 : rangeAll (coverAt (floorZones.getD 9 TZone.dflt).zone) 180 233 = true := by
  decide +kernel

theorem floorZone_ok9 :
    tzoneOK (allFloorTmpls.getD 9 ITmpl.dflt) false (floorZones.getD 9 TZone.dflt) = true :=
  tzoneOK_of_parts (zoneOK_of_parts floorZone_head9
    (floorZone_nr9 ▸ (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) floorZone_rects9_0 floorZone_rects9_45) floorZone_rects9_90) floorZone_rects9_135) floorZone_rects9_180) floorZone_rects9_225) floorZone_rects9_270) floorZone_rects9_315)) floorZone_tiles9
    (floorZone_ne9 ▸ (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) floorZone_cover9_0 floorZone_cover9_60) floorZone_cover9_120) floorZone_cover9_180))) floorZone_rest9

theorem floorZones_ok : (allFloorTmpls.zip floorZones).all (fun p => tzoneOK p.1 false p.2) = true := by
  have hl : floorZones.length = 10 := by rw [floorZones_len, floorTmpls_len]
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hi' : i < 10 := by simp only [List.length_zip, floorTmpls_len, hl] at hi; omega
  rw [List.getElem_zip]
  rw [← List.getD_eq_getElem allFloorTmpls ITmpl.dflt, ← List.getD_eq_getElem floorZones TZone.dflt]
  rcases Nat.lt_or_ge i 8 with h | h
  · exact List.all_eq_true.1 floorZones_ok0 i (List.mem_range.2 h)
  · rcases (show i = 8 ∨ i = 9 by omega) with rfl | rfl
    · exact floorZone_ok8
    · exact floorZone_ok9

set_option maxRecDepth 100000 in
theorem ceilZones_ok : (allCeilTmpls.zip ceilZones).all (fun p => tzoneOK p.1 true p.2) = true := by
  decide +kernel

end

end ArtGallery.Orthogonal.Hard
