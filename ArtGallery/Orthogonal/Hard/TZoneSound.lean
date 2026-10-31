module

public import ArtGallery.Orthogonal.Hard.TZone

/-!
# Template zones are good

From `tzoneOK t mirror zt` (evaluated by `decide`), for every `H ≥ 1000` and every translation:
the realised zone of the template (`tzFZone`) is a good zone (`FZone.Good`) for the floor line
`y = −1` and the strip top `−1/4` (mirrored: `y = −2H`, `−2H + 1/4`), its feature is the
instantiated template (mirrored through the origin), and its box is
`[ox + x_min − 1/8, ox + x_max + 1/8]` (mirrored: `[−b − x_max − 1/8, −b − x_min + 1/8]`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational Set

/-- The facts of `tzoneOK`. -/
structure TZoneFacts (t : ITmpl) (mirror : Bool) (zt : TZone) : Prop where
  zone : zoneOK zt.zone = true
  nx : zt.zone.NX = zt.xs.length
  ny : zt.zone.NY = zt.ys.length
  xs : chainB (fun a b => decide (a < b)) zt.xs = true
  ys : chainB (fun p q => decide (q.2 ≤ p.2 ∧ 0 < (q.1 - p.1) + (p.2 - q.2) * 1000)) zt.ys = true
  len : zt.idx.length = t.pts.length
  pts : ∀ pi ∈ t.pts.zip zt.idx, pi.2.1 < zt.zone.NX ∧ pi.2.2 < zt.zone.NY ∧
    zt.xs.getD pi.2.1 0 = (if mirror then -1 else 1) * pi.1.1 ∧
    zt.ys.getD pi.2.2 (0, 0) =
      ((if mirror then -1 else 1) * pi.1.2.1, (if mirror then -1 else 1) * pi.1.2.2)
  feat : featOK zt.zone zt.idx zt.src = true
  F : zt.ys.getD zt.zone.F (0, 0) = (if mirror then (0, 2 * (t.D : ℤ)) else (-(t.D : ℤ), 0))
  T : zt.ys.getD zt.zone.T (0, 0) =
    (if mirror then ((t.D : ℤ) / 4, 2 * (t.D : ℤ)) else (-(t.D : ℤ) / 4, 0))
  D8 : (t.D : ℤ) % 8 = 0
  L : (zt.xs.getD zt.zone.L 0 : ℚ) / t.D = (if mirror then -t.xmax else t.xmin) - 1 / 8
  R : (zt.xs.getD zt.zone.R 0 : ℚ) / t.D = (if mirror then -t.xmin else t.xmax) + 1 / 8

theorem tzoneFacts {t : ITmpl} {mirror : Bool} {zt : TZone} (h : tzoneOK t mirror zt = true) :
    TZoneFacts t mirror zt := by
  simp only [tzoneOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  refine ⟨h1, beq_iff_eq.1 h2, beq_iff_eq.1 h3, h4, h5, beq_iff_eq.1 h6, fun pi hpi => ?_, h8,
    beq_iff_eq.1 h9, beq_iff_eq.1 h10, of_decide_eq_true h11, of_decide_eq_true h12,
    of_decide_eq_true h13⟩
  have := List.all_eq_true.1 h7 pi hpi
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-- The realised zone of a template (`ox`: the translation in the realised plane). -/
noncomputable def tzFZone (t : ITmpl) (zt : TZone) (H ox : ℝ) : FZone :=
  gFZone (tzX t zt ox) (tzY t zt H) zt.zone zt.idx

section Sound

variable {t : ITmpl} {mirror : Bool} {zt : TZone} (h : TZoneFacts t mirror zt) (hD : 0 < t.D)
include h hD

theorem tz_monoX (ox : ℝ) : StrictMonoOn (tzX t zt ox) (Iio zt.zone.NX) := by
  rw [h.nx]; exact chainB_lt_strictMonoOn h.xs hD ox

theorem tz_monoY {H : ℝ} (hH : 1000 ≤ H) : StrictMonoOn (tzY t zt H) (Iio zt.zone.NY) := by
  rw [h.ny]; exact chainB_robust_strictMonoOn h.ys hD hH

/-- **Template zones are good.** -/
theorem tz_good {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ) :
    (tzFZone t zt H ox).Good (tzY t zt H zt.zone.F) (tzY t zt H zt.zone.T) :=
  gfzone_good (zoneFacts h.zone) (tz_monoX h hD ox) (tz_monoY h hD hH) (featFacts h.feat)

theorem tz_F (H : ℝ) : tzY t zt H zt.zone.F = if mirror then -2 * H else -1 := by
  have hD' : (t.D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  unfold tzY
  rw [h.F]
  cases mirror <;> simp <;> field_simp <;> ring

theorem tz_T (H : ℝ) : tzY t zt H zt.zone.T = if mirror then -2 * H + 1 / 4 else -1 / 4 := by
  have hD' : (t.D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have h4 : (((t.D : ℤ) / 4 : ℤ) : ℝ) = (t.D : ℝ) / 4 := by
    have := h.D8
    have e : (t.D : ℤ) = (t.D : ℤ) / 4 * 4 := by omega
    have : ((t.D : ℤ) : ℝ) = (((t.D : ℤ) / 4 : ℤ) : ℝ) * 4 := by exact_mod_cast e
    push_cast at this
    linarith
  have h4' : ((-(t.D : ℤ) / 4 : ℤ) : ℝ) = -(t.D : ℝ) / 4 := by
    have := h.D8
    have e : -(t.D : ℤ) / 4 = -((t.D : ℤ) / 4) := by omega
    rw [e]; push_cast; rw [h4]; ring
  unfold tzY
  rw [h.T]
  cases mirror
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [h4']; simp; field_simp
  · simp only [↓reduceIte]
    rw [h4]; push_cast; field_simp; ring

theorem tz_L (H ox : ℝ) :
    (tzFZone t zt H ox).L = ox + (((if mirror then -t.xmax else t.xmin) - 1 / 8 : ℚ) : ℝ) := by
  simp only [tzFZone, gFZone, tzX]
  rw [← h.L]; push_cast; ring

theorem tz_R (H ox : ℝ) :
    (tzFZone t zt H ox).R = ox + (((if mirror then -t.xmin else t.xmax) + 1 / 8 : ℚ) : ℝ) := by
  simp only [tzFZone, gFZone, tzX]
  rw [← h.R]; push_cast; ring

/-- The realised feature of a template zone. -/
theorem tz_f (H ox : ℝ) :
    (tzFZone t zt H ox).f = t.pts.map (fun p : ℤ × ℤ × ℤ =>
      ((ox + (if mirror then -1 else 1) * (p.1 : ℝ) / t.D,
        (if mirror then -1 else 1) * ((p.2.1 : ℝ) - p.2.2 * H) / t.D) : Point)) := by
  simp only [tzFZone, gFZone]
  apply List.ext_getElem (by simp [h.len])
  intro k h1 h2
  simp only [List.length_map] at h1 h2
  simp only [List.getElem_map]
  have hpi : (t.pts[k], zt.idx[k]) ∈ t.pts.zip zt.idx := by
    have := List.getElem_mem (l := t.pts.zip zt.idx) (n := k) (by simp; omega)
    simpa using this
  obtain ⟨-, -, hx, hy⟩ := h.pts _ hpi
  simp only [gpt, tzX, tzY] at hx hy ⊢
  rw [hx, hy]
  cases mirror <;> simp <;> ring

end Sound

/-! ### Instantiated templates -/

theorem tz_f_floor {t : ITmpl} {zt : TZone} (h : TZoneFacts t false zt) (hD : 0 < t.D)
    (H ox : ℚ) : (tzFZone t zt H ox).f = (t.inst H ox).map ratPoint := by
  rw [tz_f h hD, ITmpl.inst, List.map_map]
  refine List.map_congr_left (fun p _ => ?_)
  simp only [Function.comp, ratPoint, Bool.false_eq_true, ↓reduceIte]
  ext <;> push_cast <;> ring

theorem tz_f_ceil {t : ITmpl} {zt : TZone} (h : TZoneFacts t true zt) (hD : 0 < t.D)
    (H b : ℚ) : (tzFZone t zt H (-b)).f = ((t.inst H b).map ratPoint).map (fun q => -q) := by
  rw [tz_f h hD, ITmpl.inst, List.map_map, List.map_map]
  refine List.map_congr_left (fun p _ => ?_)
  simp only [Function.comp, ratPoint, ↓reduceIte]
  ext <;> push_cast <;> simp <;> ring

end

end ArtGallery.Orthogonal.Hard
