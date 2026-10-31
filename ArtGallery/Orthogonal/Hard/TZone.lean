module

public import ArtGallery.Orthogonal.Hard.GZone
public import ArtGallery.Orthogonal.Hard.Orth

/-!
# Zones of templates

The zone of a template `t` (`TZone`) is a grid zone whose abscissae `xs` and ordinates `ys`
(pairs `(y₀, d)` standing for `y₀ − d·H`) are numerators over the template's denominator `t.D`.
Ceiling templates are **mirrored** through the origin (`p ↦ −p`) into floor zones.
`tzoneOK t mirror zt` checks:

* the zone check `zoneOK`;
* the grid lists are strictly increasing (robustly for `H ≥ 1000`);
* the template vertices are grid points (`idx`);
* the feature check `featOK` (every boundary segment of the zone is a template edge or a floor
  piece joining a box corner to an end of the template, and every template edge is one);
* the box: floor `y = −1` (mirrored: `−2H`), top `−1/4` (mirrored: `−2H + 1/4`), sides at
  `x_min − 1/8` and `x_max + 1/8` (mirrored: `−x_max − 1/8` and `−x_min + 1/8`).

`tzone_real` relates the realised grid points to the instantiated template.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade ArtGallery.Stade.Chain Set

/-- The zone of a template. -/
structure TZone where
  /-- Abscissa numerators, increasing. -/
  xs : List ℤ
  /-- Ordinate numerators `(y₀, d)`, increasing for `H ≥ 1000`. -/
  ys : List (ℤ × ℤ)
  /-- Grid indices of the template vertices. -/
  idx : List (ℕ × ℕ)
  /-- Source of each boundary segment (see `srcOK`). -/
  src : List (ℕ × ℕ)
  /-- The zone. -/
  zone : Zone

/-- **The template zone check.** -/
def tzoneOK (t : ITmpl) (mirror : Bool) (zt : TZone) : Bool :=
  let z := zt.zone
  let sg : ℤ := if mirror then -1 else 1
  zoneOK z && z.NX == zt.xs.length && z.NY == zt.ys.length &&
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

/-! ### Realisation -/

/-- The realised abscissa of a grid index. -/
noncomputable def tzX (t : ITmpl) (zt : TZone) (ox : ℝ) (i : ℕ) : ℝ :=
  ox + (zt.xs.getD i 0 : ℝ) / t.D

/-- The realised ordinate of a grid index (in the mirrored plane for mirrored zones). -/
noncomputable def tzY (t : ITmpl) (zt : TZone) (H : ℝ) (j : ℕ) : ℝ :=
  ((zt.ys.getD j (0, 0)).1 - (zt.ys.getD j (0, 0)).2 * H) / t.D

theorem chainB_lt_strictMonoOn {xs : List ℤ} (h : chainB (fun a b => decide (a < b)) xs = true)
    {D : ℕ} (hD : 0 < D) (ox : ℝ) :
    StrictMonoOn (fun i => ox + (xs.getD i 0 : ℝ) / D) (Iio xs.length) := by
  have hc := chainB_sound (R := fun a b : ℤ => a < b) (fun a b h => of_decide_eq_true h) h
  have hp := List.isChain_iff_pairwise.1 hc
  intro i hi j hj hij
  simp only [mem_Iio] at hi hj
  simp only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  have := hp.rel_get_of_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij
  have h' : ((xs[i] : ℤ) : ℝ) < ((xs[j] : ℤ) : ℝ) := by exact_mod_cast this
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have := div_lt_div_of_pos_right h' hD'
  linarith

theorem chainB_robust_strictMonoOn {ys : List (ℤ × ℤ)}
    (h : chainB (fun p q => decide (q.2 ≤ p.2 ∧ 0 < (q.1 - p.1) + (p.2 - q.2) * 1000)) ys = true)
    {D : ℕ} (hD : 0 < D) {H : ℝ} (hH : 1000 ≤ H) :
    StrictMonoOn (fun j => ((ys.getD j (0, 0)).1 - (ys.getD j (0, 0)).2 * H) / D)
      (Iio ys.length) := by
  have hc := chainB_sound (R := fun p q : ℤ × ℤ => q.2 ≤ p.2 ∧ 0 < (q.1 - p.1) + (p.2 - q.2) * 1000)
    (fun a b h => of_decide_eq_true h) h
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  set g : ℤ × ℤ → ℝ := fun p => ((p.1 : ℝ) - p.2 * H) / D with hg
  have hc' : (ys.map g).IsChain (· < ·) := by
    rw [List.isChain_map]
    refine hc.imp (fun p q hpq => ?_)
    obtain ⟨h1, h2⟩ := hpq
    have h1' : ((q.2 : ℤ) : ℝ) ≤ ((p.2 : ℤ) : ℝ) := by exact_mod_cast h1
    have h2' : (0 : ℝ) < ((q.1 : ℤ) : ℝ) - p.1 + ((p.2 : ℝ) - q.2) * 1000 := by exact_mod_cast h2
    simp only [hg]
    apply div_lt_div_of_pos_right _ hD'
    nlinarith [mul_le_mul_of_nonneg_left hH (sub_nonneg.2 h1')]
  have hp := List.isChain_iff_pairwise.1 hc'
  intro i hi j hj hij
  simp only [mem_Iio] at hi hj
  have hi' : i < (ys.map g).length := by simpa using hi
  have hj' : j < (ys.map g).length := by simpa using hj
  have := hp.rel_get_of_lt (a := ⟨i, hi'⟩) (b := ⟨j, hj'⟩) hij
  simp only [List.get_eq_getElem, List.getElem_map] at this
  simp only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact this

end

end ArtGallery.Orthogonal.Hard
