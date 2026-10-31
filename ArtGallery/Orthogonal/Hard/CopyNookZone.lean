module

public import ArtGallery.Orthogonal.Hard.CopyNookZoneData
public import ArtGallery.Orthogonal.Hard.CopyNookSimple

/-!
# The zone of the copy nook is good

The zone `cnZone` (generated) of the copy nook in
normal form, mirrored through the origin, passes `zoneOK` and `featOK`, and its feature grid
indices are those of `cnGrid` in mirrored order (`cnZone_ok`, by `decide`).  Realised on the
extended grids `cnXe`, `cnYe` (in mirrored order), it is a good zone for the line `y = −2H` and
the strip top `−2H + 1/4` whose feature is the mirrored copy nook (`cn_good`, `cn_f`), with box
`[−(x_N + 3u + 3/8), −(x_N − u − 7/8)]`.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade ArtGallery.Stade.Chain Set

theorem cnZone_ok : (zoneOK cnZone && featOK cnZone cnIdx cnSrc &&
    cnIdx == cnGrid.map (fun p => (18 - p.1, 17 - p.2))) = true := by
  decide +kernel

/-- The abscissae of the copy-nook zone: the box sides and `cnXs`. -/
def cnXe (xN u G e : ℚ) : List ℚ := (xN - u - 7 / 8) :: (cnXs xN u G e ++ [xN + 3 * u + 3 / 8])

/-- The ordinates of the copy-nook zone: the strip bottom and `cnYs`. -/
def cnYe (G e H : ℚ) : List ℚ := (2 * H - 1 / 4) :: cnYs G e H

/-- The realised abscissa of a grid index of the (mirrored) copy-nook zone. -/
noncomputable def cnφ (xN u G e : ℚ) (i : ℕ) : ℝ := -(((cnXe xN u G e).getD (19 - i) 0 : ℚ) : ℝ)

/-- The realised ordinate of a grid index of the (mirrored) copy-nook zone. -/
noncomputable def cnψ (G e H : ℚ) (j : ℕ) : ℝ := -(((cnYe G e H).getD (18 - j) 0 : ℚ) : ℝ)

/-- The realised zone of the copy nook. -/
noncomputable def cnFZone (xN u G e H : ℚ) : FZone :=
  gFZone (cnφ xN u G e) (cnψ G e H) cnZone cnIdx

section Order

variable {xN u G e H : ℚ}

theorem cnXe_chain (hG : 1 < G) (hGu : G < u) (hu : u < 2) (he : 0 < e) (he' : e < 1 / 100) :
    (cnXe xN u G e).IsChain (· < ·) := by
  have hGe : 0 < G * e := by positivity
  have hGe' : G * e < 2 * e := by nlinarith
  simp only [cnXe, cnXs, List.cons_append, List.nil_append, List.isChain_cons_cons,
    List.isChain_singleton, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem cnYe_chain (hG : 1 < G) (hu : G < 2) (he : 0 < e) (he' : e < 1 / 100) :
    (cnYe G e H).IsChain (· < ·) := by
  have hGe : 0 < G * e := by positivity
  have hGe' : G * e < 2 * e := by nlinarith
  have hGe'' : e < G * e := by nlinarith
  have hee : 0 < e * e := by positivity
  have hee' : e * e < e / 100 := by nlinarith
  simp only [cnYe, cnYs, List.isChain_cons_cons, List.isChain_singleton, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- A list increasing, read backwards and negated, is increasing. -/
theorem strictMonoOn_rev_neg {xs : List ℚ} {N : ℕ} (h : xs.IsChain (· < ·))
    (hN : xs.length = N + 1) :
    StrictMonoOn (fun i => -((xs.getD (N - i) 0 : ℚ) : ℝ)) (Iio (N + 1)) := by
  have hm := strictMonoOn_getD_rat h
  intro i hi j hj hij
  simp only [mem_Iio] at hi hj
  have := hm (a := N - j) (b := N - i) (by simp only [mem_Iio]; omega)
    (by simp only [mem_Iio]; omega) (by omega)
  simp only at this ⊢
  linarith

end Order

section Good

variable {xN u G e H : ℚ} (hG : 1 < G) (hGu : G < u) (hu : u < 2) (he : 0 < e) (he' : e < 1 / 100)
include hG hGu hu he he'

theorem cn_monoX : StrictMonoOn (cnφ xN u G e) (Iio cnZone.NX) :=
  strictMonoOn_rev_neg (N := 19) (cnXe_chain hG hGu hu he he') rfl

theorem cn_monoY : StrictMonoOn (cnψ G e H) (Iio cnZone.NY) :=
  strictMonoOn_rev_neg (N := 18) (cnYe_chain hG (hGu.trans hu) he he') rfl

/-- **The copy-nook zone is good.** -/
theorem cn_good : (cnFZone xN u G e H).Good (cnψ G e H cnZone.F) (cnψ G e H cnZone.T) := by
  have h := cnZone_ok
  simp only [Bool.and_eq_true] at h
  exact gfzone_good (zoneFacts h.1.1) (cn_monoX hG hGu hu he he') (cn_monoY hG hGu hu he he')
    (featFacts h.1.2)

end Good

theorem cn_F (G e H : ℚ) : cnψ G e H cnZone.F = -(2 * (H : ℝ)) := by
  simp [cnψ, cnZone, cnYe, cnYs]

theorem cn_T (G e H : ℚ) : cnψ G e H cnZone.T = -(2 * (H : ℝ)) + 1 / 4 := by
  simp [cnψ, cnZone, cnYe]; ring

theorem cn_L (xN u G e H : ℚ) : (cnFZone xN u G e H).L = -(((xN + 3 * u + 3 / 8 : ℚ)) : ℝ) := by
  simp [cnFZone, gFZone, cnφ, cnZone, cnXe, cnXs]

theorem cn_R (xN u G e H : ℚ) : (cnFZone xN u G e H).R = -(((xN - u - 7 / 8 : ℚ)) : ℝ) := by
  simp [cnFZone, gFZone, cnφ, cnZone, cnXe]

/-- The realised feature of the copy-nook zone is the mirrored copy nook. -/
theorem cn_f (xN u G e H : ℚ) :
    (cnFZone xN u G e H).f = ((cnPts xN u G e H).map ratPoint).map (fun q => -q) := by
  have h := cnZone_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp only [cnFZone, gFZone, h.2, cnPts, List.map_map]
  refine List.map_congr_left (fun p hp => ?_)
  have hb := cnGrid_bound p hp
  simp only [Function.comp, gpt, cnφ, cnψ, ratPoint, Prod.neg_mk]
  have e1 : 19 - (18 - p.1) = p.1 + 1 := by omega
  have e2 : 18 - (17 - p.2) = p.2 + 1 := by omega
  rw [e1, e2]
  have hx : (cnXe xN u G e).getD (p.1 + 1) 0 = (cnXs xN u G e).getD p.1 0 := by
    simp only [cnXe, List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simp [cnXs]; omega)]
  have hy : (cnYe G e H).getD (p.2 + 1) 0 = (cnYs G e H).getD p.2 0 := by
    simp only [cnYe, List.getD_cons_succ]
  rw [hx, hy]

end

end ArtGallery.Orthogonal.Hard
