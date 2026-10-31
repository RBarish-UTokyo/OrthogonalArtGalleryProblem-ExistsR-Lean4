module

public import ArtGallery.Orthogonal.Hard.NookCovQ
public import ArtGallery.Orthogonal.Hard.CovRegion
public import ArtGallery.Orthogonal.Hard.CopyPocketO
public import ArtGallery.Orthogonal.Hard.CopyO
public import ArtGallery.Stade.Guarding
public import ArtGallery.Orthogonal.Hard.CovCanonBase

/-!
# Completeness: the copy nooks

A point of a rectangle of the copy nook of an input is seen by one of the two helpers of the
nook, by the variable guard `σ(v)` or the input guard `τ(v)` of the copied value, or is a band
point.  The cut trees of the coverage certificate (`nookCells`) handle the certified cells; the
remaining cells are strip cells outside the notch.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Data checks -/

/-- Every cell of a grid rectangle lies in a region rectangle of the nook. -/
def nCellsInB (B : GRect) : Bool :=
  (List.range' B.1 (B.2.1 - B.1)).all fun p => (List.range' B.2.2.1 (B.2.2.2 - B.2.2.1)).all
    fun q => cnRR.any (nCellIn p q)

/-- Every cell of a region rectangle of the nook is certified or a strip cell outside the notch. -/
def nookTargetB : Bool :=
  cnRR.all fun r => (List.range' r.1 (r.2.1 - r.1)).all fun p =>
    (List.range' r.2.2.1 (r.2.2.2 - r.2.2.1)).all fun q =>
      (decide (q < 3) && !(decide (7 ≤ p) && decide (p < 16) && decide (1 ≤ q))) ||
        nookCells.any (fun ct => decide (ct.1 = (p, q)))

theorem nookTarget_ok : nookTargetB = true := by decide +kernel

theorem cnRR_pos : ∀ r ∈ cnRR, r.1 < r.2.1 ∧ r.2.2.1 < r.2.2.2 := by decide +kernel

theorem nCells_mouth : nCellsInB (16, 19, 0, 3) = true := by decide +kernel
theorem nCells_pocket : nCellsInB (15, 17, 3, 15) = true := by decide +kernel
theorem nCells_Q : nCellsInB (13, 17, 3, 6) = true := by decide +kernel

/-! ### Cells -/

section Grid

variable {φ ψ : ℕ → ℝ} (hφ : StrictMonoOn φ (Iio 20)) (hψ : StrictMonoOn ψ (Iio 19))
include hφ hψ

/-- A point of a grid rectangle lies in one of its cells. -/
theorem grid_cell {B : GRect} (hB1 : B.1 < B.2.1) (hB2 : B.2.2.1 < B.2.2.2) {z : Point}
    (hz : z ∈ (realR φ ψ B).set) :
    ∃ p q, B.1 ≤ p ∧ p < B.2.1 ∧ B.2.2.1 ≤ q ∧ q < B.2.2.2 ∧
      z ∈ (realR φ ψ (p, p + 1, q, q + 1)).set := by
  obtain ⟨z1, z2, z3, z4⟩ := hz
  simp only [realR] at z1 z2 z3 z4
  have ex : B.1 + (B.2.1 - B.1 - 1) + 1 = B.2.1 := by omega
  have ey : B.2.2.1 + (B.2.2.2 - B.2.2.1 - 1) + 1 = B.2.2.2 := by omega
  obtain ⟨p, hp1, hp2, hxp, hxp'⟩ := nexists_step (f := φ) (B.2.1 - B.1 - 1) B.1 z1
    (by rw [ex]; exact z2)
  obtain ⟨q, hq1, hq2, hyq, hyq'⟩ := nexists_step (f := ψ) (B.2.2.2 - B.2.2.1 - 1) B.2.2.1 z3
    (by rw [ey]; exact z4)
  exact ⟨p, q, hp1, by omega, hq1, by omega, hxp, hxp', hyq, hyq'⟩

end Grid

theorem Rect.set_convex (r : Rect) : Convex ℝ r.set := by
  intro a ha b hb s t hs ht hst
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  obtain rfl : t = 1 - s := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] <;>
    nlinarith [mul_le_mul_of_nonneg_left a1 hs, mul_le_mul_of_nonneg_left b1 ht,
      mul_le_mul_of_nonneg_left a2 hs, mul_le_mul_of_nonneg_left b2 ht,
      mul_le_mul_of_nonneg_left a3 hs, mul_le_mul_of_nonneg_left b3 ht,
      mul_le_mul_of_nonneg_left a4 hs, mul_le_mul_of_nonneg_left b4 ht]

/-! ### The nook of an input -/

section Nook

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n) {i : InputSeg} (hi : i ∈ inputsO n Φ)
include hΦ hi

theorem nookI_params : CopyParams (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ) := by
  obtain ⟨d1, d2⟩ := inputO_delta hi (inputsO_var hΦ hi)
  have hH := Hr_ge' (n := n) (Φ := Φ)
  have e1 : ((paramH n Φ : ℚ) : ℝ) + 30 ≤ (i.b : ℝ) - (varA Φ i.var : ℝ) := by
    have := d1; exact_mod_cast this
  have e2 : (i.b : ℝ) - (varA Φ i.var : ℝ) ≤ 2 * ((paramH n Φ : ℚ) : ℝ) - 600 := by
    have := d2; exact_mod_cast this
  exact ⟨hH, by simp only [Hr] at *; linarith, by simp only [Hr] at *; linarith⟩

theorem nookI_mono : StrictMonoOn (iφ Φ (paramH n Φ) i.var i) (Iio 20) ∧
    StrictMonoOn (iψ Φ (paramH n Φ) i.var i) (Iio 19) := by
  obtain ⟨d1, d2⟩ := inputO_delta hi (inputsO_var hΦ hi)
  exact ⟨nookφ_mono (paramH_ge_q n Φ) d1 d2 i.ge, nookψ_mono (paramH_ge_q n Φ) d1 d2 i.ge⟩

/-- The region rectangles of the nook are in the region. -/
theorem nookI_reg : ∀ r ∈ cnRR,
    (realR (iφ Φ (paramH n Φ) i.var i) (iψ Φ (paramH n Φ) i.var i) r).set ⊆ PO n Φ := by
  have hk := inputsO_var hΦ hi
  have hZ := nzone_mem hk hi rfl
  intro r hr p hp
  have hm : realR (iφ Φ (paramH n Φ) i.var i) (iψ Φ (paramH n Φ) i.var i) r ∈
      (nzone (varA Φ i.var) i.b i.ge (paramH n Φ)).rs.map Rect.neg := by
    rw [nzone_rs]; exact List.mem_map.2 ⟨r, hr, rfl⟩
  obtain ⟨r', hr', he⟩ := List.mem_map.1 hm
  rw [← he] at hp
  exact mem_filled_of_region (zone_rect_ceil hZ hr') hp

/-- A grid rectangle all of whose cells are region cells is in the region. -/
theorem nookI_rect {B : GRect} (hB : nCellsInB B = true) (hB1 : B.1 < B.2.1)
    (hB2 : B.2.2.1 < B.2.2.2) (hB3 : B.2.1 < 20) (hB4 : B.2.2.2 < 19) :
    (realR (iφ Φ (paramH n Φ) i.var i) (iψ Φ (paramH n Φ) i.var i) B).set ⊆ PO n Φ := by
  obtain ⟨hφ, hψ⟩ := nookI_mono hΦ hi
  intro z hz
  obtain ⟨p, q, hp1, hp2, hq1, hq2, hzc⟩ := grid_cell hφ hψ hB1 hB2 hz
  have hc := List.all_eq_true.1 (List.all_eq_true.1 hB p (List.mem_range'_1.2 ⟨hp1, by omega⟩)) q
    (List.mem_range'_1.2 ⟨hq1, by omega⟩)
  obtain ⟨r, hr, hrc⟩ := List.any_eq_true.1 hc
  simp only [nCellIn, decide_eq_true_eq] at hrc
  obtain ⟨r1, r2, r3, r4⟩ := hrc
  obtain ⟨w1, w2⟩ := cnRR_bnd r hr
  apply nookI_reg hΦ hi r hr
  obtain ⟨z1, z2, z3, z4⟩ := hzc
  simp only [realR] at z1 z2 z3 z4 ⊢
  have mφ : ∀ a c, a ≤ c → c < 20 → iφ Φ (paramH n Φ) i.var i a ≤ iφ Φ (paramH n Φ) i.var i c :=
    fun a c hac hc => (hφ.le_iff_le (show a ∈ Iio 20 from lt_of_le_of_lt hac hc) hc).2 hac
  have mψ : ∀ a c, a ≤ c → c < 19 → iψ Φ (paramH n Φ) i.var i a ≤ iψ Φ (paramH n Φ) i.var i c :=
    fun a c hac hc => (hψ.le_iff_le (show a ∈ Iio 19 from lt_of_le_of_lt hac hc) hc).2 hac
  exact ⟨(mφ _ _ r1 (by omega)).trans z1, z2.trans (mφ _ _ r2 w1), (mψ _ _ r3 (by omega)).trans z3,
    z4.trans (mψ _ _ r4 w2)⟩

/-- The grid columns of the mouth: `φ₁₆ = x_N + G`, `φ₁₇ = x_N + u`, `φ₁₉ = x_N + 3u + 3/8`. -/
theorem nookI_cols : iφ Φ (paramH n Φ) i.var i 16 = ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ) +
      ((nookG (varA Φ i.var) i.b i.ge (paramH n Φ) : ℚ) : ℝ) ∧
    iφ Φ (paramH n Φ) i.var i 17 = ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ) +
      ((nookU (varA Φ i.var) i.b i.ge (paramH n Φ) : ℚ) : ℝ) ∧
    iφ Φ (paramH n Φ) i.var i 19 = ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ) +
      3 * ((nookU (varA Φ i.var) i.b i.ge (paramH n Φ) : ℚ) : ℝ) + 3 / 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp only [iφ]; rw [nookφ_eq i.ge (by norm_num)]; simp [cnXe, cnXs]) <;> ring

/-- **The guards below a copy nook see its mouth**: through the hall, and through the strip
cells below the mouth. -/
theorem nookI_mouth_sees {g : Point}
    (hg1 : (copyRm i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ)).1 ≤ g.1) (hg2 : g.1 ≤ xR n Φ)
    (hg3 : -1 / 4 ≤ g.2) (hg4 : g.2 ≤ 2 * Hr n Φ - 1 / 4)
    (hg5 : g.1 - (copyLm i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ)).1 ≤ 8 * (2 * Hr n Φ - g.2)) :
    ∀ m ∈ ArtGallery.segment (copyLm i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ))
      (copyRm i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ)),
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees g m := by
  have hk := inputsO_var hΦ hi
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  obtain ⟨hG1, hGu, hu2⟩ := nook_offsets (paramH_ge_q n Φ) d1 d2 i.ge
  obtain ⟨b1, -⟩ := nookX_bounds hΦ hi
  obtain ⟨e16, e17, e19⟩ := nookI_cols hΦ hi
  have hLm := nook_gpt_Lm (varA Φ i.var) i.b i.ge (paramH n Φ)
  have hRm := nook_gpt_Rm (varA Φ i.var) i.b i.ge (paramH n Φ)
  simp only [gpt] at hLm hRm
  push_cast at hLm hRm
  have eH : ((paramH n Φ : ℚ) : ℝ) = Hr n Φ := rfl
  have eH' : ((paramH n Φ : ℕ) : ℝ) = Hr n Φ := by simp [Hr]
  rw [eH'] at hLm hRm
  have hψ3 := nook_psi3 (a := (varA Φ i.var : ℚ)) (b := i.b) (H := paramH n Φ) i.ge
  have hψ0 := nook_psi0 (a := (varA Φ i.var : ℚ)) (b := i.b) (H := paramH n Φ) i.ge
  rw [eH] at hψ3 hψ0
  have hG1' : (1 : ℝ) < ((nookG (varA Φ i.var) i.b i.ge (paramH n Φ) : ℚ) : ℝ) := by exact_mod_cast hG1
  have hGu' : ((nookG (varA Φ i.var) i.b i.ge (paramH n Φ) : ℚ) : ℝ) <
      ((nookU (varA Φ i.var) i.b i.ge (paramH n Φ) : ℚ) : ℝ) := by exact_mod_cast hGu
  have hxL : (xL n Φ : ℝ) ≤ -3000 := by exact_mod_cast xL_neg n Φ
  set φ := iφ Φ (paramH n Φ) i.var i
  set ψ := iψ Φ (paramH n Φ) i.var i
  have eL : copyLm i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ) = (φ 16, ψ 3) := hLm.symm
  have eR : copyRm i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ) = (φ 17, ψ 3) := hRm.symm
  have hψ3' : ψ 3 = 2 * Hr n Φ := hψ3
  have hψ0' : ψ 0 = 2 * Hr n Φ - 1 / 4 := hψ0
  rw [eL] at hg5 ⊢
  rw [eR] at hg1 ⊢
  try simp only at hg1 hg5
  intro m hm w hw
  rw [mem_segment_horiz_iff (by linarith)] at hm
  obtain ⟨hm2, hm1, hm1'⟩ := hm
  obtain ⟨t, t0, t1, rfl⟩ := mem_segment_iff_lerp.1 hw
  simp only [lerp]
  by_cases hy : g.2 + t * (m.2 - g.2) ≤ 2 * Hr n Φ - 1 / 4
  · refine hall_filled ?_ ?_ ?_ hy
    · have : 0 ≤ t * (g.1 - m.1) := mul_nonneg t0 (by linarith)
      nlinarith
    · have : t * (m.1 - g.1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos t0 (by linarith)
      linarith
    · have : 0 ≤ t * (m.2 - g.2) := mul_nonneg t0 (by rw [hm2]; linarith)
      linarith
  · push Not at hy
    refine nookI_rect hΦ hi nCells_mouth (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    simp only [realR, Rect.set, mem_ofPred_eq]
    rw [hm2] at hy ⊢
    have h1t : (1 - t) * (2 * Hr n Φ - g.2) < 1 / 4 := by nlinarith
    have hd : g.1 - m.1 ≤ 8 * (2 * Hr n Φ - g.2) := by linarith
    have h2 : (1 - t) * (g.1 - m.1) ≤ (1 - t) * (8 * (2 * Hr n Φ - g.2)) :=
      mul_le_mul_of_nonneg_left hd (by linarith)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : 0 ≤ (1 - t) * (g.1 - m.1) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · nlinarith
    · change ψ 0 ≤ _; rw [hψ0']; linarith
    · change _ ≤ ψ 3; rw [hψ3']; nlinarith

/-- The named points of the nook certificate are Stade's copy points. -/
theorem nookI_f : (NRef.f).real ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ)
    ((paramH n Φ : ℚ) : ℝ) (nookPar (varA Φ i.var) i.b i.ge (paramH n Φ)) =
      copyF i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ) := by
  have hX := nookX_cast (varA Φ i.var) i.b i.ge
  simp only [NRef.real, NRef.mp, mpReal, nYB, nE, MP.ev_add, MP.ev_smul, MP.ev_c, nookPar, copyF,
    copyNbot, Hr] at hX ⊢
  rw [hX]
  have hH : (1000 : ℝ) ≤ (paramH n Φ : ℝ) := by exact_mod_cast paramH_ge_q n Φ
  have h1 : (-3 + (paramH n Φ : ℝ) * 2) ≠ 0 := by linarith
  have h2 : (-12 + (paramH n Φ : ℝ) * 8) ≠ 0 := by linarith
  ext <;> simp <;> field_simp <;> ring

/-- **The copy nook of an input.**  A point of a region rectangle of the nook is seen by one of
the two helpers of the nook, by `σ(v)` or `τ(v)`, or is a band point. -/
theorem nookI_cover {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) {R : GRect} (hR : R ∈ cnRR)
    {z : Point}
    (hz : z ∈ (realR (iφ Φ (paramH n Φ) i.var i) (iψ Φ (paramH n Φ) i.var i) R).set) :
    (∃ k ≤ 1, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees
        (gpt (iφ Φ (paramH n Φ) i.var i) (iψ Φ (paramH n Φ) i.var i) (nGuardIdx k)) z) ∨
    (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (varPt (Hr n Φ) (varA Φ i.var) v) z ∨
    (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (inPt i.b v) z ∨ BandOK n Φ z := by
  have hk := inputsO_var hΦ hi
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  have hxs := nookPar_dom (paramH_ge_q n Φ) d1 d2 i.ge
  obtain ⟨hφ, hψ⟩ := nookI_mono hΦ hi
  have hp := nookI_params hΦ hi
  have hH := Hr_ge' (n := n) (Φ := Φ)
  obtain ⟨hR1, hR2⟩ := cnRR_pos R hR
  obtain ⟨p, q, hp1, hp2, hq1, hq2, hzc⟩ := grid_cell hφ hψ hR1 hR2 hz
  obtain ⟨w1, w2⟩ := cnRR_bnd R hR
  have hzP : z ∈ PO n Φ := nookI_reg hΦ hi R hR hz
  -- the target check
  have ht := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 nookTarget_ok R hR) p
    (List.mem_range'_1.2 ⟨hp1, by omega⟩)) q (List.mem_range'_1.2 ⟨hq1, by omega⟩)
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, List.any_eq_true] at ht
  rcases ht with ⟨hq3, hnot⟩ | ⟨ct, hct, hcte⟩
  · -- a strip cell outside the notch
    have mφ : ∀ a c, a ≤ c → c < 20 →
        iφ Φ (paramH n Φ) i.var i a ≤ iφ Φ (paramH n Φ) i.var i c :=
      fun a c hac hc => (hφ.le_iff_le (show a ∈ Iio 20 from lt_of_le_of_lt hac hc) hc).2 hac
    have mψ : ∀ a c, a ≤ c → c < 19 →
        iψ Φ (paramH n Φ) i.var i a ≤ iψ Φ (paramH n Φ) i.var i c :=
      fun a c hac hc => (hψ.le_iff_le (show a ∈ Iio 19 from lt_of_le_of_lt hac hc) hc).2 hac
    obtain ⟨z1, z2, z3, z4⟩ := hzc
    simp only [realR] at z1 z2 z3 z4
    have eH : ((paramH n Φ : ℚ) : ℝ) = Hr n Φ := rfl
    have hψ0 := nook_psi0 (a := (varA Φ i.var : ℚ)) (b := i.b) (H := paramH n Φ) i.ge
    have hψ3 := nook_psi3 (a := (varA Φ i.var : ℚ)) (b := i.b) (H := paramH n Φ) i.ge
    have hψ1 := nook_psi1 (a := (varA Φ i.var : ℚ)) (b := i.b) (H := paramH n Φ) i.ge
    rw [eH] at hψ0 hψ3 hψ1
    have y0 : iψ Φ (paramH n Φ) i.var i 0 ≤ z.2 := (mψ 0 q (by omega) (by omega)).trans z3
    have y3 : z.2 ≤ iψ Φ (paramH n Φ) i.var i 3 := z4.trans (mψ (q + 1) 3 (by omega) (by norm_num))
    have x0 : iφ Φ (paramH n Φ) i.var i 0 ≤ z.1 := (mφ 0 p (by omega) (by omega)).trans z1
    have x19 : z.1 ≤ iφ Φ (paramH n Φ) i.var i 19 := z2.trans (mφ (p + 1) 19 (by omega) (by norm_num))
    -- the extent of the nook: `[x_N − 3, x_N + 7]`
    obtain ⟨-, hGu, hu2⟩ := nook_offsets (paramH_ge_q n Φ) d1 d2 i.ge
    have hu2' : ((nookU (varA Φ i.var) i.b i.ge (paramH n Φ) : ℚ) : ℝ) < 2 := by exact_mod_cast hu2
    have hu0 : (0 : ℝ) < ((nookU (varA Φ i.var) i.b i.ge (paramH n Φ) : ℚ) : ℝ) := by
      have := nook_offsets (paramH_ge_q n Φ) d1 d2 i.ge
      exact_mod_cast (by linarith [this.1, this.2.1] : (0 : ℚ) < nookU (varA Φ i.var) i.b i.ge (paramH n Φ))
    have e0 : iφ Φ (paramH n Φ) i.var i 0 = ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ) -
        ((nookU (varA Φ i.var) i.b i.ge (paramH n Φ) : ℚ) : ℝ) - 7 / 8 := by
      simp only [iφ]; rw [nookφ_eq i.ge (by norm_num)]; simp [cnXe]
    have e19 := (nookI_cols hΦ hi).2.2
    obtain ⟨-, -, -, bX0⟩ := nook_window hΦ hi
    refine Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, ?_, ?_⟩))
    · rintro c' - - ⟨w1', -, -⟩
      have : (0 : ℝ) ≤ slotG n Φ c' := Nat.cast_nonneg _
      linarith
    · rintro i' hi' ⟨e1', e2', e3'⟩
      by_cases hii : i' = i
      · subst hii
        rcases Nat.lt_or_ge p 7 with hp7 | hp7
        · have := mφ (p + 1) 7 (by omega) (by norm_num); linarith
        · rcases Nat.lt_or_ge p 16 with hp16 | hp16
          · have hq0 : q < 1 := by rcases hnot with (h | h) | h <;> omega
            have : z.2 ≤ iψ Φ (paramH n Φ) i'.var i' 1 :=
              z4.trans (mψ (q + 1) 1 (by omega) (by norm_num))
            linarith
          · have := mφ 16 p hp16 (by omega); linarith
      · obtain ⟨e7', e16', -, -⟩ := nook_window hΦ hi'
        rcases nook_sep hΦ hi hi' (Ne.symm hii) with h | h <;> linarith
  · -- a certified cell
    have htree : treeNB (p, q) [] ct.2 = true := by
      have := List.all_eq_true.1 nookCells_ok ct hct
      rw [hcte] at this; exact this
    have hS : IsClosed (PO n Φ) := ArtGallery.Jordan.isClosed_filled _
    have hf := nookI_f hΦ hi
    set X : ℝ := ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ)
    set xs := nookPar (varA Φ i.var) i.b i.ge (paramH n Φ)
    set Hq : ℝ := ((paramH n Φ : ℚ) : ℝ)
    have hzc' : z ∈ nCell X Hq xs (p, q) := hzc
    have hc : (p, q).1 + 1 < 20 ∧ (p, q).2 + 1 < 19 := ⟨by simp; omega, by simp; omega⟩
    -- the copy points
    have hLm := nook_gpt_Lm (varA Φ i.var) i.b i.ge (paramH n Φ)
    have hRm := nook_gpt_Rm (varA Φ i.var) i.b i.ge (paramH n Φ)
    have h15 := nook_φ15 (varA Φ i.var) i.b i.ge (paramH n Φ)
    have h12 := nook_ψ12 (varA Φ i.var) i.b i.ge (paramH n Φ)
    push_cast at hLm hRm h15 h12
    have eH : ((paramH n Φ : ℕ) : ℝ) = Hr n Φ := by simp [Hr]
    have eHq : ((paramH n Φ : ℚ) : ℝ) = Hr n Φ := rfl
    simp only [eH] at hLm hRm h12
    set Lm := copyLm i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ)
    set Rm := copyRm i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ)
    set F := copyF i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ)
    set Nt := copyNtop i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ)
    have gR : ∀ a c : ℕ, (NRef.g a c).real X Hq xs = gpt (iφ Φ (paramH n Φ) i.var i)
        (iψ Φ (paramH n Φ) i.var i) (a, c) := fun a c => NRef.real_g X Hq xs a c
    have gR' : ∀ a c : ℕ, (NRef.g a c).real ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ)
        ((paramH n Φ : ℚ) : ℝ) xs = gpt (iφ Φ (paramH n Φ) i.var i)
        (iψ Φ (paramH n Φ) i.var i) (a, c) := gR
    have hf' : (NRef.f).real ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ) ((paramH n Φ : ℚ) : ℝ) xs = F :=
      hf
    -- the guards see the mouth
    have hσm := nookI_mouth_sees hΦ hi (g := varPt (Hr n Φ) (varA Φ i.var) v)
      (by simp only [varPt]; exact (copy_mouth_lt_a i.ge hp).2.le)
      (by simp only [varPt]; have := varA_le_xR (n := n) (Φ := Φ) hk; have : (0 : ℝ) ≤ ArtGallery.Stade.hH n Φ := (by unfold ArtGallery.Stade.hH; positivity); linarith)
      (by simp only [varPt]; linarith) (by simp only [varPt]; linarith)
      (by
        simp only [varPt]
        obtain ⟨o1, o2⟩ := copyOff_bounds i.ge
        have := (copy_mouth_order i.ge hp)
        have hxL : copyXN i.ge (varA Φ i.var : ℝ) (i.b : ℝ) < Lm.1 := by
          cases hge : i.ge
          · simp only [Lm, copyLm, hge] at this ⊢; exact this.2.1
          · simp only [Lm, copyLm, hge] at this ⊢; exact this.1
        simp only [copyXN] at hxL
        have := hp.hhi
        nlinarith)
    have hτm := nookI_mouth_sees hΦ hi (g := inPt i.b v)
      (by simp only [inPt]; exact (copy_mouth_lt_b i.ge hp).2.le)
      (by
        simp only [inPt]
        obtain ⟨c, hc, δ, -, hδ, hb⟩ := inputsO_b hi
        have := slot_lt_xR (n := n) (Φ := Φ) hc
        have hb' : (i.b : ℝ) = (slotG n Φ c : ℝ) + δ := by rw [hb]; push_cast; ring
        have : ((slotG n Φ c : ℚ) : ℝ) + 1300 ≤ (xR n Φ : ℝ) := by exact_mod_cast this
        have : (δ : ℝ) ≤ 600 := by exact_mod_cast hδ
        push_cast at *
        linarith)
      (by simp only [inPt]; linarith) (by simp only [inPt]; linarith)
      (by
        simp only [inPt]
        obtain ⟨o1, o2⟩ := copyOff_bounds i.ge
        have := (copy_mouth_order i.ge hp)
        have hxL : copyXN i.ge (varA Φ i.var : ℝ) (i.b : ℝ) < Lm.1 := by
          cases hge : i.ge
          · simp only [Lm, copyLm, hge] at this ⊢; exact this.2.1
          · simp only [Lm, copyLm, hge] at this ⊢; exact this.1
        simp only [copyXN] at hxL
        have := hp.hhi
        nlinarith)
    rcases treeNB_sound_q hxs hφ hψ hc hS (nookI_reg hΦ hi) hzc' ct.2 [] htree (by simp) with
      ⟨k, hk1, hseg⟩ | hpk | ⟨hq, hQ⟩
    · -- a helper of the nook
      left
      refine ⟨k, hk1, ?_⟩
      have := hseg
      simp only [nGuardPt, gR] at this
      exact this
    · -- the pocket
      have hzK : z ∈ piece (quad F Lm Rm Nt) := by
        have hl := fun l (hl : l ∈ pocketLns) => hpk l hl
        simp only [pocketLns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, NLn.set, mem_ofPred_eq] at hl
        obtain ⟨l1, l2, l3, l4⟩ := hl
        simp only [hf', gR'] at l1 l2 l3 l4
        refine mem_piece_quad.2 ⟨?_, ?_, ?_, ?_⟩
        · simpa [← hLm] using l1
        · simpa [← hLm, ← hRm] using l2
        · have e : gpt (iφ Φ (paramH n Φ) i.var i) (iψ Φ (paramH n Φ) i.var i) (15, 12) = Nt :=
            Prod.ext h15 h12
          simpa [← hRm, e] using l3
        · have e : gpt (iφ Φ (paramH n Φ) i.var i) (iψ Φ (paramH n Φ) i.var i) (15, 12) = Nt :=
            Prod.ext h15 h12
          simpa [e] using l4
      have mφ : ∀ a c, a ≤ c → c < 20 →
          iφ Φ (paramH n Φ) i.var i a ≤ iφ Φ (paramH n Φ) i.var i c :=
        fun a c hac hc => (hφ.le_iff_le (show a ∈ Iio 20 from lt_of_le_of_lt hac hc) hc).2 hac
      have mψ : ∀ a c, a ≤ c → c < 19 →
          iψ Φ (paramH n Φ) i.var i a ≤ iψ Φ (paramH n Φ) i.var i c :=
        fun a c hac hc => (hψ.le_iff_le (show a ∈ Iio 19 from lt_of_le_of_lt hac hc) hc).2 hac
      have hψ3 : iψ Φ (paramH n Φ) i.var i 3 = 2 * Hr n Φ := by
        have := nook_psi3 (a := (varA Φ i.var : ℚ)) (b := i.b) (H := paramH n Φ) i.ge
        rw [eHq] at this; exact this
      have eLm : Lm = (iφ Φ (paramH n Φ) i.var i 16, iψ Φ (paramH n Φ) i.var i 3) := hLm.symm
      have eRm : Rm = (iφ Φ (paramH n Φ) i.var i 17, iψ Φ (paramH n Φ) i.var i 3) := hRm.symm
      have hF1 : F.1 = iφ Φ (paramH n Φ) i.var i 15 := by simp only [F, copyF_fst]; exact h15.symm
      have hF2 := copyF_snd_gt i.ge hp
      have hFN := copyF_lt_Nbot i.ge hp
      have hNN := copyNbot_lt_Ntop i.ge hp
      have hNt : Nt = (iφ Φ (paramH n Φ) i.var i 15, iψ Φ (paramH n Φ) i.var i 12) :=
        Prod.ext h15.symm h12.symm
      have eLm' : copyLm i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ) =
          (iφ Φ (paramH n Φ) i.var i 16, iψ Φ (paramH n Φ) i.var i 3) := eLm
      have eRm' : copyRm i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ) =
          (iφ Φ (paramH n Φ) i.var i 17, iψ Φ (paramH n Φ) i.var i 3) := eRm
      have hNt' : copyNtop i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ) =
          (iφ Φ (paramH n Φ) i.var i 15, iψ Φ (paramH n Φ) i.var i 12) := hNt
      have hF1' : (copyF i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ)).1 = iφ Φ (paramH n Φ) i.var i 15 := hF1
      have hKP : piece (quad F Lm Rm Nt) ⊆ PO n Φ := by
        have hrect := nookI_rect hΦ hi nCells_pocket (by norm_num) (by norm_num) (by norm_num)
          (by norm_num)
        obtain ⟨c1, c2, c3, c4⟩ := copyF_pocket_ccw i.ge hp
        have m1516 := mφ 15 16 (by norm_num) (by norm_num)
        have m1617 := mφ 16 17 (by norm_num) (by norm_num)
        have m312 := mψ 3 12 (by norm_num) (by norm_num)
        have m1215 := mψ 12 15 (by norm_num) (by norm_num)
        refine (quad_subset_convex (Rect.set_convex _) c1 c2 c3 c4 ?_ ?_ ?_ ?_).trans hrect <;>
          simp only [realR, Rect.set, mem_ofPred_eq]
        · rw [hF1']
          have : F.2 ≤ Nt.2 := by simp only [F, Nt]; linarith
          rw [hNt] at this
          exact ⟨le_rfl, by linarith, by rw [hψ3]; linarith, by simp at this; linarith⟩
        · rw [eLm']; exact ⟨by linarith, by linarith, le_rfl, by linarith⟩
        · rw [eRm']; exact ⟨by linarith, le_rfl, le_rfl, by linarith⟩
        · rw [hNt']; exact ⟨le_rfl, by linarith, by linarith, by linarith⟩
      rcases copyF_pocket_cover' i.ge hp hKP hv1 hv2 hσm hτm z hzK with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · -- the triangle `Q` below the nook segment, only in the cells `(13..14, 4..5)`
      have hqc : (p, q) ∈ nookQCells := by
        have := List.all_eq_true.1 nookCells_q ct hct
        rw [hq, hcte] at this
        simpa using this
      have mφ : ∀ a c, a ≤ c → c < 20 →
          iφ Φ (paramH n Φ) i.var i a ≤ iφ Φ (paramH n Φ) i.var i c :=
        fun a c hac hc => (hφ.le_iff_le (show a ∈ Iio 20 from lt_of_le_of_lt hac hc) hc).2 hac
      have mψ : ∀ a c, a ≤ c → c < 19 →
          iψ Φ (paramH n Φ) i.var i a ≤ iψ Φ (paramH n Φ) i.var i c :=
        fun a c hac hc => (hψ.le_iff_le (show a ∈ Iio 19 from lt_of_le_of_lt hac hc) hc).2 hac
      have eLm : Lm = (iφ Φ (paramH n Φ) i.var i 16, iψ Φ (paramH n Φ) i.var i 3) := hLm.symm
      have eRm : Rm = (iφ Φ (paramH n Φ) i.var i 17, iψ Φ (paramH n Φ) i.var i 3) := hRm.symm
      have hp13 : 13 ≤ p ∧ p ≤ 14 ∧ 4 ≤ q ∧ q ≤ 5 := by
        simp only [nookQCells, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hqc
        omega
      obtain ⟨z1, z2, z3, z4⟩ := hzc
      simp only [realR] at z1 z2 z3 z4
      set C := (realR (iφ Φ (paramH n Φ) i.var i) (iψ Φ (paramH n Φ) i.var i) (13, 17, 3, 6)).set
      have hCP : C ⊆ PO n Φ :=
        nookI_rect hΦ hi nCells_Q (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have hzC : z ∈ C := by
        simp only [C, realR, Rect.set, mem_ofPred_eq]
        exact ⟨(mφ 13 p (by omega) (by omega)).trans z1, z2.trans (mφ (p + 1) 17 (by omega) (by norm_num)),
          (mψ 3 q (by omega) (by omega)).trans z3, z4.trans (mψ (q + 1) 6 (by omega) (by norm_num))⟩
      have hmC : ArtGallery.segment Lm Rm ⊆ C := by
        rw [segment_eq]
        refine (Rect.set_convex _).segment_subset ?_ ?_ <;>
          simp only [C, realR, Rect.set, mem_ofPred_eq, eLm, eRm]
        · exact ⟨mφ 13 16 (by norm_num) (by norm_num), mφ 16 17 (by norm_num) (by norm_num), le_rfl,
            mψ 3 6 (by norm_num) (by norm_num)⟩
        · exact ⟨mφ 13 17 (by norm_num) (by norm_num), le_rfl, le_rfl, mψ 3 6 (by norm_num) (by norm_num)⟩
      -- the three sides of `Q`
      have hl := fun l (hl : l ∈ qLns) => hQ l hl
      simp only [qLns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        NLn.set, mem_ofPred_eq] at hl
      obtain ⟨l1, l2, l3⟩ := hl
      simp only [hf', gR'] at l1 l2 l3
      have hF1 : F.1 = iφ Φ (paramH n Φ) i.var i 15 := by simp only [F, copyF_fst]; exact h15.symm
      have hψ6F : F.2 < iψ Φ (paramH n Φ) i.var i 6 := by
        have := nookψ_eq (a := (varA Φ i.var : ℚ)) (b := i.b) (H := paramH n Φ) i.ge (j := 6)
          (by norm_num)
        simp only [cnYe, cnYs, List.getD_cons_succ, List.getD_cons_zero] at this
        simp only [iψ]
        rw [this]
        simp only [F, copyF_snd, Hr]
        have h3 : (0 : ℝ) < 2 * (paramH n Φ : ℚ) - 3 := by
          have : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := hH
          linarith
        have he : (0 : ℝ) < 3 / (2 * (paramH n Φ : ℚ) - 3) := div_pos (by norm_num) h3
        have he' : (3 : ℝ) / (2 * (paramH n Φ : ℚ) - 3) < 1 / 100 := by
          rw [div_lt_iff₀ h3]
          have : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := hH
          linarith
        push_cast at he he' ⊢
        have : 3 / (4 * (2 * ((paramH n Φ : ℝ)) - 3 * 4 / 4)) = (3 / (2 * (paramH n Φ : ℝ) - 3)) / 4 := by
          field_simp
        nlinarith
      have hz1 : z.1 ≤ copyXN i.ge (varA Φ i.var : ℝ) (i.b : ℝ) := by
        simp only [gpt, det] at l1
        rw [hF1] at l1
        rw [← h15]
        nlinarith
      have m1315 : iφ Φ (paramH n Φ) i.var i 13 < iφ Φ (paramH n Φ) i.var i 15 :=
        hφ (by simp) (by simp) (by norm_num)
      have hz2 : z.2 ≤ (copyNbot i.ge (Hr n Φ) (varA Φ i.var : ℝ) (i.b : ℝ)).2 := by
        simp only [gpt, det] at l2
        have h6 := nook_ψ6_lt (a := (varA Φ i.var : ℚ)) (b := i.b) (paramH_ge_q n Φ) i.ge
        push_cast at h6
        rw [eH] at h6
        nlinarith
      have hzl : 0 ≤ det F Lm z := by
        rw [eLm]; simpa [gpt] using l3
      have hm : ∀ m ∈ ArtGallery.segment Lm Rm, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees
          (if i.ge then inPt i.b v else varPt (Hr n Φ) (varA Φ i.var) v) m := by
        have hσm' : ∀ m ∈ ArtGallery.segment Lm Rm, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees
            (varPt (Hr n Φ) (varA Φ i.var) v) m := hσm
        have hτm' : ∀ m ∈ ArtGallery.segment Lm Rm, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees
            (inPt i.b v) m := hτm
        cases i.ge
        · simpa using hσm'
        · simpa using hτm'
      have := copyQ_sees' i.ge hp (Rect.set_convex _) hCP hmC hv1 hv2 hm hzC hz1 hzl hz2
      cases hge : i.ge
      · rw [hge] at this; exact Or.inr (Or.inl (by simpa using this))
      · rw [hge] at this; exact Or.inr (Or.inr (Or.inl (by simpa using this)))

end Nook

end

end ArtGallery.Orthogonal.Hard
