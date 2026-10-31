module

public import ArtGallery.Orthogonal.Hard.RatEq
public import ArtGallery.Stade.GuardCopy

/-!
# The extended copy pocket

The nook segment of an orthogonal copy nook is Stade's segment `N_bot N_top` extended below
`N_bot` by an eighth of its length, to the foot `F = (x_N, N_bot − e/4)` (`e = 3/(2H − 3)`).  The
guard covering the bottom of the nook (the variable guard for LE, the input guard for GE) still
reaches the extension through the mouth: its shadow through `L_m` lies at or below `F`
(`copyLE_sig_Pt_ext`, `copyGE_tau_Ps_ext`, strengthening Stade's non-restriction lemmas).  Hence
the two guards of the same value see the pocket `F, L_m, R_m, N_top` (`copyF_pocket_cover`).
-/

@[expose] public section

namespace ArtGallery.Stade

open ArtGallery.Geometry

variable {H a b : ℝ}

/-- The foot `F` of the extended nook segment. -/
noncomputable def copyF (ge : Bool) (H a b : ℝ) : Point :=
  (copyXN ge a b, (copyNbot ge H a b).2 - 3 / (4 * (2 * H - 3)))

@[simp] theorem copyF_fst (ge : Bool) : (copyF ge H a b).1 = copyXN ge a b := rfl

theorem copyF_snd (ge : Bool) :
    (copyF ge H a b).2 = 2 * H + 1 - 3 / (2 * H - 3) - 3 / (4 * (2 * H - 3)) := rfl

theorem copyF_snd_gt (ge : Bool) (hp : CopyParams H a b) : 2 * H < (copyF ge H a b).2 := by
  rw [copyF_snd]
  have h3 := hp.pos3
  have e1 : 3 / (2 * H - 3) ≤ 1 / 100 := by rw [div_le_iff₀ h3]; linarith [hp.hH]
  have e2 : 3 / (4 * (2 * H - 3)) ≤ 1 / 100 := by
    rw [div_le_iff₀ (by linarith)]; linarith [hp.hH]
  linarith

theorem copyF_lt_Nbot (ge : Bool) (hp : CopyParams H a b) :
    (copyF ge H a b).2 < (copyNbot ge H a b).2 := by
  have h3 := hp.pos3
  have : 0 < 3 / (4 * (2 * H - 3)) := div_pos (by norm_num) (by linarith)
  simp only [copyF]; linarith

/-- **LE: the shadow of `σ(v)` through `L_m = P_τ` is at or below the foot `F`.** -/
theorem copyLE_sig_Pt_ext (hp : CopyParams H a b) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) :
    vproj (varPt H a v) (copyPt false H a b) (copyXN false a b) ≤ (copyF false H a b).2 := by
  have hX := copyPt_fst_sub_a false hp
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  have h3 := hp.pos3
  obtain ⟨Δ, rfl⟩ : ∃ Δ, b = a + Δ := ⟨b - a, by ring⟩
  simp only [add_sub_cancel_left] at hlo hhi
  have hK : 0 < Δ * H - 2 * Δ + 16 * H - 24 := by nlinarith
  have hH1 : H - 1 ≠ 0 := by linarith
  have hH2 : H * 2 - 1 ≠ 0 := by linarith
  generalize hKd : Δ * H - 2 * Δ + 16 * H - 24 = K at hK
  have hX' : (copyPt false H a (a + Δ)).1 - (varPt H a v).1 = -K / (H - 1) := by
    rw [varPt_fst, hX, ← hKd]; simp only [copyOff]; field_simp; ring
  set N := 4 * Δ * H * v - 9 * Δ * H - 6 * Δ * v + 15 * Δ + 16 * H ^ 2 + 32 * H * v - 136 * H
    - 48 * v + 168 with hN
  have key : vproj (varPt H a v) (copyPt false H a (a + Δ)) (copyXN false a (a + Δ)) -
      (copyF false H a (a + Δ)).2 = -(4 * N - 3 * K) / (4 * (2 * H - 3) * K) := by
    rw [vproj_eq_of hX']
    simp only [varPt, copyPt_snd, copyF, copyNbot_snd, copyXN, copyOff, hN]
    have := hK.ne'; have := h3.ne'; have : H * 2 - 3 ≠ 0 := by linarith
    field_simp
    rw [← hKd]
    ring
  have hnum : 0 ≤ 4 * N - 3 * K := by
    rw [hN, ← hKd]
    nlinarith [mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hv2) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hv2) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hv2) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hhi) (sub_nonneg.2 hH)]
  have hfin := neg_nonpos.2 (div_nonneg hnum (by positivity : (0 : ℝ) ≤ 4 * (2 * H - 3) * K))
  rw [← neg_div, ← key] at hfin
  linarith

/-- **GE: the shadow of `τ(w)` through `L_m = P_σ` is at or below the foot `F`.** -/
theorem copyGE_tau_Ps_ext (hp : CopyParams H a b) {w : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2) :
    vproj (inPt b w) (copyPs true H a b) (copyXN true a b) ≤ (copyF true H a b).2 := by
  have hX := copyPs_fst_sub_b true hp
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  have h3 := hp.pos3
  obtain ⟨Δ, rfl⟩ : ∃ Δ, b = a + Δ := ⟨b - a, by ring⟩
  simp only [add_sub_cancel_left] at hlo hhi
  have hK : 0 < Δ * H - Δ - 6 * H + 9 := by nlinarith
  have hH1 : H - 1 ≠ 0 := by linarith
  have hH2 : H * 2 - 1 ≠ 0 := by linarith
  generalize hKd : Δ * H - Δ - 6 * H + 9 = K at hK
  have hX' : (copyPs true H a (a + Δ)).1 - (inPt (a + Δ) w).1 = -(4 * K) / (2 * H - 1) := by
    rw [inPt_fst, hX, ← hKd]; simp only [copyOff]; field_simp; ring
  set N := 4 * Δ * H * w - 7 * Δ * H - 6 * Δ * w + 9 * Δ + 12 * H ^ 2 - 48 * H * w + 42 * H
    + 72 * w - 90 with hN
  have key : vproj (inPt (a + Δ) w) (copyPs true H a (a + Δ)) (copyXN true a (a + Δ)) -
      (copyF true H a (a + Δ)).2 = -(4 * N - 3 * K) / (4 * (2 * H - 3) * K) := by
    rw [vproj_eq_of hX']
    simp only [inPt, copyPs_snd, copyF, copyNbot_snd, copyXN, copyOff, hN]
    have := hK.ne'; have := h3.ne'; have : H * 2 - 3 ≠ 0 := by linarith
    field_simp
    rw [← hKd]
    ring
  have hnum : 0 ≤ 4 * N - 3 * K := by
    rw [hN, ← hKd]
    nlinarith [mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hw2) (sub_nonneg.2 hhi),
      mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hw2) (sub_nonneg.2 hlo),
      mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hw2) (sub_nonneg.2 hH),
      mul_nonneg (sub_nonneg.2 hhi) (sub_nonneg.2 hH)]
  have hfin := neg_nonpos.2 (div_nonneg hnum (by positivity : (0 : ℝ) ≤ 4 * (2 * H - 3) * K))
  rw [← neg_div, ← key] at hfin
  linarith


/-- A guard below the ceiling and a point above it are on opposite sides of the mouth. -/
theorem copy_side_ext (ge : Bool) (hp : CopyParams H a b) {g : Point} (hg : g.2 < 2 * H) {h : ℝ}
    (hh : 2 * H < h) :
    det (copyLm ge H a b) (copyRm ge H a b) g *
      det (copyLm ge H a b) (copyRm ge H a b) (copyXN ge a b, h) < 0 := by
  rw [copy_det_mouth, copy_det_mouth]
  have h1 := copyLm_lt_Rm ge hp
  have hpos : 0 < (copyRm ge H a b).1 - (copyLm ge H a b).1 := by linarith
  have hA : 0 < h - 2 * H := by linarith
  have hB : 0 < 2 * H - g.2 := by linarith
  nlinarith [mul_pos (mul_pos hpos hpos) (mul_pos hA hB)]

/-- **LE, extended**: every point of the extended nook segment at or below the shadow of `v` is
reached from `σ(v)` through the mouth. -/
theorem copyLE_sig_cross_ext (hp : CopyParams H a b) {v h : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hh1 : (copyF false H a b).2 ≤ h) (hh2 : h ≤ copyShadow H v) :
    ∃ q ∈ segment (copyLm false H a b) (copyRm false H a b),
      q ∈ segment (varPt H a v) (copyXN false a b, h) := by
  obtain ⟨h1, h2⟩ := copy_mouth_lt_a false hp
  refine exists_cross_vert (copy_side_ext false hp (varPt_snd_lt hp hv2)
    (by linarith [copyF_snd_gt false hp])) h1 h2 ?_
  simp only [copyLm_false, copyRm_false]
  rw [copy_vproj_sig false hp]
  have hu := copyLE_sig_Pt_ext hp hv1 hv2
  nlinarith

/-- **GE, extended**: every point of the extended nook segment at or below the shadow of `w` is
reached from `τ(w)` through the mouth. -/
theorem copyGE_tau_cross_ext (hp : CopyParams H a b) {w h : ℝ} (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hh1 : (copyF true H a b).2 ≤ h) (hh2 : h ≤ copyShadow H w) :
    ∃ q ∈ segment (copyLm true H a b) (copyRm true H a b),
      q ∈ segment (inPt b w) (copyXN true a b, h) := by
  obtain ⟨h1, h2⟩ := copy_mouth_lt_b true hp
  refine exists_cross_vert (copy_side_ext true hp (inPt_snd_lt hp hw2)
    (by linarith [copyF_snd_gt true hp])) h1 h2 ?_
  simp only [copyLm_true, copyRm_true]
  rw [copy_vproj_tau true hp]
  have hu := copyGE_tau_Ps_ext hp hw1 hw2
  nlinarith

/-- **The extended pocket is a strictly convex counter-clockwise quadrilateral.** -/
theorem copyF_pocket_ccw (ge : Bool) (hp : CopyParams H a b) :
    0 < det (copyF ge H a b) (copyLm ge H a b) (copyRm ge H a b) ∧
      0 < det (copyLm ge H a b) (copyRm ge H a b) (copyNtop ge H a b) ∧
      0 < det (copyRm ge H a b) (copyNtop ge H a b) (copyF ge H a b) ∧
      0 < det (copyNtop ge H a b) (copyF ge H a b) (copyLm ge H a b) := by
  have hLR := copyLm_lt_Rm ge hp
  have hNB := copyF_snd_gt ge hp
  have hNN : (copyF ge H a b).2 < (copyNtop ge H a b).2 := by
    linarith [copyF_lt_Nbot ge hp, copyNbot_lt_Ntop ge hp]
  obtain ⟨hxL, hxR⟩ : copyXN ge a b < (copyLm ge H a b).1 ∧
      copyXN ge a b < (copyRm ge H a b).1 := by
    obtain ⟨h1, h2, -, -⟩ := copy_mouth_order ge hp
    cases ge
    · exact ⟨h2, h1⟩
    · exact ⟨h1, h2⟩
  unfold det
  simp only [copyLm_snd, copyRm_snd, copyNtop_fst, copyF_fst]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The extended nook segment, explicitly. -/
theorem copyF_nook_iff (ge : Bool) (hp : CopyParams H a b) {s : Point} :
    s ∈ segment (copyF ge H a b) (copyNtop ge H a b) ↔
      s.1 = copyXN ge a b ∧ (copyF ge H a b).2 ≤ s.2 ∧ s.2 ≤ (copyNtop ge H a b).2 := by
  have e1 : copyF ge H a b = (copyXN ge a b, (copyF ge H a b).2) := rfl
  have e2 : copyNtop ge H a b = (copyXN ge a b, (copyNtop ge H a b).2) := rfl
  rw [e1, e2, mem_segment_vert_iff (by linarith [copyF_lt_Nbot ge hp, copyNbot_lt_Ntop ge hp])]

/-- **The extended copy pocket is seen by the two guards of the same value.** -/
theorem copyF_pocket_cover {P : Polygon} (ge : Bool) (hp : CopyParams H a b) {A : Set Point}
    (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hmA : segment (copyLm ge H a b) (copyRm ge H a b) ⊆ A)
    (hKP : piece (quad (copyF ge H a b) (copyLm ge H a b) (copyRm ge H a b) (copyNtop ge H a b)) ⊆
      P.filled) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hσA : varPt H a v ∈ A) (hτA : inPt b v ∈ A) :
    ∀ z ∈ piece (quad (copyF ge H a b) (copyLm ge H a b) (copyRm ge H a b) (copyNtop ge H a b)),
      P.Sees (varPt H a v) z ∨ P.Sees (inPt b v) z := by
  obtain ⟨h1, h2, h3, h4⟩ := copyF_pocket_ccw ge hp
  have hcov := pocket_cover (P := P) (Gs := {varPt H a v, inPt b v}) h1 h2 h3 h4 hKP
    (fun g hg m hm => by
      rcases hg with rfl | rfl
      · exact sees_of_convex hA hAP hσA (hmA hm)
      · exact sees_of_convex hA hAP hτA (hmA hm))
    (fun s hs => by
      obtain ⟨e1, e2, e3⟩ := (copyF_nook_iff ge hp).1 hs
      have e : s = (copyXN ge a b, s.2) := Prod.ext e1 rfl
      cases ge
      · by_cases hsh : s.2 ≤ copyShadow H v
        · obtain ⟨q, hq, hqs⟩ := copyLE_sig_cross_ext hp hv1 hv2 e2 hsh
          exact ⟨_, Or.inl rfl, q, hq, by rw [e]; exact hqs⟩
        · push Not at hsh
          obtain ⟨q, hq, hqs⟩ := copyLE_tau_cross hp hv1 hv2 hsh.le e3
          exact ⟨_, Or.inr rfl, q, hq, by rw [e]; exact hqs⟩
      · by_cases hsh : copyShadow H v ≤ s.2
        · obtain ⟨q, hq, hqs⟩ := copyGE_sig_cross hp hv1 hv2 hsh e3
          exact ⟨_, Or.inl rfl, q, hq, by rw [e]; exact hqs⟩
        · push Not at hsh
          obtain ⟨q, hq, hqs⟩ := copyGE_tau_cross_ext hp hv1 hv2 e2 hsh.le
          exact ⟨_, Or.inr rfl, q, hq, by rw [e]; exact hqs⟩)
  intro z hz
  obtain ⟨g, hg, hgz⟩ := hcov z hz
  rcases hg with rfl | rfl
  · exact Or.inl hgz
  · exact Or.inr hgz


/-! ### Beyond the nook segment: the fan of the bottom guard -/

/-- The line through `g` and `O` in slope form at `O`. -/
theorem vproj_at (g O : Point) (hO : O.1 ≠ g.1) (x : ℝ) :
    vproj g O x = O.2 + (O.2 - g.2) / (O.1 - g.1) * (x - O.1) := by
  have : O.1 - g.1 ≠ 0 := sub_ne_zero.2 hO
  unfold vproj; field_simp; ring

/-- A point above the line `F O`, left of `F`, is above the ray from `g` through `O` when this
ray passes below `F`. -/
theorem fan_lower {g O F : Point} {c h : ℝ} (hO : O.1 < g.1) (hF : F.1 < O.1) (hc : c ≤ F.1)
    (hFv : vproj g O F.1 ≤ F.2) (hl : 0 ≤ det F O (c, h)) : vproj g O c ≤ h := by
  rw [det_vert F O c h (ne_of_gt hF)] at hl
  have hl' : vproj F O c ≤ h := by nlinarith [mul_nonneg_iff.1 hl]
  rw [vproj_at g O hO.ne] at hFv ⊢
  rw [vproj_at F O hF.ne'] at hl'
  have hF2 : vproj F O F.1 = F.2 := by unfold vproj; ring
  rw [vproj_at F O hF.ne'] at hF2
  set sg := (O.2 - g.2) / (O.1 - g.1)
  set sF := (O.2 - F.2) / (O.1 - F.1)
  have hd : 0 ≤ sg - sF := by nlinarith
  nlinarith [mul_nonneg hd (by linarith : (0 : ℝ) ≤ O.1 - c)]

/-- Left of a point, the ray from a guard below `O` through `O` is higher. -/
theorem fan_upper {g O : Point} {c c0 h : ℝ} (hO : O.1 < g.1) (hg : g.2 < O.2) (hc : c ≤ c0)
    (hv : h ≤ vproj g O c0) : h ≤ vproj g O c := by
  rw [vproj_at g O hO.ne] at hv ⊢
  have : (O.2 - g.2) / (O.1 - g.1) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  nlinarith [mul_nonneg_of_nonpos_of_nonpos this (by linarith : c - c0 ≤ 0)]

/-- **The fan of a guard through the mouth**: a point beyond the mouth between the rays of `g`
through its ends is seen by `g`, via a convex set `A` (guard side) and a convex set `R` (nook
side) containing the mouth. -/
theorem fan_sees {P : Polygon} {g L R z : Point} {A C : Set Point} (hA : Convex ℝ A)
    (hAP : A ⊆ P.filled) (hgA : g ∈ A) (hmA : segment L R ⊆ A) (hC : Convex ℝ C)
    (hCP : C ⊆ P.filled) (hmC : segment L R ⊆ C) (hzC : z ∈ C) (hL : L.1 < g.1) (hR : R.1 < g.1)
    (hside : det L R g * det L R z < 0)
    (hh : (z.2 - vproj g L z.1) * (z.2 - vproj g R z.1) ≤ 0) : P.Sees g z := by
  have hside' : det L R g * det L R (z.1, z.2) < 0 := by simpa using hside
  obtain ⟨q, hq, hqz⟩ := exists_cross_vert hside' hL hR hh
  simp only [Prod.mk.eta] at hqz
  exact sees_via hC hCP hqz (sees_of_convex hA hAP hgA (hmA hq)) (hmC hq) hzC

/-- **The triangle below the nook segment** (left of `x_N`, above the line `F L_m`, below
`N_bot`) is seen by the guard covering the bottom of the nook: `σ(v)` for LE, `τ(v)` for GE. -/
theorem copyQ_sees {P : Polygon} (ge : Bool) (hp : CopyParams H a b) {A C : Set Point}
    (hA : Convex ℝ A) (hAP : A ⊆ P.filled)
    (hmA : segment (copyLm ge H a b) (copyRm ge H a b) ⊆ A) (hC : Convex ℝ C)
    (hCP : C ⊆ P.filled) (hmC : segment (copyLm ge H a b) (copyRm ge H a b) ⊆ C)
    {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hgA : (if ge then inPt b v else varPt H a v) ∈ A) {z : Point} (hzC : z ∈ C)
    (hz1 : z.1 ≤ copyXN ge a b) (hzl : 0 ≤ det (copyF ge H a b) (copyLm ge H a b) z)
    (hz2 : z.2 ≤ (copyNbot ge H a b).2) :
    P.Sees (if ge then inPt b v else varPt H a v) z := by
  have hLR := copyLm_lt_Rm ge hp
  obtain ⟨hxL, -⟩ : copyXN ge a b < (copyLm ge H a b).1 ∧ copyXN ge a b < (copyRm ge H a b).1 := by
    obtain ⟨h1, h2, -, -⟩ := copy_mouth_order ge hp
    cases ge
    · exact ⟨h2, h1⟩
    · exact ⟨h1, h2⟩
  have hzl' : 0 ≤ det (copyF ge H a b) (copyLm ge H a b) (z.1, z.2) := by simpa using hzl
  have hFz : 2 * H < z.2 := by
    -- above the line `F L_m`, left of `F`: higher than `F`
    have hF := copyF_snd_gt ge hp
    rw [det_vert _ _ z.1 z.2 (by simp only [copyF_fst]; exact hxL.ne')] at hzl'
    have hpos : 0 < (copyLm ge H a b).1 - (copyF ge H a b).1 := by simp only [copyF_fst]; linarith
    have h1 : vproj (copyF ge H a b) (copyLm ge H a b) z.1 ≤ z.2 := by
      nlinarith [mul_nonneg_iff.1 hzl']
    rw [vproj_at _ _ (by simp only [copyF_fst]; exact hxL.ne')] at h1
    simp only [copyLm_snd, copyF_fst] at h1
    have hs : (2 * H - (copyF ge H a b).2) / ((copyLm ge H a b).1 - copyXN ge a b) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by linarith)
    have := mul_pos_of_neg_of_neg hs (by linarith : z.1 - (copyLm ge H a b).1 < 0)
    linarith
  have hside : ∀ g : Point, g.2 < 2 * H →
      det (copyLm ge H a b) (copyRm ge H a b) g * det (copyLm ge H a b) (copyRm ge H a b) z < 0 := by
    intro g hg
    rw [copy_det_mouth, copy_det_mouth]
    have hpos : 0 < (copyRm ge H a b).1 - (copyLm ge H a b).1 := by linarith
    have hA' : 0 < z.2 - 2 * H := by linarith
    have hB : 0 < 2 * H - g.2 := by linarith
    nlinarith [mul_pos (mul_pos hpos hpos) (mul_pos hA' hB)]
  have hsh := (copyShadow_mem hp hv1 hv2).1
  cases ge
  · -- LE: `σ(v)`, `L_m = P_τ`, `R_m = P_σ`
    simp only [Bool.false_eq_true, ↓reduceIte] at hgA ⊢
    obtain ⟨h1, h2⟩ := copy_mouth_lt_a false hp
    refine fan_sees hA hAP hgA hmA hC hCP hmC hzC h1 h2 (hside _ (varPt_snd_lt hp hv2)) ?_
    have lo := fan_lower (g := varPt H a v) h1 (by simp only [copyF_fst]; exact hxL)
      (by simp only [copyF_fst]; exact hz1)
      (by simp only [copyF_fst, copyLm_false]; exact copyLE_sig_Pt_ext hp hv1 hv2) hzl'
    have up := fan_upper (g := varPt H a v) (O := copyRm false H a b) (c0 := copyXN false a b) (h := z.2) h2
      (by rw [copyRm_snd]; exact varPt_snd_lt hp hv2) hz1
      (by simp only [copyRm_false]; rw [copy_vproj_sig false hp]; simp only [copyNbot_snd] at hz2;
          linarith)
    nlinarith
  · -- GE: `τ(v)`, `L_m = P_σ`, `R_m = P_τ`
    simp only [↓reduceIte] at hgA ⊢
    obtain ⟨h1, h2⟩ := copy_mouth_lt_b true hp
    refine fan_sees hA hAP hgA hmA hC hCP hmC hzC h1 h2 (hside _ (inPt_snd_lt hp hv2)) ?_
    have lo := fan_lower (g := inPt b v) h1 (by simp only [copyF_fst]; exact hxL)
      (by simp only [copyF_fst]; exact hz1)
      (by simp only [copyF_fst, copyLm_true]; exact copyGE_tau_Ps_ext hp hv1 hv2) hzl'
    have up := fan_upper (g := inPt b v) (O := copyRm true H a b) (c0 := copyXN true a b) (h := z.2) h2
      (by rw [copyRm_snd]; exact inPt_snd_lt hp hv2) hz1
      (by simp only [copyRm_true]; rw [copy_vproj_tau true hp]; simp only [copyNbot_snd] at hz2;
          linarith)
    nlinarith

/-! ### Variants with the visibility of the mouth as hypothesis -/

/-- **The extended copy pocket**, the two guards seeing the mouth. -/
theorem copyF_pocket_cover' {P : Polygon} (ge : Bool) (hp : CopyParams H a b)
    (hKP : piece (quad (copyF ge H a b) (copyLm ge H a b) (copyRm ge H a b) (copyNtop ge H a b)) ⊆
      P.filled) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hσ : ∀ m ∈ segment (copyLm ge H a b) (copyRm ge H a b), P.Sees (varPt H a v) m)
    (hτ : ∀ m ∈ segment (copyLm ge H a b) (copyRm ge H a b), P.Sees (inPt b v) m) :
    ∀ z ∈ piece (quad (copyF ge H a b) (copyLm ge H a b) (copyRm ge H a b) (copyNtop ge H a b)),
      P.Sees (varPt H a v) z ∨ P.Sees (inPt b v) z := by
  obtain ⟨h1, h2, h3, h4⟩ := copyF_pocket_ccw ge hp
  have hcov := pocket_cover (P := P) (Gs := {varPt H a v, inPt b v}) h1 h2 h3 h4 hKP
    (fun g hg m hm => by
      rcases hg with rfl | rfl
      · exact hσ m hm
      · exact hτ m hm)
    (fun s hs => by
      obtain ⟨e1, e2, e3⟩ := (copyF_nook_iff ge hp).1 hs
      have e : s = (copyXN ge a b, s.2) := Prod.ext e1 rfl
      cases ge
      · by_cases hsh : s.2 ≤ copyShadow H v
        · obtain ⟨q, hq, hqs⟩ := copyLE_sig_cross_ext hp hv1 hv2 e2 hsh
          exact ⟨_, Or.inl rfl, q, hq, by rw [e]; exact hqs⟩
        · push Not at hsh
          obtain ⟨q, hq, hqs⟩ := copyLE_tau_cross hp hv1 hv2 hsh.le e3
          exact ⟨_, Or.inr rfl, q, hq, by rw [e]; exact hqs⟩
      · by_cases hsh : copyShadow H v ≤ s.2
        · obtain ⟨q, hq, hqs⟩ := copyGE_sig_cross hp hv1 hv2 hsh e3
          exact ⟨_, Or.inl rfl, q, hq, by rw [e]; exact hqs⟩
        · push Not at hsh
          obtain ⟨q, hq, hqs⟩ := copyGE_tau_cross_ext hp hv1 hv2 e2 hsh.le
          exact ⟨_, Or.inr rfl, q, hq, by rw [e]; exact hqs⟩)
  intro z hz
  obtain ⟨g, hg, hgz⟩ := hcov z hz
  rcases hg with rfl | rfl
  · exact Or.inl hgz
  · exact Or.inr hgz

/-- The fan through the mouth, the guard seeing the mouth. -/
theorem fan_sees' {P : Polygon} {g L R z : Point} {C : Set Point}
    (hm : ∀ m ∈ segment L R, P.Sees g m) (hC : Convex ℝ C)
    (hCP : C ⊆ P.filled) (hmC : segment L R ⊆ C) (hzC : z ∈ C) (hL : L.1 < g.1) (hR : R.1 < g.1)
    (hside : det L R g * det L R z < 0)
    (hh : (z.2 - vproj g L z.1) * (z.2 - vproj g R z.1) ≤ 0) : P.Sees g z := by
  have hside' : det L R g * det L R (z.1, z.2) < 0 := by simpa using hside
  obtain ⟨q, hq, hqz⟩ := exists_cross_vert hside' hL hR hh
  simp only [Prod.mk.eta] at hqz
  exact sees_via hC hCP hqz (hm q hq) (hmC hq) hzC

/-- **The triangle below the nook segment**, the bottom guard seeing the mouth. -/
theorem copyQ_sees' {P : Polygon} (ge : Bool) (hp : CopyParams H a b) {C : Set Point}
    (hC : Convex ℝ C)
    (hCP : C ⊆ P.filled) (hmC : segment (copyLm ge H a b) (copyRm ge H a b) ⊆ C)
    {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2)
    (hm : ∀ m ∈ segment (copyLm ge H a b) (copyRm ge H a b),
      P.Sees (if ge then inPt b v else varPt H a v) m) {z : Point} (hzC : z ∈ C)
    (hz1 : z.1 ≤ copyXN ge a b) (hzl : 0 ≤ det (copyF ge H a b) (copyLm ge H a b) z)
    (hz2 : z.2 ≤ (copyNbot ge H a b).2) :
    P.Sees (if ge then inPt b v else varPt H a v) z := by
  have hLR := copyLm_lt_Rm ge hp
  obtain ⟨hxL, -⟩ : copyXN ge a b < (copyLm ge H a b).1 ∧ copyXN ge a b < (copyRm ge H a b).1 := by
    obtain ⟨h1, h2, -, -⟩ := copy_mouth_order ge hp
    cases ge
    · exact ⟨h2, h1⟩
    · exact ⟨h1, h2⟩
  have hzl' : 0 ≤ det (copyF ge H a b) (copyLm ge H a b) (z.1, z.2) := by simpa using hzl
  have hFz : 2 * H < z.2 := by
    have hF := copyF_snd_gt ge hp
    rw [det_vert _ _ z.1 z.2 (by simp only [copyF_fst]; exact hxL.ne')] at hzl'
    have hpos : 0 < (copyLm ge H a b).1 - (copyF ge H a b).1 := by simp only [copyF_fst]; linarith
    have h1 : vproj (copyF ge H a b) (copyLm ge H a b) z.1 ≤ z.2 := by
      nlinarith [mul_nonneg_iff.1 hzl']
    rw [vproj_at _ _ (by simp only [copyF_fst]; exact hxL.ne')] at h1
    simp only [copyLm_snd, copyF_fst] at h1
    have hs : (2 * H - (copyF ge H a b).2) / ((copyLm ge H a b).1 - copyXN ge a b) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by linarith)
    have := mul_pos_of_neg_of_neg hs (by linarith : z.1 - (copyLm ge H a b).1 < 0)
    linarith
  have hside : ∀ g : Point, g.2 < 2 * H →
      det (copyLm ge H a b) (copyRm ge H a b) g * det (copyLm ge H a b) (copyRm ge H a b) z < 0 := by
    intro g hg
    rw [copy_det_mouth, copy_det_mouth]
    have hpos : 0 < (copyRm ge H a b).1 - (copyLm ge H a b).1 := by linarith
    have hA' : 0 < z.2 - 2 * H := by linarith
    have hB : 0 < 2 * H - g.2 := by linarith
    nlinarith [mul_pos (mul_pos hpos hpos) (mul_pos hA' hB)]
  have hsh := (copyShadow_mem hp hv1 hv2).1
  cases ge
  · simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢
    obtain ⟨h1, h2⟩ := copy_mouth_lt_a false hp
    refine fan_sees' hm hC hCP hmC hzC h1 h2 (hside _ (varPt_snd_lt hp hv2)) ?_
    have lo := fan_lower (g := varPt H a v) h1 (by simp only [copyF_fst]; exact hxL)
      (by simp only [copyF_fst]; exact hz1)
      (by simp only [copyF_fst, copyLm_false]; exact copyLE_sig_Pt_ext hp hv1 hv2) hzl'
    have up := fan_upper (g := varPt H a v) (O := copyRm false H a b) (c0 := copyXN false a b) (h := z.2) h2
      (by rw [copyRm_snd]; exact varPt_snd_lt hp hv2) hz1
      (by simp only [copyRm_false]; rw [copy_vproj_sig false hp]; simp only [copyNbot_snd] at hz2;
          linarith)
    nlinarith
  · simp only [↓reduceIte] at hm ⊢
    obtain ⟨h1, h2⟩ := copy_mouth_lt_b true hp
    refine fan_sees' hm hC hCP hmC hzC h1 h2 (hside _ (inPt_snd_lt hp hv2)) ?_
    have lo := fan_lower (g := inPt b v) h1 (by simp only [copyF_fst]; exact hxL)
      (by simp only [copyF_fst]; exact hz1)
      (by simp only [copyF_fst, copyLm_true]; exact copyGE_tau_Ps_ext hp hv1 hv2) hzl'
    have up := fan_upper (g := inPt b v) (O := copyRm true H a b) (c0 := copyXN true a b) (h := z.2) h2
      (by rw [copyRm_snd]; exact inPt_snd_lt hp hv2) hz1
      (by simp only [copyRm_true]; rw [copy_vproj_tau true hp]; simp only [copyNbot_snd] at hz2;
          linarith)
    nlinarith

end ArtGallery.Stade

end
