module

public import ArtGallery.Orthogonal.Hard.CovBand
public import ArtGallery.Orthogonal.Hard.LowerO

/-!
# The strips are seen by the variable guard of `0` and by `H_L`

The variable guard `g₀ = (a₀, H + 2v − 1)` of variable `0` sees every point of the region in the
hall and the floor strip, except in the block windows of the `invRevLe` slots
(`sees_g0_floor`); every point of the ceiling strip outside the notch windows of the copy nooks
is seen by `g₀` or by the basin helper `H_L = (x_L + 25/2, −5/2)` (`sees_ceil`).  A segment from
`g₀` (resp. `H_L`) crosses each strip within less than two units of its endpoint, where only the
floor block or a notch can stop it.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### The region lies between the walls -/

theorem PO_x {p : Point} (hp : p ∈ PO n Φ) : (xL n Φ : ℝ) ≤ p.1 ∧ p.1 ≤ xR n Φ := by
  rw [PO, filledO] at hp
  obtain ⟨r, hr, hpr⟩ := hp
  simp only [regionRectsO, combRects, List.mem_cons, List.mem_append, List.mem_map] at hr
  rcases hr with rfl | hr | ⟨r', hr', rfl⟩
  · exact ⟨hpr.1, hpr.2.1⟩
  · have := hc_box zfO_good zord_zfO r hr p hpr
    exact ⟨this.1, this.2.1⟩
  · have := hc_box zcO_good zord_zcO r' hr' (-p) (Rect.mem_neg.1 hpr)
    simp only [Prod.fst_neg] at this
    constructor <;> linarith [this.1, this.2.1]

/-- `x_R ≤ 2H + 100`. -/
theorem xR_le : (xR n Φ : ℝ) ≤ 2 * Hr n Φ + 100 := by
  have h := paramH_ge' n Φ
  have : (paramX0 n Φ : ℚ) + 1200 * paramC Φ ≤ 2 * (paramH n Φ : ℚ) := by
    unfold paramX0
    have : ((n - 1) * paramDV Φ + 1200 * paramC Φ : ℕ) ≤ paramH n Φ := h
    have : (((n - 1) * paramDV Φ + 1200 * paramC Φ : ℕ) : ℚ) ≤ paramH n Φ := by exact_mod_cast this
    push_cast at this ⊢
    linarith
  have e : (xR n Φ : ℚ) ≤ 2 * (paramH n Φ : ℚ) + 100 := by unfold xR; linarith
  simp only [Hr]; exact_mod_cast e

theorem xL_eq : (xL n Φ : ℝ) = -3 * Hr n Φ := by simp [xL, Hr]

/-- The basin rectangle `[x_L + 12, x_L + 20] × [−3, −1/4]` lies in the region. -/
theorem basin_rect_filled {p : Point} (h1 : (xL n Φ : ℝ) + 12 ≤ p.1) (h2 : p.1 ≤ (xL n Φ : ℝ) + 20)
    (h3 : -3 ≤ p.2) (h4 : p.2 ≤ -1 / 4) : p ∈ PO n Φ := by
  have hZ : fzone oBasin (paramH n Φ) (xL n Φ) ∈ zfO n Φ := by simp [zfO]
  have hl : (⟨12, 20, (-3, 0), (-1 / 4, 0)⟩ : LR) ∈ tzLR oBasin (fz oBasin) false := by decide +kernel
  have hr : LR.real (xL n Φ : ℝ) ((paramH n Φ : ℚ) : ℝ) ⟨12, 20, (-3, 0), (-1 / 4, 0)⟩ ∈
      (fzone oBasin (paramH n Φ) (xL n Φ)).rs := by
    rw [fzone_rs]; exact List.mem_map.2 ⟨_, hl, rfl⟩
  refine mem_filled_of_region (zone_rect_floor hZ hr) ?_
  simp only [LR.real, AH.ev, Rect.set, mem_ofPred_eq]
  push_cast
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### The copy nooks -/

theorem nook_phi7 {a b H : ℚ} (ge : Bool) :
    nookφ a b ge H 7 = ((nookX a b ge : ℚ) : ℝ) - 1 / 2 := by
  rw [nookφ_eq ge (by norm_num)]; simp [cnXe, cnXs]

theorem nook_phi16 {a b H : ℚ} (ge : Bool) :
    nookφ a b ge H 16 = ((nookX a b ge : ℚ) : ℝ) + ((nookG a b ge H : ℚ) : ℝ) := by
  rw [nookφ_eq ge (by norm_num)]; simp [cnXe, cnXs]

theorem nook_psi1 {a b H : ℚ} (ge : Bool) : nookψ a b ge H 1 = 2 * (H : ℝ) - 1 / 8 := by
  rw [nookψ_eq ge (by norm_num)]; simp [cnYe, cnYs]

/-- The notch window of the nook of an input lies in `[x_N − 1/2, x_N + 2]`, between
`x_L + 99` and `−98`. -/
theorem nook_window (hΦ : ∀ c ∈ Φ, c.VarsLt n) {i : InputSeg} (hi : i ∈ inputsO n Φ) :
    iφ Φ (paramH n Φ) i.var i 7 = ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ) - 1 / 2 ∧
    iφ Φ (paramH n Φ) i.var i 16 ≤ ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ) + 2 ∧
    (xL n Φ : ℝ) + 100 ≤ ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ) ∧
    ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ) + 100 ≤ 0 := by
  have hk := inputsO_var hΦ hi
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  obtain ⟨-, hGu, hu⟩ := nook_offsets (paramH_ge_q n Φ) d1 d2 i.ge
  obtain ⟨b1, b2⟩ := nookX_bounds hΦ hi
  refine ⟨nook_phi7 i.ge, ?_, b1, b2⟩
  show nookφ _ _ _ _ 16 ≤ _
  rw [nook_phi16]
  have : ((nookG (varA Φ i.var) i.b i.ge (paramH n Φ) : ℚ) : ℝ) ≤ 2 := by
    exact_mod_cast (hGu.trans hu).le
  linarith

/-- The nooks of distinct inputs are at least `10` apart. -/
theorem nook_sep (hΦ : ∀ c ∈ Φ, c.VarsLt n) {i i' : InputSeg} (hi : i ∈ inputsO n Φ)
    (hi' : i' ∈ inputsO n Φ) (hne : i ≠ i') :
    ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ) + 10 ≤ nookX (varA Φ i'.var) i'.b i'.ge ∨
      ((nookX (varA Φ i'.var) i'.b i'.ge : ℚ) : ℝ) + 10 ≤ nookX (varA Φ i.var) i.b i.ge := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
  obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hi'
  have hjj : j ≠ j' := fun h => hne (by subst h; rfl)
  rcases lt_or_gt_of_ne hjj with h | h
  · rcases nookX_sep hΦ hj hj' h with h' | h'
    · right; exact_mod_cast h'
    · left; exact_mod_cast h'
  · rcases nookX_sep hΦ hj' hj h with h' | h'
    · left; exact_mod_cast h'
    · right; exact_mod_cast h'


/-! ### The variable guard of `0` -/

/-- The guard of variable `0` of value `v`. -/
noncomputable def gZero (n : ℕ) (Φ : List Constraint) (v : ℝ) : Point := (0, Hr n Φ + 2 * v - 1)

/-- The basin helper `H_L`. -/
noncomputable def hL (n : ℕ) (Φ : List Constraint) : Point := ((xL n Φ : ℝ) + 25 / 2, -5 / 2)

theorem Hr_ge' : (1000 : ℝ) ≤ Hr n Φ := Hr_ge n Φ

/-- **The hall and the floor strip are seen by `g₀`**, outside the block windows of the
`invRevLe` slots. -/
theorem sees_g0_floor {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) {z : Point} (hz : z ∈ PO n Φ)
    (hz1 : -1 ≤ z.2) (hz2 : z.2 ≤ 2 * Hr n Φ - 1 / 4)
    (hW : ∀ c < paramC Φ, cKind (gadAt Φ c) = .invRevLe →
      ¬((slotG n Φ c : ℝ) + 31 < z.1 ∧ z.1 < (slotG n Φ c : ℝ) + 61 ∧ z.2 < -1 / 2)) :
    (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (gZero n Φ v) z := by
  intro w ⟨t, t0, t1, hw⟩
  have hH := Hr_ge' (n := n) (Φ := Φ)
  obtain ⟨zx1, zx2⟩ := PO_x hz
  have hxL : (xL n Φ : ℝ) ≤ -3000 := by exact_mod_cast xL_neg n Φ
  have hxR : (100 : ℝ) ≤ xR n Φ := by exact_mod_cast xR_pos n Φ
  have hxR2 := xR_le (n := n) (Φ := Φ)
  simp only [gZero] at hw
  set g2 := Hr n Φ + 2 * v - 1 with hg2
  have wx : w.1 = t * z.1 := by rw [hw]; ring
  have wy : w.2 = g2 + t * (z.2 - g2) := by rw [hw]
  have hx1 : (xL n Φ : ℝ) ≤ w.1 := by rw [wx]; nlinarith
  have hx2 : w.1 ≤ xR n Φ := by rw [wx]; nlinarith
  by_cases hy : -1 / 4 ≤ w.2
  · exact hall_filled hx1 hx2 hy (by rw [wy]; nlinarith)
  push Not at hy
  have hwz : z.2 ≤ w.2 := by rw [wy]; nlinarith
  rcases floor_band hx1 hx2 (by linarith) hy.le with h | ⟨c, hc, hk, w1, w2, w3⟩
  · exact h
  · by_cases ht : t = 1
    · subst ht
      have : w = z := by rw [hw]; ext <;> simp
      rw [this]; exact hz
    exfalso
    have ht1 : t < 1 := lt_of_le_of_ne t1 ht
    have hG : (0 : ℝ) ≤ slotG n Φ c := Nat.cast_nonneg _
    have hpos : 0 < t * z.1 := by rw [← wx]; linarith
    have hz0 : 0 < z.1 := by
      by_contra h; push Not at h; nlinarith
    have e1 : (1 - t) * (g2 - z.2) = w.2 - z.2 := by rw [wy]; ring
    have hgz : Hr n Φ ≤ g2 - z.2 := by rw [hg2]; nlinarith
    have hzw : z.2 < w.2 := by nlinarith
    have h1t : (1 - t) * Hr n Φ ≤ 1 / 2 := by nlinarith
    have hzx : (1 - t) * z.1 < 2 := by nlinarith
    refine hW c hc hk ⟨by nlinarith, by nlinarith, by linarith⟩

/-! ### The ceiling strip -/

theorem nook_window' (hΦ : ∀ c ∈ Φ, c.VarsLt n) {i : InputSeg} (hi : i ∈ inputsO n Φ) :
    iψ Φ (paramH n Φ) i.var i 1 = 2 * Hr n Φ - 1 / 8 := by
  simp only [iψ, Hr]; rw [nook_psi1]

set_option maxHeartbeats 1000000 in
/-- **The ceiling strip is seen by `g₀` or by `H_L`**, outside the notch windows of the copy
nooks. -/
theorem sees_ceil (hΦ : ∀ c ∈ Φ, c.VarsLt n) {v : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) {z : Point}
    (hz : z ∈ PO n Φ) (hz1 : 2 * Hr n Φ - 1 / 4 < z.2) (hz2 : z.2 ≤ 2 * Hr n Φ)
    (hE : ∀ i ∈ inputsO n Φ, ¬(iφ Φ (paramH n Φ) i.var i 7 < z.1 ∧
      z.1 < iφ Φ (paramH n Φ) i.var i 16 ∧ iψ Φ (paramH n Φ) i.var i 1 < z.2)) :
    (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (gZero n Φ v) z ∨
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (hL n Φ) z := by
  classical
  have hH := Hr_ge' (n := n) (Φ := Φ)
  obtain ⟨zx1, zx2⟩ := PO_x hz
  have hxL : (xL n Φ : ℝ) ≤ -3000 := by exact_mod_cast xL_neg n Φ
  have hxR : (100 : ℝ) ≤ xR n Φ := by exact_mod_cast xR_pos n Φ
  have hxR2 := xR_le (n := n) (Φ := Φ)
  have hxLe := xL_eq (n := n) (Φ := Φ)
  by_cases hall : ArtGallery.segment (gZero n Φ v) z ⊆ PO n Φ
  · exact Or.inl hall
  right
  obtain ⟨w, ⟨t, t0, t1, hw⟩, hwP⟩ := Set.not_subset.1 hall
  simp only [gZero] at hw
  set g2 := Hr n Φ + 2 * v - 1 with hg2
  have wx : w.1 = t * z.1 := by rw [hw]; ring
  have wy : w.2 = g2 + t * (z.2 - g2) := by rw [hw]
  have hx1 : (xL n Φ : ℝ) ≤ w.1 := by rw [wx]; nlinarith
  have hx2 : w.1 ≤ xR n Φ := by rw [wx]; nlinarith
  have hwy1 : 2 * Hr n Φ - 1 / 4 < w.2 := by
    by_contra h; push Not at h
    exact hwP (hall_filled hx1 hx2 (by rw [wy]; nlinarith) h)
  have hwy2 : w.2 ≤ 2 * Hr n Φ := by rw [wy]; nlinarith
  rcases ceil_band hx1 hx2 hwy1.le hwy2 with h | ⟨i, hi, w1, w2, w3⟩
  · exact absurd h hwP
  have ht : t ≠ 1 := by
    intro ht; subst ht; apply hwP
    have : w = z := by rw [hw]; ext <;> simp
    rw [this]; exact hz
  have ht1 : t < 1 := lt_of_le_of_ne t1 ht
  obtain ⟨e7, e16, eL, e0⟩ := nook_window hΦ hi
  set xN := ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ)
  have hneg : t * z.1 < 0 := by rw [← wx]; linarith
  have hz0 : z.1 < 0 := by by_contra h; push Not at h; nlinarith
  have e1 : (1 - t) * (z.2 - g2) = z.2 - w.2 := by rw [wy]; ring
  have hgz : Hr n Φ - 4 ≤ z.2 - g2 := by rw [hg2]; nlinarith
  have hzw : w.2 < z.2 := by nlinarith
  have hzx1 : z.1 < w.1 := by
    rw [wx]; nlinarith [mul_pos (sub_pos.2 ht1) (neg_pos.2 hz0)]
  have hz7 : z.1 ≤ iφ Φ (paramH n Φ) i.var i 7 := by
    by_contra h; push Not at h
    exact hE i hi ⟨h, by linarith, by linarith⟩
  have h1t : (1 - t) * (Hr n Φ - 4) ≤ 1 / 4 := by nlinarith
  have hzx2 : w.1 - z.1 < 1 := by
    have : w.1 - z.1 = (1 - t) * (-z.1) := by rw [wx]; ring
    rw [this]; nlinarith
  -- `H_L` sees `z`
  intro u ⟨s, s0, s1, hu⟩
  simp only [hL] at hu
  set d := z.1 - ((xL n Φ : ℝ) + 25 / 2) with hd
  have ux : u.1 = (xL n Φ : ℝ) + 25 / 2 + s * d := by rw [hu]
  have uy : u.2 = -5 / 2 + s * (z.2 - -5 / 2) := by rw [hu]
  have hdz : 80 ≤ d := by rw [hd]; linarith
  have hdH : d ≤ 5 * Hr n Φ + 100 := by rw [hd]; linarith
  have hsd0 : 0 ≤ s * d := mul_nonneg s0 (by linarith)
  have hsd1 : s * d ≤ d := mul_le_of_le_one_left (by linarith) s1
  have hy0 : 0 ≤ z.2 - -5 / 2 := by linarith
  have hsy0 : 0 ≤ s * (z.2 - -5 / 2) := mul_nonneg s0 hy0
  have hsy1 : s * (z.2 - -5 / 2) ≤ z.2 - -5 / 2 := mul_le_of_le_one_left hy0 s1
  have hu1 : (xL n Φ : ℝ) ≤ u.1 := by rw [ux]; linarith
  have hu2 : u.1 ≤ xR n Φ := by rw [ux]; linarith
  by_cases hya : u.2 ≤ -1 / 4
  · have hs : s * (z.2 - -5 / 2) ≤ 9 / 4 := by rw [uy] at hya; linarith
    have hs' : s * (2 * Hr n Φ) ≤ s * (z.2 - -5 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) s0
    have hsH : s * 1000 ≤ s * Hr n Φ := mul_le_mul_of_nonneg_left hH s0
    have hsdH : s * d ≤ s * (5 * Hr n Φ + 100) := mul_le_mul_of_nonneg_left hdH s0
    refine basin_rect_filled (by rw [ux]; linarith) ?_ (by rw [uy]; linarith) hya
    rw [ux]
    linarith
  push Not at hya
  by_cases hyb : u.2 ≤ 2 * Hr n Φ - 1 / 4
  · exact hall_filled hu1 hu2 hya.le hyb
  push Not at hyb
  have huy2 : u.2 ≤ 2 * Hr n Φ := by rw [uy]; linarith
  rcases ceil_band hu1 hu2 hyb.le huy2 with h | ⟨i', hi', v1, v2, -⟩
  · exact h
  by_cases hs : s = 1
  · subst hs
    have : u = z := by
      ext
      · rw [ux, hd]; ring
      · rw [uy]; ring
    rw [this]; exact hz
  exfalso
  have hs1 : s < 1 := lt_of_le_of_ne s1 hs
  have f1 : (1 - s) * (z.2 - -5 / 2) = z.2 - u.2 := by rw [uy]; ring
  have f2' : (1 - s) * (2 * Hr n Φ) ≤ (1 - s) * (z.2 - -5 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have f2 : (1 - s) * (2 * Hr n Φ) ≤ 1 / 4 := by linarith
  have f3 : z.1 - u.1 = (1 - s) * d := by rw [ux]; ring
  have f4 : 0 < z.1 - u.1 := by rw [f3]; exact mul_pos (by linarith) (by linarith)
  have f6 : (1 - s) * 1000 ≤ (1 - s) * Hr n Φ := mul_le_mul_of_nonneg_left hH (by linarith)
  have f7 : (1 - s) * d ≤ (1 - s) * (5 * Hr n Φ + 100) := mul_le_mul_of_nonneg_left hdH (by linarith)
  have f5 : z.1 - u.1 < 1 := by rw [f3]; linarith
  by_cases hii : i' = i
  · subst hii; linarith
  · obtain ⟨e7', e16', -, -⟩ := nook_window hΦ hi'
    rcases nook_sep hΦ hi hi' (Ne.symm hii) with h | h <;> linarith

end

end ArtGallery.Orthogonal.Hard
