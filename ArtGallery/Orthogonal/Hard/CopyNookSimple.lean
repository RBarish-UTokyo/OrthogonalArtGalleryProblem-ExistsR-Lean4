module

public import ArtGallery.Orthogonal.Hard.Poly
public import ArtGallery.Orthogonal.Hard.Comb

/-!
# The orthogonal copy nook is a dented ceiling feature

The 46 vertices of `copyNookO a b ge H` are written in terms of four quantities: the nook
abscissa `x_N`, the offsets `u = R_m.x − x_N` and `G = L_m.x − x_N` of the mouth corners and
`e = 3/(2H − 3)` (half the length of the nook segment).  Their abscissae take 18 values and
their ordinates 18 values, in an order that does not depend on the instance once
`1 < G < u < 2` and `0 < e < 1/100` (`cnXs_chain`, `cnYs_chain`); the chain of grid indices
(`cnGrid`) is checked by `decide`, and `ceilFeatureD_of_mono` transfers the check
(`copyNookO_ceilD`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade ArtGallery.Stade.Chain

/-- The 18 abscissae of the copy nook, increasing. -/
def cnXs (xN u G e : ℚ) : List ℚ :=
  [xN - u - 3 / 4, xN - u - 1 / 4, xN - u - 1 / 32, xN - u, xN - u + 1 / 32, xN - u + 1 / 4,
    xN - 1 / 2, xN - 27 * G * e / 64 - 9 * e / 32, xN - 27 * G * e / 64,
    xN - 9 * G * e / 32 - 9 * e / 512, xN - 9 * G * e / 32, xN - 9 * G * e / 32 + 9 * e / 512,
    xN - 9 * G * e / 64, xN - 9 * G * e / 128, xN, xN + G, xN + u, xN + 3 * u + 1 / 4]

/-- The 18 ordinates of the copy nook, increasing (the bottom of the orthogonal nook segment is
`2H + 1 − 5e/4`). -/
def cnYs (G e H : ℚ) : List ℚ :=
  [2 * H - 1 / 8, 2 * H - 1 / 16, 2 * H, 2 * H + (1 + e) - 1 / 2,
    2 * H + 1 - 5 * e / 4 + (1 - 5 * e / 4) * (9 * e / 32) - 9 * G * e / 64,
    2 * H + 1 - 5 * e / 4 + (1 - 5 * e / 4) * (9 * e / 64),
    2 * H + 1 - 5 * e / 4 + (1 - 5 * e / 4) * (9 * e / 32) - 9 * e / 512,
    2 * H + 1 - 5 * e / 4 + (1 - 5 * e / 4) * (9 * e / 32),
    2 * H + 1 - 5 * e / 4 + (1 - 5 * e / 4) * (9 * e / 32) + 9 * e / 512,
    2 * H + 1 - 5 * e / 4 + (1 - 5 * e / 4) * (9 * e / 32) + 9 * G * e / 64,
    2 * H + 1 - 5 * e / 4 + (1 - 5 * e / 4) * (9 * e / 32) + 9 * G * e / 64 + 9 * e / 64,
    2 * H + (1 + e),
    2 * H + 2 * (1 + e) - 1 / 4, 2 * H + 2 * (1 + e) - 1 / 32, 2 * H + 2 * (1 + e),
    2 * H + 2 * (1 + e) + 1 / 32, 2 * H + 2 * (1 + e) + 1 / 4, 2 * H + 3 * (1 + e) + 1 / 2]

/-- The grid indices of the 46 vertices of the copy nook. -/
def cnGrid : List (ℕ × ℕ) :=
  [(16, 2), (16, 13), (17, 13), (17, 14), (5, 14), (5, 16), (4, 16), (4, 17), (3, 17), (3, 16),
    (1, 16), (1, 15), (0, 15), (0, 14), (1, 14), (1, 12), (2, 12), (2, 3), (3, 3), (3, 11),
    (14, 11), (14, 5), (12, 5), (12, 7), (13, 7), (13, 8), (12, 8), (12, 9), (10, 9), (10, 10),
    (9, 10), (9, 9), (8, 9), (8, 7), (7, 7), (7, 6), (8, 6), (8, 4), (10, 4), (10, 1), (11, 1),
    (11, 2), (15, 2), (15, 0), (6, 0), (6, 2)]

theorem cnGrid_ok : oCeilDB 2 cnGrid = true := by decide

theorem cnGrid_bound : ∀ p ∈ cnGrid, p.1 < 18 ∧ p.2 < 18 := by decide

/-- The vertices of the copy nook in terms of `x_N, u, G, e, H`. -/
def cnPts (xN u G e H : ℚ) : List (ℚ × ℚ) :=
  cnGrid.map fun p => ((cnXs xN u G e).getD p.1 0, (cnYs G e H).getD p.2 0)

section Order

variable {xN u G e H : ℚ}

theorem cnXs_chain (hG : 1 < G) (hGu : G < u) (hu : u < 2) (he : 0 < e) (he' : e < 1 / 100) :
    (cnXs xN u G e).IsChain (· < ·) := by
  have hGe : 0 < G * e := by positivity
  have hGe' : G * e < 2 * e := by nlinarith
  simp only [cnXs, List.isChain_cons_cons, List.isChain_singleton, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem cnYs_chain (hG : 1 < G) (hu : G < 2) (he : 0 < e) (he' : e < 1 / 100) :
    (cnYs G e H).IsChain (· < ·) := by
  have hGe : 0 < G * e := by positivity
  have hGe' : G * e < 2 * e := by nlinarith
  have hGe'' : e < G * e := by nlinarith
  have hee : 0 < e * e := by positivity
  have hee' : e * e < e / 100 := by nlinarith
  simp only [cnYs, List.isChain_cons_cons, List.isChain_singleton, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end Order

theorem strictMonoOn_getD_rat {xs : List ℚ} (h : xs.IsChain (· < ·)) :
    StrictMonoOn (fun i => ((xs.getD i 0 : ℚ) : ℝ)) (Set.Iio xs.length) := by
  intro i hi j hj hij
  simp only [Set.mem_Iio] at hi hj
  show ((xs.getD i 0 : ℚ) : ℝ) < ((xs.getD j 0 : ℚ) : ℝ)
  rw [List.getD_eq_getElem (l := xs) (d := 0) hi, List.getD_eq_getElem (l := xs) (d := 0) hj]
  exact_mod_cast (List.isChain_iff_pairwise.1 h).rel_get_of_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij

/-- **The copy nook in normal form is a dented ceiling feature.** -/
theorem cnPts_ceilD {xN u G e H : ℚ} (hG : 1 < G) (hGu : G < u) (hu : u < 2) (he : 0 < e)
    (he' : e < 1 / 100) {lo hi : ℝ} (hlo : lo < ((xN - u - 3 / 4 : ℚ) : ℝ))
    (hhi : ((xN + 3 * u + 1 / 4 : ℚ) : ℝ) < hi) (hH : 1 ≤ H) :
    CeilFeatureD (2 * (H : ℝ)) lo hi ((cnPts xN u G e H).map ratPoint) ∧
      ∀ q ∈ chainSet ((cnPts xN u G e H).map ratPoint), 0 < q.2 := by
  have hx := cnXs_chain (xN := xN) hG hGu hu he he'
  have hy := cnYs_chain (H := H) hG (hGu.trans hu) he he'
  have hxl : (cnXs xN u G e).length = 18 := rfl
  have hyl : (cnYs G e H).length = 18 := rfl
  have e1 : (cnPts xN u G e H).map ratPoint = cnGrid.map
      (Prod.map (fun i => (((cnXs xN u G e).getD i 0 : ℚ) : ℝ))
        (fun j => (((cnYs G e H).getD j 0 : ℚ) : ℝ))) := by
    simp only [cnPts, List.map_map]; rfl
  have hl : InGrid (Set.Iio (cnXs xN u G e).length) (Set.Iio (cnYs G e H).length) cnGrid := by
    intro p hp
    rw [hxl, hyl]
    exact cnGrid_bound p hp
  have h2 : (((cnYs G e H).getD 2 0 : ℚ) : ℝ) = 2 * (H : ℝ) := by
    simp [cnYs]
  -- the abscissae lie between the first and the last one
  have hxs : ∀ i, i < 18 → xN - u - 3 / 4 ≤ (cnXs xN u G e).getD i 0 ∧
      (cnXs xN u G e).getD i 0 ≤ xN + 3 * u + 1 / 4 := by
    intro i hi
    have hm := strictMonoOn_getD_rat hx
    have h0 : (0 : ℕ) ∈ Set.Iio (cnXs xN u G e).length := by rw [hxl]; decide
    have h17 : (17 : ℕ) ∈ Set.Iio (cnXs xN u G e).length := by rw [hxl]; decide
    have hi' : i ∈ Set.Iio (cnXs xN u G e).length := by rw [hxl]; exact hi
    have a1 := hm.monotoneOn h0 hi' (Nat.zero_le i)
    have a2 := hm.monotoneOn hi' h17 (by omega)
    have c0 : (cnXs xN u G e).getD 0 0 = xN - u - 3 / 4 := rfl
    have c17 : (cnXs xN u G e).getD 17 0 = xN + 3 * u + 1 / 4 := rfl
    rw [c0] at a1; rw [c17] at a2
    exact ⟨by exact_mod_cast a1, by exact_mod_cast a2⟩
  refine ⟨?_, ?_⟩
  · rw [e1, ← h2]
    refine ceilFeatureD_of_mono (strictMonoOn_getD_rat hx) (strictMonoOn_getD_rat hy) hl
      (by rw [hyl]; decide) cnGrid_ok ?_
    intro p hp
    obtain ⟨b1, b2⟩ := hxs p.1 (cnGrid_bound p hp).1
    constructor
    · exact lt_of_lt_of_le hlo (by exact_mod_cast b1)
    · exact lt_of_le_of_lt (by exact_mod_cast b2) hhi
  · -- every ordinate is at least `2H − 1/8 > 0`
    apply chainSet_snd_gt
    intro q hq
    rw [e1] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    have hm := strictMonoOn_getD_rat hy
    have h0 : (0 : ℕ) ∈ Set.Iio (cnYs G e H).length := by rw [hyl]; decide
    have hj : p.2 ∈ Set.Iio (cnYs G e H).length := by rw [hyl]; exact (cnGrid_bound p hp).2
    have a1 := hm.monotoneOn h0 hj (Nat.zero_le _)
    have c0 : (cnYs G e H).getD 0 0 = 2 * H - 1 / 8 := rfl
    simp only [c0] at a1
    have : (0 : ℝ) < ((2 * H - 1 / 8 : ℚ) : ℝ) := by
      have : (0 : ℚ) < 2 * H - 1 / 8 := by linarith
      exact_mod_cast this
    simp only [Prod.map_snd]
    linarith

/-! ### From the definition to the normal form -/

theorem copyNookGen_eq (xN u G e H : ℚ) :
    copyNookGen (xN + u, 2 * H) (xN + G, 2 * H) (xN, 2 * H + 1 + e) (xN, 2 * H + 1 - 5 * e / 4) =
      cnPts xN u G e H := by
  simp only [copyNookGen, aamCanon, cChain, rotL, shiftQ, cnPts, cnGrid, cnXs, cnYs,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_succ,
    List.getD_cons_zero, List.cons.injEq, Prod.mk.injEq]
  and_intros
  all_goals first | trivial | ring

/-- The offset `u = R_m.x − x_N` of the right mouth corner. -/
def nookU (a b : ℚ) (ge : Bool) (H : ℚ) : ℚ := (nookRm a b ge H).1 - nookX a b ge

/-- The offset `G = L_m.x − x_N` of the left mouth corner. -/
def nookG (a b : ℚ) (ge : Bool) (H : ℚ) : ℚ := (nookLm a b ge H).1 - nookX a b ge

theorem copyNookO_eq (a b : ℚ) (ge : Bool) (H : ℚ) :
    copyNookO a b ge H =
      cnPts (nookX a b ge) (nookU a b ge H) (nookG a b ge H) (3 / (2 * H - 3)) H := by
  rw [← copyNookGen_eq]
  have hR : nookRm a b ge H = (nookX a b ge + nookU a b ge H, 2 * H) := by
    unfold nookU; cases ge <;> simp [nookRm, nookPs, nookPt]
  have hL : nookLm a b ge H = (nookX a b ge + nookG a b ge H, 2 * H) := by
    unfold nookG; cases ge <;> simp [nookLm, nookPs, nookPt]
  have hB : nookBotO a b ge H = (nookX a b ge, 2 * H + 1 - 5 * (3 / (2 * H - 3)) / 4) := by
    simp only [nookBotO, nookBot, nookTop]; ext <;> simp only <;> ring
  rw [copyNookO, hR, hL, hB]
  rfl

/-- The mouth offsets: `1 < G < u < 2`. -/
theorem nook_offsets {a b H : ℚ} (hH : 1000 ≤ H) (h1 : H + 30 ≤ b - a) (h2 : b - a ≤ 2 * H - 600)
    (ge : Bool) : 1 < nookG a b ge H ∧ nookG a b ge H < nookU a b ge H ∧ nookU a b ge H < 2 := by
  have hd1 : 0 < 2 * H - 1 := by linarith
  have hd2 : 0 < 2 * H - 2 := by linarith
  have hn1 : 2 * H - 1 ≠ 0 := hd1.ne'
  have hn2 : 2 * H - 2 ≠ 0 := hd2.ne'
  have hn3 : H - 1 ≠ 0 := by intro h; linarith
  cases ge
  · -- type LE: `R_m = P_σ`, `L_m = P_τ`, `e = −16`
    have hu : nookU a b false H = 2 * (b - a + 16) / (2 * H - 1) := by
      simp only [nookU, nookRm, nookPs, nookX, copyE, Bool.false_eq_true, ↓reduceIte]; field_simp; ring
    have hg : nookG a b false H = (2 * (b - a) + 16) / (2 * H - 2) := by
      simp only [nookG, nookLm, nookPt, nookX, copyE, Bool.false_eq_true, ↓reduceIte]; field_simp; ring
    rw [hu, hg]
    refine ⟨?_, ?_, ?_⟩
    · rw [lt_div_iff₀ hd2]; linarith
    · rw [div_lt_div_iff₀ hd2 hd1]; nlinarith
    · rw [div_lt_iff₀ hd1]; linarith
  · -- type GE: `R_m = P_τ`, `L_m = P_σ`, `e = 12`
    have hu : nookU a b true H = (2 * (b - a) - 12) / (2 * H - 2) := by
      simp only [nookU, nookRm, nookPt, nookX, copyE, ↓reduceIte]; field_simp; ring
    have hg : nookG a b true H = 2 * (b - a - 12) / (2 * H - 1) := by
      simp only [nookG, nookLm, nookPs, nookX, copyE, ↓reduceIte]; field_simp; ring
    rw [hu, hg]
    refine ⟨?_, ?_, ?_⟩
    · rw [lt_div_iff₀ hd1]; linarith
    · rw [div_lt_div_iff₀ hd1 hd2]; nlinarith
    · rw [div_lt_iff₀ hd2]; linarith

/-- **The orthogonal copy nook is a dented ceiling feature** of `y = 2H`, inside every strip
containing `[x_N − 3, x_N + 7]`, and lies above `y = 0`. -/
theorem copyNookO_ceilD {a b H : ℚ} (hH : 1000 ≤ H) (h1 : H + 30 ≤ b - a)
    (h2 : b - a ≤ 2 * H - 600) (ge : Bool) {lo hi : ℝ} (hlo : lo < ((nookX a b ge - 3 : ℚ) : ℝ))
    (hhi : ((nookX a b ge + 7 : ℚ) : ℝ) < hi) :
    CeilFeatureD (2 * (H : ℝ)) lo hi ((copyNookO a b ge H).map ratPoint) ∧
      ∀ q ∈ chainSet ((copyNookO a b ge H).map ratPoint), 0 < q.2 := by
  obtain ⟨hG, hGu, hu⟩ := nook_offsets hH h1 h2 ge
  have hd3 : 0 < 2 * H - 3 := by linarith
  have he : 0 < 3 / (2 * H - 3) := by positivity
  have he' : 3 / (2 * H - 3) < 1 / 100 := by rw [div_lt_iff₀ hd3]; linarith
  rw [copyNookO_eq]
  refine cnPts_ceilD hG hGu hu he he' (lt_of_lt_of_le hlo ?_) (lt_of_le_of_lt ?_ hhi)
    (by linarith)
  · exact_mod_cast (show nookX a b ge - 3 ≤ nookX a b ge - nookU a b ge H - 3 / 4 by linarith)
  · exact_mod_cast (show nookX a b ge + 3 * nookU a b ge H + 1 / 4 ≤ nookX a b ge + 7 by linarith)

end

end ArtGallery.Orthogonal.Hard
