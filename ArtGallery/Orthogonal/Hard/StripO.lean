module

public import ArtGallery.Orthogonal.Hard.CertGroup
public import ArtGallery.Orthogonal.Hard.OrientO

/-!
# The region lies in the strip `−5H ≤ y ≤ 3H`

Every vertex of `polyO` satisfies `−5H ≤ y ≤ 3H`: template vertices by a robust check on the
template data (`tmpl_strip`), copy-nook vertices since their ordinates are grid ordinates
`cnYs ∈ [2H − 1/8, 2H + 3(1 + e) + 1/2]`.  Hence so does every point of the region
(`Stade.filled_snd_ge`, `filled_snd_le`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational Set

/-- A template vertex `(x, y₀, d)` satisfies `−5H ≤ y₀/D − (d/D) H ≤ 3H` for all `H ≥ 1000`. -/
def tmplStripB (t : ITmpl) : Bool :=
  t.pts.all fun p =>
    decide ((p.2.2 : ℚ) / t.D ≤ 5 ∧ 0 ≤ (p.2.1 : ℚ) / t.D + (5 - (p.2.2 : ℚ) / t.D) * 1000 ∧
      -3 ≤ (p.2.2 : ℚ) / t.D ∧ 0 ≤ -(p.2.1 : ℚ) / t.D + (3 + (p.2.2 : ℚ) / t.D) * 1000)

theorem tmpl_strip : (allFloorTmpls.all tmplStripB && allCeilTmpls.all tmplStripB) = true := by
  decide +kernel

theorem ITmpl.inst_y {t : ITmpl} (ht : tmplStripB t = true) {H : ℚ} (hH : 1000 ≤ H) (ox : ℚ) :
    ∀ p ∈ t.inst H ox, -5 * H ≤ p.2 ∧ p.2 ≤ 3 * H := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  simp only [tmplStripB, List.all_eq_true, decide_eq_true_eq] at ht
  obtain ⟨h1, h2, h3, h4⟩ := ht q hq
  rw [neg_div] at h4
  have e1 := mul_nonneg (show (0 : ℚ) ≤ 5 - (q.2.2 : ℚ) / t.D by linarith)
    (show (0 : ℚ) ≤ H - 1000 by linarith)
  have e2 := mul_nonneg (show (0 : ℚ) ≤ 3 + (q.2.2 : ℚ) / t.D by linarith)
    (show (0 : ℚ) ≤ H - 1000 by linarith)
  constructor <;> simp only <;> nlinarith

theorem copyNookO_y {a b H : ℚ} (hH : 1000 ≤ H) (h1 : H + 30 ≤ b - a) (h2 : b - a ≤ 2 * H - 600)
    (ge : Bool) : ∀ p ∈ copyNookO a b ge H, 0 ≤ p.2 ∧ p.2 ≤ 3 * H := by
  obtain ⟨hG, hGu, hu⟩ := nook_offsets hH h1 h2 ge
  have hd3 : 0 < 2 * H - 3 := by linarith
  have he : 0 < 3 / (2 * H - 3) := by positivity
  have he' : 3 / (2 * H - 3) < 1 / 100 := by rw [div_lt_iff₀ hd3]; linarith
  rw [copyNookO_eq]
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  have hy := cnYs_chain (H := H) hG (hGu.trans hu) he he'
  have hm := strictMonoOn_getD_rat hy
  have hq' : q.2 ∈ Set.Iio (cnYs (nookG a b ge H) (3 / (2 * H - 3)) H).length :=
    (cnGrid_bound q hq).2
  have h0 : (0 : ℕ) ∈ Set.Iio (cnYs (nookG a b ge H) (3 / (2 * H - 3)) H).length := by simp [cnYs]
  have h17 : (17 : ℕ) ∈ Set.Iio (cnYs (nookG a b ge H) (3 / (2 * H - 3)) H).length := by
    simp [cnYs]
  have a1 := hm.monotoneOn h0 hq' (Nat.zero_le _)
  have a2 := hm.monotoneOn hq' h17 (by have := (cnGrid_bound q hq).2; omega)
  simp only [Rat.cast_le] at a1 a2
  have c0 : (cnYs (nookG a b ge H) (3 / (2 * H - 3)) H).getD 0 0 = 2 * H - 1 / 8 := rfl
  have c17 : (cnYs (nookG a b ge H) (3 / (2 * H - 3)) H).getD 17 0 =
      2 * H + 3 * (1 + 3 / (2 * H - 3)) + 1 / 2 := rfl
  rw [c0] at a1; rw [c17] at a2
  constructor <;> simp only <;> linarith

variable {n : ℕ} {Φ : List Constraint}

theorem polyO_snd : ∀ p ∈ (polyO n Φ).map ratPoint,
    -5 * Hr n Φ ≤ p.2 ∧ p.2 ≤ 3 * Hr n Φ := by
  have hH := paramH_ge_q n Φ
  have hT := tmpl_strip
  simp only [Bool.and_eq_true, List.all_eq_true] at hT
  have key : ∀ q ∈ polyO n Φ, -5 * (paramH n Φ : ℚ) ≤ q.2 ∧ q.2 ≤ 3 * (paramH n Φ : ℚ) := by
    intro q hq
    simp only [polyO, List.mem_append, List.mem_singleton, List.mem_cons, List.mem_flatten,
      List.not_mem_nil, or_false] at hq
    rcases hq with (((rfl | ⟨f, hf, hqf⟩) | (rfl | rfl)) | ⟨f, hf, hqf⟩) | rfl
    · constructor <;> simp only <;> linarith
    · rcases mem_floorFeatsO hf with rfl | ⟨k, -, t, ht, rfl⟩ | ⟨c, -, t, ht, rfl⟩
      · exact ITmpl.inst_y (hT.1 _ List.mem_cons_self) hH _ q hqf
      · exact ITmpl.inst_y (hT.1 _ (mem_allFloorTmpls_var ht)) hH _ q hqf
      · exact ITmpl.inst_y (hT.1 _ (mem_allFloorTmpls_slot ht)) hH _ q hqf
    · constructor <;> simp only <;> linarith
    · constructor <;> simp only <;> linarith
    · rcases mem_ceilFeatsO hf with ⟨i, -, t, ht, rfl⟩ | ⟨k, -, t, ht, rfl⟩ | ⟨k, hk, i, hi, rfl⟩
      · exact ITmpl.inst_y (hT.2 _ (mem_allCeilTmpls_input ht)) hH _ q hqf
      · exact ITmpl.inst_y (hT.2 _ (mem_allCeilTmpls_var ht)) hH _ q hqf
      · obtain ⟨h1, h2⟩ := inputO_delta hi hk
        have := copyNookO_y hH h1 h2 i.ge q hqf
        constructor <;> linarith [this.1, this.2]
    · constructor <;> simp only <;> linarith
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  have := key q hq
  have a1 : ((-5 * (paramH n Φ : ℚ) : ℚ) : ℝ) ≤ ((q.2 : ℚ) : ℝ) := by exact_mod_cast this.1
  have a2 : ((q.2 : ℚ) : ℝ) ≤ ((3 * (paramH n Φ : ℚ) : ℚ) : ℝ) := by exact_mod_cast this.2
  push_cast at a1 a2
  exact ⟨by simpa [ratPoint, Hr] using a1, by simpa [ratPoint, Hr] using a2⟩

/-- **The region lies in the strip `−5H ≤ y ≤ 3H`.** -/
theorem strip_bound (n : ℕ) (Φ : List Constraint) : StripBound n Φ := by
  intro p hp
  have hn : (Polygon.mk ((polyO n Φ).map ratPoint)).n = (polyO n Φ).length := n_map_ratPoint _
  have hv : ∀ j < (Polygon.mk ((polyO n Φ).map ratPoint)).n,
      -5 * Hr n Φ ≤ ((Polygon.mk ((polyO n Φ).map ratPoint)).vtx j).2 ∧
        ((Polygon.mk ((polyO n Φ).map ratPoint)).vtx j).2 ≤ 3 * Hr n Φ := by
    intro j hj
    rw [hn] at hj
    rw [vtx_map_ratPoint]
    have hm : ratPoint ((polyO n Φ).getD j 0) ∈ (polyO n Φ).map ratPoint := by
      rw [List.getD_eq_getElem _ _ hj]
      exact List.mem_map_of_mem (List.getElem_mem hj)
    exact polyO_snd _ hm
  have h1 := filled_snd_ge _ (fun j hj => (hv j hj).1) p hp
  have h2 := filled_snd_le _ (fun j hj => (hv j hj).2) p hp
  simp only [Hr] at h1 h2
  push_cast at h1 h2
  simp only [yMin, yMax, AH.ev, Hr]
  push_cast
  constructor <;> linarith

end

end ArtGallery.Orthogonal.Hard
