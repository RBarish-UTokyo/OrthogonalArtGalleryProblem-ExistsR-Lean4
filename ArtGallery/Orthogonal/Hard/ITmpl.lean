module

public import ArtGallery.Orthogonal.Hard.Comb
public import Mathlib.Data.Prod.Lex

/-!
# Integer templates depending affinely on `H`

A template of the orthogonal construction is a chain of vertices `(x, y₀ − d·H)` translated by an
abscissa `ox`; its data is stored as integer triples `(x, y₀, d)` over a common denominator `D`
(`ITmpl`).  For `H ≥ H₀` the order of the ordinates of a template is the lexicographic order of
the keys `(−d, y₀)`, provided the robust test `lexMonoB H₀` holds.  The orthogonal feature checks
of `ArtGallery/Orthogonal/Hard/Comb.lean` are therefore evaluated once, by `decide`, on integer
keys (`ikey`), and transfer to every `H ≥ H₀` and every translation (`ITmpl.floorD`,
`ITmpl.ceilD`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade.Chain Set

/-- A template: integer triples `(x, y₀, d)` over the common denominator `D`, standing for the
points `(ox + x/D, y₀/D − (d/D)·H)`. -/
structure ITmpl where
  /-- The common denominator. -/
  D : ℕ
  /-- The vertices `(x, y₀, d)`. -/
  pts : List (ℤ × ℤ × ℤ)

/-- The rational vertices of a template for the parameter `H`, translated by `ox`. -/
def ITmpl.inst (H ox : ℚ) (t : ITmpl) : List (ℚ × ℚ) :=
  t.pts.map fun p => (ox + (p.1 : ℚ) / t.D, (p.2.1 : ℚ) / t.D - (p.2.2 : ℚ) / t.D * H)

/-- The order keys of a vertex: `(0, x)` for the abscissa, `(−d, y₀)` for the ordinate. -/
def ikey (p : ℤ × ℤ × ℤ) : (ℤ ×ₗ ℤ) × (ℤ ×ₗ ℤ) := (toLex (0, p.1), toLex (-p.2.2, p.2.1))

/-- The robust order test: whenever `d_q < d_p`, the vertex `q` lies above `p` for every
`H ≥ H₀`. -/
def lexMonoB (H₀ : ℤ) (pts : List (ℤ × ℤ × ℤ)) : Bool :=
  pts.all fun p => pts.all fun q => decide (q.2.2 < p.2.2 → 0 < (q.2.1 - p.2.1) + (p.2.2 - q.2.2) * H₀)

/-- The real abscissa of an abscissa key. -/
noncomputable def keyX (D : ℕ) (ox : ℝ) (k : ℤ ×ₗ ℤ) : ℝ := ox + ((ofLex k).2 : ℝ) / D

/-- The real ordinate of an ordinate key. -/
noncomputable def keyY (D : ℕ) (H : ℝ) (k : ℤ ×ₗ ℤ) : ℝ := (((ofLex k).2 : ℝ) + ((ofLex k).1 : ℝ) * H) / D

theorem keyX_mono {D : ℕ} (hD : 0 < D) (ox : ℝ) :
    StrictMonoOn (keyX D ox) {k | (ofLex k).1 = 0} := by
  intro k hk l hl hkl
  simp only [mem_ofPred_eq] at hk hl
  rcases Prod.Lex.lt_iff.1 hkl with h | ⟨-, h⟩
  · rw [hk, hl] at h; exact absurd h (lt_irrefl 0)
  · unfold keyX
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    have : ((ofLex k).2 : ℝ) < ((ofLex l).2 : ℝ) := by exact_mod_cast h
    have := div_lt_div_of_pos_right this hD'
    linarith

/-- The ordinate keys of a template. -/
def keysY (pts : List (ℤ × ℤ × ℤ)) : Set (ℤ ×ₗ ℤ) := {k | ∃ p ∈ pts, (ikey p).2 = k}

theorem keyY_mono {D : ℕ} (hD : 0 < D) {H₀ : ℤ} {H : ℝ} (hH : (H₀ : ℝ) ≤ H)
    {pts : List (ℤ × ℤ × ℤ)} (hm : lexMonoB H₀ pts = true) :
    StrictMonoOn (keyY D H) (keysY pts) := by
  intro k hk l hl hkl
  obtain ⟨p, hp, rfl⟩ := hk
  obtain ⟨q, hq, rfl⟩ := hl
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  unfold keyY
  apply div_lt_div_of_pos_right _ hD'
  simp only [ikey, ofLex_toLex]
  rcases Prod.Lex.lt_iff.1 hkl with h | ⟨h1, h2⟩
  · simp only [ikey, ofLex_toLex] at h
    simp only [lexMonoB, List.all_eq_true, decide_eq_true_eq] at hm
    have hpq := hm p hp q hq (by omega)
    have hd : (q.2.2 : ℝ) < p.2.2 := by exact_mod_cast (show q.2.2 < p.2.2 by omega)
    have hpq' : (0 : ℝ) < ((q.2.1 : ℝ) - p.2.1) + ((p.2.2 : ℝ) - q.2.2) * H₀ := by
      exact_mod_cast hpq
    have := mul_le_mul_of_nonneg_left hH (sub_nonneg.2 hd.le)
    push_cast
    nlinarith
  · simp only [ikey, ofLex_toLex] at h1 h2
    have h1' : (-(p.2.2 : ℝ)) = -(q.2.2 : ℝ) := by exact_mod_cast h1
    have h2' : (p.2.1 : ℝ) < q.2.1 := by exact_mod_cast h2
    push_cast
    rw [h1']; linarith

theorem ITmpl.inst_eq (t : ITmpl) (hD : 0 < t.D) (H ox : ℚ) :
    (t.inst H ox).map ratPoint =
      (t.pts.map ikey).map (Prod.map (keyX t.D (ox : ℝ)) (keyY t.D (H : ℝ))) := by
  simp only [ITmpl.inst, List.map_map]
  apply List.map_congr_left
  intro p _
  have hD' : (t.D : ℝ) ≠ 0 := by positivity
  simp only [Function.comp, ratPoint, ikey, Prod.map, keyX, keyY, ofLex_toLex]
  push_cast
  refine Prod.ext rfl ?_
  field_simp
  ring

theorem ITmpl.inGrid (t : ITmpl) :
    InGrid {k : ℤ ×ₗ ℤ | (ofLex k).1 = 0} (keysY t.pts) (t.pts.map ikey) := by
  intro k hk
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
  exact ⟨by simp [ikey], ⟨p, hp, rfl⟩⟩

/-- **Template floor features.**  A template passing the checks is a dented floor feature of
the line `y = keyY k₀` for every `H ≥ H₀` and every translation keeping it inside the strip. -/
theorem ITmpl.floorD {t : ITmpl} (hD : 0 < t.D) {H₀ : ℤ} (hm : lexMonoB H₀ t.pts = true)
    {k₀ : ℤ ×ₗ ℤ} (hk₀ : ∃ p ∈ t.pts, (ikey p).2 = k₀) (hck : oFloorDB k₀ (t.pts.map ikey) = true)
    {H ox : ℚ} (hH : (H₀ : ℚ) ≤ H) {xlo xhi : ℝ}
    (hx : ∀ p ∈ t.pts, xlo < (ox : ℝ) + (p.1 : ℝ) / t.D ∧ (ox : ℝ) + (p.1 : ℝ) / t.D < xhi) :
    FloorFeatureD (keyY t.D (H : ℝ) k₀) xlo xhi ((t.inst H ox).map ratPoint) := by
  rw [ITmpl.inst_eq t hD]
  have hH' : ((H₀ : ℚ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  push_cast at hH'
  refine floorFeatureD_of_mono (keyX_mono hD _) (keyY_mono hD hH' hm) t.inGrid hk₀ hck ?_
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  simpa [ikey, keyX] using hx q hq

/-- **Template ceiling features.** -/
theorem ITmpl.ceilD {t : ITmpl} (hD : 0 < t.D) {H₀ : ℤ} (hm : lexMonoB H₀ t.pts = true)
    {k₀ : ℤ ×ₗ ℤ} (hk₀ : ∃ p ∈ t.pts, (ikey p).2 = k₀) (hck : oCeilDB k₀ (t.pts.map ikey) = true)
    {H ox : ℚ} (hH : (H₀ : ℚ) ≤ H) {xlo xhi : ℝ}
    (hx : ∀ p ∈ t.pts, xlo < (ox : ℝ) + (p.1 : ℝ) / t.D ∧ (ox : ℝ) + (p.1 : ℝ) / t.D < xhi) :
    CeilFeatureD (keyY t.D (H : ℝ) k₀) xlo xhi ((t.inst H ox).map ratPoint) := by
  rw [ITmpl.inst_eq t hD]
  have hH' : ((H₀ : ℚ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  push_cast at hH'
  refine ceilFeatureD_of_mono (keyX_mono hD _) (keyY_mono hD hH' hm) t.inGrid hk₀ hck ?_
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  simpa [ikey, keyX] using hx q hq

end

end ArtGallery.Orthogonal.Hard
