module

public import ArtGallery.Orthogonal.Hard.TemplatesData

/-!
# Orthogonal construction: checked facts about the templates

Every floor template is a dented floor feature of `y = −1` lying below `y = 0`, and every
ceiling template is a dented ceiling feature of `y = 2H` lying above `y = 0`, for every `H ≥ 1000`
and every translation keeping it inside the strip (`floorOK_sound`, `ceilOK_sound`).  The
Boolean checks are evaluated once by `decide +kernel` on the integer data (`floorTmpls_ok`,
`ceilTmpls_ok`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade ArtGallery.Stade.Chain

/-- The floor template check: positive denominator, robust order of the ordinates for
`H ≥ 1000`, a vertex on the floor `y = −1`, the dented floor feature check, all vertices below
`y = 0`. -/
def floorOK (t : ITmpl) : Bool :=
  decide (0 < t.D) && lexMonoB 1000 t.pts && t.pts.any (fun p => decide (p.2 = (-(t.D : ℤ), 0))) &&
  oFloorDB (toLex ((0 : ℤ), -(t.D : ℤ))) (t.pts.map ikey) &&
  t.pts.all (fun p => decide (0 ≤ p.2.2 ∧ p.2.1 < 0))

/-- The ceiling template check: as `floorOK`, for the ceiling `y = 2H` (key `(2D, 0)`), all
vertices above `y = 0`. -/
def ceilOK (t : ITmpl) : Bool :=
  decide (0 < t.D) && lexMonoB 1000 t.pts &&
  t.pts.any (fun p => decide (p.2 = (0, -2 * (t.D : ℤ)))) &&
  oCeilDB (toLex (2 * (t.D : ℤ), (0 : ℤ))) (t.pts.map ikey) &&
  t.pts.all (fun p => decide (p.2.2 ≤ 0 ∧ 0 < p.2.1 - p.2.2 * 1000))

/-- All floor templates. -/
def allFloorTmpls : List ITmpl :=
  oBasin :: oVarFloor ++ allKinds.flatMap oSlotFloor

/-- All ceiling templates. -/
def allCeilTmpls : List ITmpl :=
  oVarCeil ++ oInputCeil true ++ oInputCeil false

/-! ### The checks in parts

A kernel evaluation keeps its intermediate results for the whole declaration; the checks of the
large templates are split into ranges of rows (`lexRow`) and of chain positions (`chainRow`),
proved as separate declarations. -/

/-- `p i` for `a ≤ i < b`. -/
def rangeAll (p : ℕ → Bool) (a b : ℕ) : Bool := (List.range' a (b - a)).all p

theorem rangeAll_join {p : ℕ → Bool} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : rangeAll p a b = true) (h2 : rangeAll p b c = true) : rangeAll p a c = true := by
  unfold rangeAll at *
  rw [List.all_eq_true] at *
  intro k hk
  rw [List.mem_range'_1] at hk
  by_cases hkb : k < b
  · exact h1 k (List.mem_range'_1.2 ⟨hk.1, by omega⟩)
  · exact h2 k (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem rangeAll_get {p : ℕ → Bool} {n : ℕ} (h : rangeAll p 0 n = true) {k : ℕ} (hk : k < n) :
    p k = true :=
  List.all_eq_true.1 h k (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)

/-- Row `i` of the robust order test. -/
def lexRow (H₀ : ℤ) (pts : List (ℤ × ℤ × ℤ)) (i : ℕ) : Bool :=
  match pts.drop i with
  | p :: _ => pts.all fun q => decide (q.2.2 < p.2.2 → 0 < (q.2.1 - p.2.1) + (p.2.2 - q.2.2) * H₀)
  | [] => true

theorem lexMonoB_of_rows {H₀ : ℤ} {pts : List (ℤ × ℤ × ℤ)}
    (h : rangeAll (lexRow H₀ pts) 0 pts.length = true) : lexMonoB H₀ pts = true := by
  unfold lexMonoB
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have := rangeAll_get h hi
  unfold lexRow at this
  rwa [List.drop_eq_getElem_cons hi] at this

/-- Position `i` of the simplicity check of an orthogonal chain. -/
def chainRow {α : Type*} [LinearOrder α] (ch : List (α × α)) (i : ℕ) : Bool :=
  match ch.drop i with
  | a :: b :: l => axisB a b && oFirstOK a b l
  | _ => true

theorem oChainB_of_rows {α : Type*} [LinearOrder α] :
    ∀ (ch : List (α × α)), (∀ i < ch.length, chainRow ch i = true) → oChainB ch = true
  | [], _ => by simp [oChainB]
  | [_], _ => by simp [oChainB]
  | a :: b :: l, h => by
    have h0 := h 0 (by simp)
    simp only [chainRow, List.drop_zero, Bool.and_eq_true] at h0
    have ih := oChainB_of_rows (b :: l) fun i hi => by
      have := h (i + 1) (by simp at hi ⊢; omega)
      simpa [chainRow] using this
    simp only [oChainB, h0.1, h0.2, ih, Bool.and_self]

/-- The conditions of `floorOK` other than the order test and the chain simplicity. -/
def floorRest (t : ITmpl) : Bool :=
  decide (0 < t.D) && t.pts.any (fun p => decide (p.2 = (-(t.D : ℤ), 0))) &&
  decide (3 ≤ (t.pts.map ikey).length) && endsB (toLex ((0 : ℤ), -(t.D : ℤ))) (t.pts.map ikey) &&
  spanB (toLex ((0 : ℤ), -(t.D : ℤ))) (t.pts.map ikey) &&
  t.pts.all (fun p => decide (0 ≤ p.2.2 ∧ p.2.1 < 0))

theorem floorOK_of_parts {t : ITmpl} (h0 : floorRest t = true)
    (h1 : rangeAll (lexRow 1000 t.pts) 0 t.pts.length = true)
    (h2 : rangeAll (chainRow (t.pts.map ikey)) 0 (t.pts.map ikey).length = true) :
    floorOK t = true := by
  simp only [floorRest, Bool.and_eq_true] at h0
  obtain ⟨⟨⟨⟨⟨hD, hany⟩, hlen⟩, hends⟩, hspan⟩, hall⟩ := h0
  have hc : oChainB (t.pts.map ikey) = true :=
    oChainB_of_rows _ fun i hi => rangeAll_get h2 hi
  simp only [floorOK, oFloorDB, hD, lexMonoB_of_rows h1, hany, hlen, hc, hends, hspan, hall,
    Bool.and_self]

/-- The default template. -/
def ITmpl.dflt : ITmpl := ⟨1, []⟩

theorem all_of_getD {α : Type*} {l : List α} {p : α → Bool} (d : α) {n : ℕ} (hn : l.length = n)
    (h : ∀ i < n, p (l.getD i d) = true) : l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := h i (by omega)
  rwa [List.getD_eq_getElem _ _ hi] at this

theorem floorTmpls_len : allFloorTmpls.length = 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem floorTmpls_ok0 : (List.range 8).all (fun i => floorOK (allFloorTmpls.getD i ITmpl.dflt)) =
    true := by decide +kernel

theorem floorTmpl_rest8 : floorRest (allFloorTmpls.getD 8 ITmpl.dflt) = true := by decide +kernel
theorem floorTmpl_rest9 : floorRest (allFloorTmpls.getD 9 ITmpl.dflt) = true := by decide +kernel
theorem floorTmpl_len8 : (allFloorTmpls.getD 8 ITmpl.dflt).pts.length = 232 := by decide +kernel
theorem floorTmpl_len9 : (allFloorTmpls.getD 9 ITmpl.dflt).pts.length = 232 := by decide +kernel
theorem floorTmpl_lex8_0 : rangeAll (lexRow 1000 (allFloorTmpls.getD 8 ITmpl.dflt).pts) 0 58 = true := by
  decide +kernel
theorem floorTmpl_chain8_0 : rangeAll (chainRow ((allFloorTmpls.getD 8 ITmpl.dflt).pts.map ikey)) 0 58 =
    true := by decide +kernel
theorem floorTmpl_lex8_58 : rangeAll (lexRow 1000 (allFloorTmpls.getD 8 ITmpl.dflt).pts) 58 116 = true := by
  decide +kernel
theorem floorTmpl_chain8_58 : rangeAll (chainRow ((allFloorTmpls.getD 8 ITmpl.dflt).pts.map ikey)) 58 116 =
    true := by decide +kernel
theorem floorTmpl_lex8_116 : rangeAll (lexRow 1000 (allFloorTmpls.getD 8 ITmpl.dflt).pts) 116 174 = true := by
  decide +kernel
theorem floorTmpl_chain8_116 : rangeAll (chainRow ((allFloorTmpls.getD 8 ITmpl.dflt).pts.map ikey)) 116 174 =
    true := by decide +kernel
theorem floorTmpl_lex8_174 : rangeAll (lexRow 1000 (allFloorTmpls.getD 8 ITmpl.dflt).pts) 174 232 = true := by
  decide +kernel
theorem floorTmpl_chain8_174 : rangeAll (chainRow ((allFloorTmpls.getD 8 ITmpl.dflt).pts.map ikey)) 174 232 =
    true := by decide +kernel
theorem floorTmpl_lex9_0 : rangeAll (lexRow 1000 (allFloorTmpls.getD 9 ITmpl.dflt).pts) 0 58 = true := by
  decide +kernel
theorem floorTmpl_chain9_0 : rangeAll (chainRow ((allFloorTmpls.getD 9 ITmpl.dflt).pts.map ikey)) 0 58 =
    true := by decide +kernel
theorem floorTmpl_lex9_58 : rangeAll (lexRow 1000 (allFloorTmpls.getD 9 ITmpl.dflt).pts) 58 116 = true := by
  decide +kernel
theorem floorTmpl_chain9_58 : rangeAll (chainRow ((allFloorTmpls.getD 9 ITmpl.dflt).pts.map ikey)) 58 116 =
    true := by decide +kernel
theorem floorTmpl_lex9_116 : rangeAll (lexRow 1000 (allFloorTmpls.getD 9 ITmpl.dflt).pts) 116 174 = true := by
  decide +kernel
theorem floorTmpl_chain9_116 : rangeAll (chainRow ((allFloorTmpls.getD 9 ITmpl.dflt).pts.map ikey)) 116 174 =
    true := by decide +kernel
theorem floorTmpl_lex9_174 : rangeAll (lexRow 1000 (allFloorTmpls.getD 9 ITmpl.dflt).pts) 174 232 = true := by
  decide +kernel
theorem floorTmpl_chain9_174 : rangeAll (chainRow ((allFloorTmpls.getD 9 ITmpl.dflt).pts.map ikey)) 174 232 =
    true := by decide +kernel

theorem floorTmpl_ok8 : floorOK (allFloorTmpls.getD 8 ITmpl.dflt) = true :=
  floorOK_of_parts floorTmpl_rest8 (floorTmpl_len8 ▸ (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) floorTmpl_lex8_0 floorTmpl_lex8_58) floorTmpl_lex8_116) floorTmpl_lex8_174))
    (by rw [List.length_map, floorTmpl_len8]; exact (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) floorTmpl_chain8_0 floorTmpl_chain8_58) floorTmpl_chain8_116) floorTmpl_chain8_174))

theorem floorTmpl_ok9 : floorOK (allFloorTmpls.getD 9 ITmpl.dflt) = true :=
  floorOK_of_parts floorTmpl_rest9 (floorTmpl_len9 ▸ (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) floorTmpl_lex9_0 floorTmpl_lex9_58) floorTmpl_lex9_116) floorTmpl_lex9_174))
    (by rw [List.length_map, floorTmpl_len9]; exact (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) (rangeAll_join (by norm_num) (by norm_num) floorTmpl_chain9_0 floorTmpl_chain9_58) floorTmpl_chain9_116) floorTmpl_chain9_174))

theorem floorTmpls_ok : allFloorTmpls.all floorOK = true := by
  refine all_of_getD ITmpl.dflt floorTmpls_len fun i hi => ?_
  rcases Nat.lt_or_ge i 8 with h | h
  · exact List.all_eq_true.1 floorTmpls_ok0 i (List.mem_range.2 h)
  · rcases (show i = 8 ∨ i = 9 by omega) with rfl | rfl
    · exact floorTmpl_ok8
    · exact floorTmpl_ok9

theorem ceilTmpls_ok : allCeilTmpls.all ceilOK = true := by decide +kernel

theorem mem_allFloorTmpls_slot {k : TKind} {t : ITmpl} (h : t ∈ oSlotFloor k) :
    t ∈ allFloorTmpls :=
  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, mem_allKinds k, h⟩))

/-- The real points of a template. -/
abbrev ITmpl.pts' (H ox : ℚ) (t : ITmpl) : List Point := (t.inst H ox).map ratPoint

theorem ITmpl.mem_pts' {H ox : ℚ} {t : ITmpl} {q : Point} (hq : q ∈ t.pts' H ox) :
    ∃ p ∈ t.pts, q = ((ox : ℝ) + (p.1 : ℝ) / t.D,
      (p.2.1 : ℝ) / t.D - (p.2.2 : ℝ) / t.D * (H : ℝ)) := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
  exact ⟨p, hp, by simp [ratPoint]⟩

/-- **Floor templates.** -/
theorem floorOK_sound {t : ITmpl} (h : floorOK t = true) {H ox : ℚ} (hH : 1000 ≤ H)
    {xlo xhi : ℝ}
    (hx : ∀ p ∈ t.pts, xlo < (ox : ℝ) + (p.1 : ℝ) / t.D ∧ (ox : ℝ) + (p.1 : ℝ) / t.D < xhi) :
    FloorFeatureD (-1) xlo xhi (t.pts' H ox) ∧ ∀ q ∈ chainSet (t.pts' H ox), q.2 < 0 := by
  simp only [floorOK, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hD, hm⟩, ⟨p₀, hp₀, hp₀'⟩⟩, hck⟩, hbel⟩ := h
  have hD' : (0 : ℝ) < t.D := by exact_mod_cast hD
  have hk : keyY t.D (H : ℝ) (toLex ((0 : ℤ), -(t.D : ℤ))) = -1 := by
    simp only [keyY, ofLex_toLex]; push_cast; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [← hk]
    exact ITmpl.floorD hD (H₀ := 1000) hm ⟨p₀, hp₀, by simp [ikey, hp₀']⟩ hck
      (by exact_mod_cast hH) hx
  · apply chainSet_snd_lt
    intro q hq
    obtain ⟨p, hp, rfl⟩ := ITmpl.mem_pts' hq
    obtain ⟨hd, hy⟩ := hbel p hp
    have hd' : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hd
    have hy' : (p.2.1 : ℝ) < 0 := by exact_mod_cast hy
    have hH' : (0 : ℝ) ≤ H := by have : (0 : ℚ) ≤ H := by linarith
                                 exact_mod_cast this
    simp only
    have h1 : (p.2.1 : ℝ) / t.D < 0 := div_neg_of_neg_of_pos hy' hD'
    have h2 : 0 ≤ (p.2.2 : ℝ) / t.D * H := mul_nonneg (div_nonneg hd' hD'.le) hH'
    linarith

/-- **Ceiling templates.** -/
theorem ceilOK_sound {t : ITmpl} (h : ceilOK t = true) {H ox : ℚ} (hH : 1000 ≤ H)
    {xlo xhi : ℝ}
    (hx : ∀ p ∈ t.pts, xlo < (ox : ℝ) + (p.1 : ℝ) / t.D ∧ (ox : ℝ) + (p.1 : ℝ) / t.D < xhi) :
    CeilFeatureD (2 * (H : ℝ)) xlo xhi (t.pts' H ox) ∧ ∀ q ∈ chainSet (t.pts' H ox), 0 < q.2 := by
  simp only [ceilOK, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hD, hm⟩, ⟨p₀, hp₀, hp₀'⟩⟩, hck⟩, habv⟩ := h
  have hD' : (0 : ℝ) < t.D := by exact_mod_cast hD
  have hk : keyY t.D (H : ℝ) (toLex (2 * (t.D : ℤ), (0 : ℤ))) = 2 * (H : ℝ) := by
    simp only [keyY, ofLex_toLex]; push_cast; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [← hk]
    exact ITmpl.ceilD hD (H₀ := 1000) hm ⟨p₀, hp₀, by simp [ikey, hp₀']⟩ hck
      (by exact_mod_cast hH) hx
  · apply chainSet_snd_gt
    intro q hq
    obtain ⟨p, hp, rfl⟩ := ITmpl.mem_pts' hq
    obtain ⟨hd, hy⟩ := habv p hp
    have hd' : (p.2.2 : ℝ) ≤ 0 := by exact_mod_cast hd
    have hy' : (0 : ℝ) < p.2.1 - p.2.2 * 1000 := by exact_mod_cast hy
    have hH' : (1000 : ℝ) ≤ H := by exact_mod_cast hH
    simp only
    have : (0 : ℝ) < (p.2.1 : ℝ) - p.2.2 * H := by nlinarith
    rw [show (p.2.1 : ℝ) / t.D - (p.2.2 : ℝ) / t.D * H = ((p.2.1 : ℝ) - p.2.2 * H) / t.D by
      field_simp]
    exact div_pos this hD'

end

end ArtGallery.Orthogonal.Hard
