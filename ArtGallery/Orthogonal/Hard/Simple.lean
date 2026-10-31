module

public import ArtGallery.Orthogonal.Hard.TemplatesCheck
public import ArtGallery.Orthogonal.Hard.CopyNookSimple
public import ArtGallery.Stade.Simple

/-!
# The orthogonal polygon is simple

**Main result.** `simpleO n Φ : (Polygon.mk ((polyO n Φ).map ratPoint)).Simple`.

`polyO n Φ` is the rectangle `[x_L, x_R] × [−1, 2H]` with dented floor features below `y = 0`
and dented ceiling features above `y = 0` (`simple_of_combsD`).  The templates are features by
`TemplatesCheck.lean`, the copy nooks by `CopyNookSimple.lean`; here we check the abscissa ranges
of the templates (by `decide`), that the features lie strictly between the walls, and that they
are ordered and pairwise separated by vertical lines, using Stade's separation lemmas
`S1`–`S4` (`ArtGallery/Stade/Params.lean`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational Set

/-! ### Abscissa ranges of the templates -/

/-- The smallest element of a list (`0` for the empty list). -/
def lmin : List ℚ → ℚ
  | [] => 0
  | [a] => a
  | a :: l => min a (lmin l)

/-- The largest element of a list (`0` for the empty list). -/
def lmax : List ℚ → ℚ
  | [] => 0
  | [a] => a
  | a :: l => max a (lmax l)

theorem lmin_le : ∀ {l : List ℚ} {x : ℚ}, x ∈ l → lmin l ≤ x
  | [], _, h => by simp at h
  | [a], x, h => by simp at h; subst h; simp [lmin]
  | a :: b :: l, x, h => by
    simp only [lmin]
    rcases List.mem_cons.1 h with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (lmin_le h)

theorem le_lmax : ∀ {l : List ℚ} {x : ℚ}, x ∈ l → x ≤ lmax l
  | [], _, h => by simp at h
  | [a], x, h => by simp at h; subst h; simp [lmax]
  | a :: b :: l, x, h => by
    simp only [lmax]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (le_lmax h).trans (le_max_right _ _)

/-- The local abscissae of a template. -/
def ITmpl.xs (t : ITmpl) : List ℚ := t.pts.map fun p => (p.1 : ℚ) / t.D

/-- The smallest local abscissa of a template. -/
def ITmpl.xmin (t : ITmpl) : ℚ := lmin t.xs

/-- The largest local abscissa of a template. -/
def ITmpl.xmax (t : ITmpl) : ℚ := lmax t.xs

theorem ITmpl.x_mem {t : ITmpl} {p : ℤ × ℤ × ℤ} (hp : p ∈ t.pts) :
    t.xmin ≤ (p.1 : ℚ) / t.D ∧ (p.1 : ℚ) / t.D ≤ t.xmax :=
  ⟨lmin_le (List.mem_map.2 ⟨p, hp, rfl⟩), le_lmax (List.mem_map.2 ⟨p, hp, rfl⟩)⟩

theorem slotFloor_range :
    allKinds.all (fun k => (oSlotFloor k).all fun t => decide (-500 ≤ t.xmin ∧ t.xmax ≤ 600)) =
      true := by decide +kernel

theorem slotFloor_sep :
    allKinds.all (fun k => pairwiseB (fun f g => decide (f.xmax < g.xmin)) (oSlotFloor k)) =
      true := by decide +kernel

theorem varFloor_range : oVarFloor.all (fun t => decide (-1 / 4 ≤ t.xmin ∧ t.xmax ≤ 3)) = true := by
  decide +kernel

theorem varFloor_sep : pairwiseB (fun f g => decide (f.xmax < g.xmin)) oVarFloor = true := by
  decide +kernel

theorem basin_range : 2 ≤ oBasin.xmin ∧ oBasin.xmax ≤ 20 := by decide +kernel

theorem varCeil_range : oVarCeil.all (fun t => decide (-3 ≤ t.xmin ∧ t.xmax ≤ 1 / 4)) = true := by
  decide +kernel

theorem varCeil_sep : pairwiseB (fun f g => decide (g.xmax < f.xmin)) oVarCeil = true := by
  decide +kernel

theorem inputCeil_range :
    ((oInputCeil true).all (fun t => decide (-3 ≤ t.xmin ∧ t.xmax ≤ 1 / 4)) &&
      (oInputCeil false).all (fun t => decide (-1 / 4 ≤ t.xmin ∧ t.xmax ≤ 3))) = true := by
  decide +kernel

theorem inputCeil_sep (pos : Bool) :
    pairwiseB (fun f g => decide (g.xmax < f.xmin)) (oInputCeil pos) = true := by
  cases pos <;> decide +kernel

theorem oTmplInputs_ok :
    allKinds.all (fun k => (oTmplInputs k).all (fun i => decide (30 ≤ i.lx ∧ i.lx ≤ 600)) &&
      pairwiseB (fun i j => decide (i.lx + 44 ≤ j.lx)) (oTmplInputs k)) = true := by
  decide +kernel

/-! ### Unpacking -/

variable {n : ℕ} {Φ : List Constraint}

theorem inputCeil_x {pos : Bool} {t : ITmpl} (ht : t ∈ oInputCeil pos) :
    -3 ≤ t.xmin ∧ t.xmax ≤ 3 := by
  have := inputCeil_range
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  cases pos
  · have := this.2 t ht; constructor <;> linarith [this.1, this.2]
  · have := this.1 t ht; constructor <;> linarith [this.1, this.2]

theorem oTmplInputs_x {k : TKind} {t : TInput} (h : t ∈ oTmplInputs k) :
    30 ≤ t.lx ∧ t.lx ≤ 600 := by
  have := oTmplInputs_ok
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  exact (this k (mem_allKinds k)).1 t h

theorem oTmplInputs_pw (k : TKind) : (oTmplInputs k).Pairwise (fun i j => i.lx + 44 ≤ j.lx) := by
  have := oTmplInputs_ok
  simp only [List.all_eq_true, Bool.and_eq_true] at this
  exact (pairwiseB_sound (this k (mem_allKinds k)).2).imp (fun h => of_decide_eq_true h)

theorem inputsO_b {i : InputSeg} (h : i ∈ inputsO n Φ) :
    ∃ c < paramC Φ, ∃ δ : ℚ, 30 ≤ δ ∧ δ ≤ 600 ∧ i.b = (slotG n Φ c : ℚ) + δ := by
  simp only [inputsO, slotInputsO, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨c, hc, t, ht, rfl⟩ := h
  exact ⟨c, hc, t.lx, (oTmplInputs_x ht).1, (oTmplInputs_x ht).2, rfl⟩

/-- The input abscissae increase with gaps `≥ 44`. -/
theorem inputsO_pw : (inputsO n Φ).Pairwise (fun i j => i.b + 44 ≤ j.b) := by
  unfold inputsO
  rw [List.pairwise_flatMap]
  refine ⟨fun c _ => ?_, ?_⟩
  · unfold slotInputsO
    rw [List.pairwise_map]
    exact (oTmplInputs_pw _).imp (fun h => by simp only; linarith)
  · refine List.pairwise_lt_range.imp (fun {c c'} hcc => ?_)
    intro x hx y hy
    simp only [slotInputsO, List.mem_map] at hx hy
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨t', ht', rfl⟩ := hy
    have := s2_slot (n := n) (Φ := Φ) hcc
    have h1 := oTmplInputs_x ht
    have h2 := oTmplInputs_x ht'
    simp only
    linarith [h1.2, h2.1]

theorem inputO_delta {i : InputSeg} (hi : i ∈ inputsO n Φ) {k : ℕ} (hk : k < n) :
    (paramH n Φ : ℚ) + 30 ≤ i.b - varA Φ k ∧ i.b - varA Φ k ≤ 2 * (paramH n Φ : ℚ) - 600 := by
  obtain ⟨c, hc, δ, hδ0, hδ1, hb⟩ := inputsO_b hi
  rw [hb]
  exact s1 hk hc hδ0 hδ1

theorem inputO_nookX {i : InputSeg} (hi : i ∈ inputsO n Φ) {k : ℕ} (hk : k < n) :
    -2 * (paramH n Φ : ℚ) - 16 ≤ nookX (varA Φ k) i.b i.ge ∧
      nookX (varA Φ k) i.b i.ge ≤ -1200 * (paramC Φ : ℚ) - 18 := by
  obtain ⟨c, hc, δ, hδ0, hδ1, hb⟩ := inputsO_b hi
  unfold nookX
  rw [hb]
  have he := copyE_bounds i.ge
  exact s3_range hk hc hδ0 hδ1 he.1 he.2

theorem inputO_b_bounds {i : InputSeg} (hi : i ∈ inputsO n Φ) :
    (paramX0 n Φ : ℚ) + 30 ≤ i.b ∧ i.b + 700 ≤ xR n Φ := by
  obtain ⟨c, hc, δ, hδ0, hδ1, hb⟩ := inputsO_b hi
  have h1 := slot_lt_xR (n := n) hc
  have h2 : (paramX0 n Φ : ℚ) ≤ slotG n Φ c := by
    have : paramX0 n Φ ≤ slotG n Φ c := by unfold slotG; omega
    exact_mod_cast this
  rw [hb]; constructor <;> linarith

/-! ### Features of templates -/

/-- The abscissae of an instantiated template lie in `[ox + xmin, ox + xmax]`. -/
theorem ITmpl.inst_x {t : ITmpl} {H ox : ℚ} :
    ∀ p ∈ t.inst H ox, ox + t.xmin ≤ p.1 ∧ p.1 ≤ ox + t.xmax := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  have := ITmpl.x_mem hq
  constructor <;> simp only <;> linarith [this.1, this.2]

theorem floorTmpl_feature {t : ITmpl} (ht : t ∈ allFloorTmpls) {H ox : ℚ} (hH : 1000 ≤ H)
    {xlo xhi : ℚ} (hlo : xlo < ox + t.xmin) (hhi : ox + t.xmax < xhi) :
    FloorFeatureD (-1) (xlo : ℝ) (xhi : ℝ) ((t.inst H ox).map ratPoint) ∧
      ∀ q ∈ chainSet ((t.inst H ox).map ratPoint), q.2 < 0 := by
  have hok : floorOK t = true := by
    have := floorTmpls_ok
    simp only [List.all_eq_true] at this
    exact this t ht
  refine floorOK_sound hok hH (fun p hp => ?_)
  have := ITmpl.x_mem hp
  constructor
  · exact_mod_cast (show xlo < ox + (p.1 : ℚ) / t.D by linarith [this.1])
  · exact_mod_cast (show ox + (p.1 : ℚ) / t.D < xhi by linarith [this.2])

theorem ceilTmpl_feature {t : ITmpl} (ht : t ∈ allCeilTmpls) {H ox : ℚ} (hH : 1000 ≤ H)
    {xlo xhi : ℚ} (hlo : xlo < ox + t.xmin) (hhi : ox + t.xmax < xhi) :
    CeilFeatureD (2 * (H : ℝ)) (xlo : ℝ) (xhi : ℝ) ((t.inst H ox).map ratPoint) ∧
      ∀ q ∈ chainSet ((t.inst H ox).map ratPoint), 0 < q.2 := by
  have hok : ceilOK t = true := by
    have := ceilTmpls_ok
    simp only [List.all_eq_true] at this
    exact this t ht
  refine ceilOK_sound hok hH (fun p hp => ?_)
  have := ITmpl.x_mem hp
  constructor
  · exact_mod_cast (show xlo < ox + (p.1 : ℚ) / t.D by linarith [this.1])
  · exact_mod_cast (show ox + (p.1 : ℚ) / t.D < xhi by linarith [this.2])

/-! ### Floor -/

theorem mem_floorFeatsO {f : List (ℚ × ℚ)} (h : f ∈ floorFeatsO n Φ) :
    f = oBasin.inst (paramH n Φ) (xL n Φ) ∨
    (∃ k < n, ∃ t ∈ oVarFloor, f = t.inst (paramH n Φ) (varA Φ k)) ∨
    (∃ c < paramC Φ, ∃ t ∈ oSlotFloor (cKind (gadAt Φ c)),
      f = t.inst (paramH n Φ) (slotG n Φ c)) := by
  simp only [floorFeatsO, List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_range,
    List.mem_map] at h
  rcases h with (rfl | ⟨k, hk, t, ht, rfl⟩) | ⟨c, hc, t, ht, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨k, hk, t, ht, rfl⟩)
  · exact Or.inr (Or.inr ⟨c, hc, t, ht, rfl⟩)

theorem varFloor_x {t : ITmpl} (ht : t ∈ oVarFloor) : -1 / 4 ≤ t.xmin ∧ t.xmax ≤ 3 := by
  have := varFloor_range
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this t ht

theorem slotFloor_x {k : TKind} {t : ITmpl} (ht : t ∈ oSlotFloor k) : -500 ≤ t.xmin ∧ t.xmax ≤ 600 := by
  have := slotFloor_range
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this k (mem_allKinds k) t ht

theorem mem_allFloorTmpls_var {t : ITmpl} (h : t ∈ oVarFloor) : t ∈ allFloorTmpls :=
  List.mem_cons_of_mem _ (List.mem_append_left _ h)

/-- Every floor feature is a dented floor feature of `y = −1` between the walls, below `y = 0`,
and its abscissae lie in a known range. -/
theorem floor_featureO : ∀ f ∈ floorFeatsO n Φ,
    (FloorFeatureD (-1) (xL n Φ : ℝ) (xR n Φ : ℝ) (f.map ratPoint) ∧
      ∀ q ∈ chainSet (f.map ratPoint), q.2 < 0) := by
  intro f hf
  have hH := paramH_ge_q n Φ
  have hxL := xL_neg n Φ
  have hxR := xR_pos n Φ
  rcases mem_floorFeatsO hf with rfl | ⟨k, hk, t, ht, rfl⟩ | ⟨c, hc, t, ht, rfl⟩
  · have := basin_range
    have h0 : (0 : ℚ) ≤ paramX0 n Φ := by positivity
    refine floorTmpl_feature List.mem_cons_self hH (by linarith [this.1]) ?_
    unfold xL xR; linarith [this.2]
  · have hb := varFloor_x ht
    have h1 := var_lt_xR (Φ := Φ) hk
    have h2 := varA_nonneg Φ k
    exact floorTmpl_feature (mem_allFloorTmpls_var ht) hH (by linarith [hb.1]) (by linarith [hb.2])
  · have hb := slotFloor_x ht
    have h1 := slot_lt_xR (n := n) hc
    have h2 := slotG_nonneg n Φ c
    exact floorTmpl_feature (mem_allFloorTmpls_slot ht) hH (by linarith [hb.1])
      (by linarith [hb.2])

theorem floor_lenO {f : List (ℚ × ℚ)} (hf : f ∈ floorFeatsO n Φ) : 2 ≤ f.length := by
  have := (floor_featureO f hf).1.1
  simpa using this

theorem floorRelO_of_bounds {f g : List (ℚ × ℚ)} (hf2 : f ∈ floorFeatsO n Φ)
    (hg2 : g ∈ floorFeatsO n Φ) {U L : ℚ} (hf : ∀ p ∈ f, p.1 ≤ U) (hg : ∀ q ∈ g, L ≤ q.1)
    (hUL : U < L) : FloorRel f g :=
  sep_floor hf hg hUL (floor_lenO hf2) (floor_lenO hg2)

/-- The floor features are pairwise disjoint and ordered from left to right. -/
theorem floor_pwO : (floorFeatsO n Φ).Pairwise FloorRel := by
  have hH := paramH_ge_q n Φ
  have hC : (0 : ℚ) ≤ paramC Φ := by positivity
  refine List.Pairwise.imp_of_mem (R := fun f g => f ∈ floorFeatsO n Φ → g ∈ floorFeatsO n Φ →
    FloorRel f g) (fun ha hb h => h ha hb) ?_
  unfold floorFeatsO
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨List.pairwise_singleton _ _, ?_, ?_⟩, ?_, ?_⟩
  · -- variables
    rw [List.pairwise_flatMap]
    refine ⟨fun k _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      refine (pairwiseB_sound varFloor_sep).imp_of_mem (fun {f g} hfm hgm hfg hf hg => ?_)
      have := of_decide_eq_true hfg
      exact floorRelO_of_bounds hf hg (fun p hp => (ITmpl.inst_x p hp).2)
        (fun q hq => (ITmpl.inst_x q hq).1) (by linarith)
    · refine List.pairwise_lt_range.imp (fun {k k'} hkk => ?_)
      intro f hf g hg hf' hg'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hf
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hg
      have h := s2_var (Φ := Φ) hkk
      have b1 := varFloor_x ht
      have b2 := varFloor_x ht'
      exact floorRelO_of_bounds hf' hg' (fun p hp => (ITmpl.inst_x p hp).2)
        (fun q hq => (ITmpl.inst_x q hq).1) (by linarith [b1.2, b2.1])
  · -- basin vs variables
    intro f hf g hg hf' hg'
    rw [List.mem_singleton] at hf
    subst hf
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hg
    obtain ⟨k, hk, t, ht, rfl⟩ := hg
    have b1 := basin_range
    have b2 := varFloor_x ht
    have h2 := varA_nonneg Φ k
    have hxL := xL_neg n Φ
    exact floorRelO_of_bounds hf' hg' (fun p hp => (ITmpl.inst_x p hp).2)
      (fun q hq => (ITmpl.inst_x q hq).1) (by linarith [b1.2, b2.1])
  · -- slots
    rw [List.pairwise_flatMap]
    refine ⟨fun c _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      have hs := slotFloor_sep
      simp only [List.all_eq_true] at hs
      refine (pairwiseB_sound (hs _ (mem_allKinds _))).imp_of_mem
        (fun {f g} hfm hgm hfg hf hg => ?_)
      have := of_decide_eq_true hfg
      exact floorRelO_of_bounds hf hg (fun p hp => (ITmpl.inst_x p hp).2)
        (fun q hq => (ITmpl.inst_x q hq).1) (by linarith)
    · refine List.pairwise_lt_range.imp (fun {c c'} hcc => ?_)
      intro f hf g hg hf' hg'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hf
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hg
      have := s2_slot (n := n) (Φ := Φ) hcc
      have b1 := slotFloor_x ht
      have b2 := slotFloor_x ht'
      exact floorRelO_of_bounds hf' hg' (fun p hp => (ITmpl.inst_x p hp).2)
        (fun q hq => (ITmpl.inst_x q hq).1) (by linarith [b1.2, b2.1])
  · -- basin and variables vs slots
    intro f hf g hg hf' hg'
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hg
    obtain ⟨c, hc, t', ht', rfl⟩ := hg
    have b2 := slotFloor_x ht'
    rcases List.mem_append.1 hf with hf | hf
    · rw [List.mem_singleton] at hf
      subst hf
      have b1 := basin_range
      have hxL := xL_neg n Φ
      have h0 := slotG_nonneg n Φ c
      exact floorRelO_of_bounds hf' hg' (fun p hp => (ITmpl.inst_x p hp).2)
        (fun q hq => (ITmpl.inst_x q hq).1) (by linarith [b1.2, b2.1])
    · simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hf
      obtain ⟨k, hk, t, ht, rfl⟩ := hf
      have b1 := varFloor_x ht
      have := s2_var_slot (Φ := Φ) (c := c) hk
      exact floorRelO_of_bounds hf' hg' (fun p hp => (ITmpl.inst_x p hp).2)
        (fun q hq => (ITmpl.inst_x q hq).1) (by linarith [b1.2, b2.1])

/-! ### Ceiling -/

theorem mem_ceilFeatsO {f : List (ℚ × ℚ)} (h : f ∈ ceilFeatsO n Φ) :
    (∃ i ∈ inputsO n Φ, ∃ t ∈ oInputCeil i.pos, f = t.inst (paramH n Φ) i.b) ∨
    (∃ k < n, ∃ t ∈ oVarCeil, f = t.inst (paramH n Φ) (varA Φ k)) ∨
    (∃ k < n, ∃ i ∈ inputsO n Φ, f = copyNookO (varA Φ k) i.b i.ge (paramH n Φ)) := by
  simp only [ceilFeatsO, List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range,
    List.mem_map, List.mem_filter, beq_iff_eq] at h
  rcases h with (⟨i, hi, t, ht, rfl⟩ | ⟨k, hk, t, ht, rfl⟩) | ⟨k, hk, i, ⟨hi, -⟩, rfl⟩
  · exact Or.inl ⟨i, hi, t, ht, rfl⟩
  · exact Or.inr (Or.inl ⟨k, hk, t, ht, rfl⟩)
  · exact Or.inr (Or.inr ⟨k, hk, i, hi, rfl⟩)

theorem varCeil_x {t : ITmpl} (ht : t ∈ oVarCeil) : -3 ≤ t.xmin ∧ t.xmax ≤ 1 / 4 := by
  have := varCeil_range
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this t ht

theorem mem_allCeilTmpls_var {t : ITmpl} (h : t ∈ oVarCeil) : t ∈ allCeilTmpls :=
  List.mem_append_left _ (List.mem_append_left _ h)

theorem mem_allCeilTmpls_input {pos : Bool} {t : ITmpl} (h : t ∈ oInputCeil pos) :
    t ∈ allCeilTmpls := by
  cases pos
  · exact List.mem_append_right _ h
  · exact List.mem_append_left _ (List.mem_append_right _ h)

/-- The abscissae of a copy nook lie in `[x_N − 3, x_N + 7]`. -/
theorem copyNookO_x {a b H : ℚ} (hH : 1000 ≤ H) (h1 : H + 30 ≤ b - a) (h2 : b - a ≤ 2 * H - 600)
    (ge : Bool) : ∀ p ∈ copyNookO a b ge H, nookX a b ge - 3 ≤ p.1 ∧ p.1 ≤ nookX a b ge + 7 := by
  obtain ⟨hG, hGu, hu⟩ := nook_offsets hH h1 h2 ge
  have hd3 : 0 < 2 * H - 3 := by linarith
  have he : 0 < 3 / (2 * H - 3) := by positivity
  have he' : 3 / (2 * H - 3) < 1 / 100 := by rw [div_lt_iff₀ hd3]; linarith
  rw [copyNookO_eq]
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  have hx := cnXs_chain (xN := nookX a b ge) hG hGu hu he he'
  have hm := strictMonoOn_getD_rat hx
  have hq' : q.1 ∈ Set.Iio (cnXs (nookX a b ge) (nookU a b ge H) (nookG a b ge H)
      (3 / (2 * H - 3))).length := (cnGrid_bound q hq).1
  have h0 : (0 : ℕ) ∈ Set.Iio (cnXs (nookX a b ge) (nookU a b ge H) (nookG a b ge H)
      (3 / (2 * H - 3))).length := by simp [cnXs]
  have h17 : (17 : ℕ) ∈ Set.Iio (cnXs (nookX a b ge) (nookU a b ge H) (nookG a b ge H)
      (3 / (2 * H - 3))).length := by simp [cnXs]
  have a1 := hm.monotoneOn h0 hq' (Nat.zero_le _)
  have a2 := hm.monotoneOn hq' h17 (by have := (cnGrid_bound q hq).1; omega)
  simp only [Rat.cast_le] at a1 a2
  have c0 : (cnXs (nookX a b ge) (nookU a b ge H) (nookG a b ge H) (3 / (2 * H - 3))).getD 0 0 =
      nookX a b ge - nookU a b ge H - 3 / 4 := rfl
  have c17 : (cnXs (nookX a b ge) (nookU a b ge H) (nookG a b ge H) (3 / (2 * H - 3))).getD 17 0 =
      nookX a b ge + 3 * nookU a b ge H + 1 / 4 := rfl
  rw [c0] at a1; rw [c17] at a2
  constructor <;> simp only <;> linarith

/-- Every ceiling feature is a dented ceiling feature of `y = 2H` between the walls, above
`y = 0`. -/
theorem ceil_featureO : ∀ f ∈ ceilFeatsO n Φ,
    (CeilFeatureD (2 * ((paramH n Φ : ℚ) : ℝ)) (xL n Φ : ℝ) (xR n Φ : ℝ) (f.map ratPoint) ∧
      ∀ q ∈ chainSet (f.map ratPoint), 0 < q.2) := by
  intro f hf
  have hH := paramH_ge_q n Φ
  have hxL := xL_neg n Φ
  have hxR := xR_pos n Φ
  rcases mem_ceilFeatsO hf with ⟨i, hi, t, ht, rfl⟩ | ⟨k, hk, t, ht, rfl⟩ | ⟨k, hk, i, hi, rfl⟩
  · have hb := inputO_b_bounds hi
    have h0 : (0 : ℚ) ≤ paramX0 n Φ := by positivity
    have hx := inputCeil_x ht
    exact ceilTmpl_feature (mem_allCeilTmpls_input ht) hH (by linarith [hx.1])
      (by linarith [hx.2])
  · have h1 := var_lt_xR (Φ := Φ) hk
    have h2 := varA_nonneg Φ k
    have hx := varCeil_x ht
    exact ceilTmpl_feature (mem_allCeilTmpls_var ht) hH (by linarith [hx.1]) (by linarith [hx.2])
  · obtain ⟨h1, h2⟩ := inputO_delta hi hk
    obtain ⟨h3, h4⟩ := inputO_nookX hi hk
    have h5 := s4_xL n Φ
    have h6 : (0 : ℚ) ≤ paramC Φ := by positivity
    exact copyNookO_ceilD hH h1 h2 i.ge (by exact_mod_cast (show xL n Φ < _ by linarith))
      (by exact_mod_cast (show _ < xR n Φ by linarith))

theorem ceil_lenO {f : List (ℚ × ℚ)} (hf : f ∈ ceilFeatsO n Φ) : 2 ≤ f.length := by
  have := (ceil_featureO f hf).1.1
  simpa using this

theorem ceilRelO_of_bounds {f g : List (ℚ × ℚ)} (hf2 : f ∈ ceilFeatsO n Φ)
    (hg2 : g ∈ ceilFeatsO n Φ) {U L : ℚ} (hf : ∀ p ∈ f, L ≤ p.1) (hg : ∀ q ∈ g, q.1 ≤ U)
    (hUL : U < L) : CeilRel f g :=
  sep_ceil hf hg hUL (ceil_lenO hf2) (ceil_lenO hg2)

/-- The ceiling features are pairwise disjoint and ordered from right to left. -/
theorem ceil_pwO : (ceilFeatsO n Φ).Pairwise CeilRel := by
  have hH := paramH_ge_q n Φ
  have hC : (0 : ℚ) ≤ paramC Φ := by positivity
  refine List.Pairwise.imp_of_mem (R := fun f g => f ∈ ceilFeatsO n Φ → g ∈ ceilFeatsO n Φ →
    CeilRel f g) (fun ha hb h => h ha hb) ?_
  unfold ceilFeatsO
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- inputs
    rw [List.pairwise_flatMap]
    refine ⟨fun i _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      refine (pairwiseB_sound (inputCeil_sep i.pos)).imp_of_mem
        (fun {f g} hfm hgm hfg hf hg => ?_)
      have := of_decide_eq_true hfg
      exact ceilRelO_of_bounds hf hg (fun p hp => (ITmpl.inst_x p hp).1)
        (fun q hq => (ITmpl.inst_x q hq).2) (by linarith)
    · rw [List.pairwise_reverse]
      refine inputsO_pw.imp (fun {i j} hij => ?_)
      intro f hf g hg hf' hg'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hf
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hg
      have b1 := inputCeil_x ht
      have b2 := inputCeil_x ht'
      exact ceilRelO_of_bounds hf' hg' (fun p hp => (ITmpl.inst_x p hp).1)
        (fun q hq => (ITmpl.inst_x q hq).2) (by linarith [b1.1, b2.2])
  · -- variables
    rw [List.pairwise_flatMap]
    refine ⟨fun k _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      refine (pairwiseB_sound varCeil_sep).imp_of_mem (fun {f g} hfm hgm hfg hf hg => ?_)
      have := of_decide_eq_true hfg
      exact ceilRelO_of_bounds hf hg (fun p hp => (ITmpl.inst_x p hp).1)
        (fun q hq => (ITmpl.inst_x q hq).2) (by linarith)
    · rw [List.pairwise_reverse]
      refine List.pairwise_lt_range.imp (fun {k k'} hkk => ?_)
      intro f hf g hg hf' hg'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hf
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hg
      have := s2_var (Φ := Φ) hkk
      have b1 := varCeil_x ht
      have b2 := varCeil_x ht'
      exact ceilRelO_of_bounds hf' hg' (fun p hp => (ITmpl.inst_x p hp).1)
        (fun q hq => (ITmpl.inst_x q hq).2) (by linarith [b1.1, b2.2])
  · -- inputs vs variables
    intro f hf g hg hf' hg'
    simp only [List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map] at hf hg
    obtain ⟨i, hi, t, ht, rfl⟩ := hf
    obtain ⟨k, hk, t', ht', rfl⟩ := hg
    have hb := inputO_b_bounds hi
    have hv := s2_var_slot (Φ := Φ) (c := 0) hk
    have : (slotG n Φ 0 : ℚ) = paramX0 n Φ := by simp [slotG]
    have b1 := inputCeil_x ht
    have b2 := varCeil_x ht'
    exact ceilRelO_of_bounds hf' hg' (fun p hp => (ITmpl.inst_x p hp).1)
      (fun q hq => (ITmpl.inst_x q hq).2) (by linarith [b1.1, b2.2])
  · -- copy nooks
    rw [List.pairwise_flatMap]
    refine ⟨fun k hk => ?_, ?_⟩
    · rw [List.mem_reverse, List.mem_range] at hk
      rw [List.pairwise_map]
      refine (inputsO_pw.filter _).imp_of_mem (fun {i j} hi hj hij hf' hg' => ?_)
      simp only [List.mem_filter, beq_iff_eq] at hi hj
      obtain ⟨d1, d2⟩ := inputO_delta hi.1 hk
      obtain ⟨d3, d4⟩ := inputO_delta hj.1 hk
      have hs := s3_same (a := (varA Φ k : ℚ)) hij (copyE_bounds i.ge) (copyE_bounds j.ge)
      exact ceilRelO_of_bounds hf' hg' (L := nookX (varA Φ k) i.b i.ge - 3)
        (U := nookX (varA Φ k) j.b j.ge + 7)
        (fun p hp => (copyNookO_x hH d1 d2 i.ge p hp).1)
        (fun q hq => (copyNookO_x hH d3 d4 j.ge q hq).2)
        (by unfold nookX; linarith)
    · rw [List.pairwise_reverse]
      refine List.pairwise_lt_range.imp_of_mem (fun {k k'} _ hk' hkk => ?_)
      rw [List.mem_range] at hk'
      intro f hf g hg hf' hg'
      simp only [List.mem_map, List.mem_filter, beq_iff_eq] at hf hg
      obtain ⟨j, ⟨hj, -⟩, rfl⟩ := hf
      obtain ⟨i, ⟨hi, -⟩, rfl⟩ := hg
      obtain ⟨d1, d2⟩ := inputO_delta hj hk'
      obtain ⟨d3, d4⟩ := inputO_delta hi (hkk.trans hk')
      obtain ⟨c, hc, δ, hδ0, hδ1, hb⟩ := inputsO_b hi
      obtain ⟨c', hc', δ', hδ0', hδ1', hb'⟩ := inputsO_b hj
      have hs := s3_diff (n := n) (Φ := Φ) (c := c) hkk hc' hδ0 hδ1' (copyE_bounds i.ge)
        (copyE_bounds j.ge)
      exact ceilRelO_of_bounds hf' hg' (L := nookX (varA Φ k') j.b j.ge - 3)
        (U := nookX (varA Φ k) i.b i.ge + 7)
        (fun p hp => (copyNookO_x hH d1 d2 j.ge p hp).1)
        (fun q hq => (copyNookO_x hH d3 d4 i.ge q hq).2)
        (by unfold nookX; rw [hb, hb']; linarith)
  · -- wedges vs copy nooks
    intro f hf g hg hf' hg'
    simp only [List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map,
      List.mem_filter, beq_iff_eq, List.mem_append] at hf hg
    obtain ⟨k, hk, i, ⟨hi, -⟩, rfl⟩ := hg
    obtain ⟨d1, d2⟩ := inputO_delta hi hk
    obtain ⟨h3, h4⟩ := inputO_nookX hi hk
    have hnook : ∀ q ∈ copyNookO (varA Φ k) i.b i.ge (paramH n Φ), q.1 ≤ -11 := by
      intro q hq
      have := (copyNookO_x hH d1 d2 i.ge q hq).2
      linarith
    rcases hf with ⟨j, hj, t, ht, rfl⟩ | ⟨k', hk', t, ht, rfl⟩
    · have hb := inputO_b_bounds hj
      have h0 : (0 : ℚ) ≤ paramX0 n Φ := by positivity
      have b1 := inputCeil_x ht
      exact ceilRelO_of_bounds hf' hg' (L := j.b - 3) (U := -11)
        (fun p hp => by have := (ITmpl.inst_x p hp).1; linarith [b1.1]) hnook (by linarith)
    · have h0 := varA_nonneg Φ k'
      have b1 := varCeil_x ht
      exact ceilRelO_of_bounds hf' hg' (L := (varA Φ k' : ℚ) - 3) (U := -11)
        (fun p hp => by have := (ITmpl.inst_x p hp).1; linarith [b1.1]) hnook (by linarith)

/-! ### The polygon is simple -/

theorem polyO_map (n : ℕ) (Φ : List Constraint) :
    (polyO n Φ).map ratPoint =
      [((xL n Φ : ℝ), (-1 : ℝ))] ++ ((floorFeatsO n Φ).map (List.map ratPoint)).flatten ++
        [((xR n Φ : ℝ), (-1 : ℝ)), ((xR n Φ : ℝ), 2 * ((paramH n Φ : ℚ) : ℝ))] ++
        ((ceilFeatsO n Φ).map (List.map ratPoint)).flatten ++
        [((xL n Φ : ℝ), 2 * ((paramH n Φ : ℚ) : ℝ))] := by
  simp only [polyO, List.map_append, List.map_cons, List.map_nil, List.map_flatten]
  simp [ratPoint]

/-- **The orthogonal polygon is simple.** -/
theorem simpleO (n : ℕ) (Φ : List Constraint) :
    (Polygon.mk ((polyO n Φ).map ratPoint)).Simple := by
  rw [polyO_map]
  have hx : (xL n Φ : ℝ) < xR n Φ := by exact_mod_cast xL_lt_xR n Φ
  have hH : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := by exact_mod_cast paramH_ge_q n Φ
  refine simple_of_combsD (m := 0) hx (by norm_num) (by linarith) _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact (floor_featureO g hg).1
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact (floor_featureO g hg).2
  · rw [List.pairwise_map]; exact floor_pwO
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact (ceil_featureO g hg).1
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact (ceil_featureO g hg).2
  · rw [List.pairwise_map]; exact ceil_pwO

end

end ArtGallery.Orthogonal.Hard
