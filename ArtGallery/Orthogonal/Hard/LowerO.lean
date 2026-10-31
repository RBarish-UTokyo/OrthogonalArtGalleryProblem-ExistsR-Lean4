module

public import ArtGallery.Orthogonal.Hard.CountO
public import ArtGallery.Orthogonal.Hard.NookCerts

/-!
# The lower bound (a) for the orthogonal polygon

The counting witnesses are those of the template groups (`TIdx`, `CountO.lean`) and two per copy
nook (`nookBW`, `nookCW`, the tips of the upper arm of the AAM helper and of the lower arm of the
chain helper).  The viewers of a copy-nook witness lie in the open box of the nook's zone
(`sees_nookCert`), hence in `x_N − 3 < x < x_N + 7`; the boxes of distinct nooks and the strips of
the template groups are pairwise disjoint (S3, layout), and the two witnesses of one nook are
separated by their certificates (`nook_disj`).  Every boundary guard set has at least `guardsO`
points (`card_le_guardsO`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Variables of the inputs -/

theorem gadAt_mem {c : ℕ} (hc : c < paramC Φ) : gadAt Φ c ∈ Φ ∧ isGad (gadAt Φ c) = true := by
  have hm : gadAt Φ c ∈ gad Φ := by
    unfold gadAt
    rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem hc
  exact List.mem_filter.1 hm

/-- With all variables `< n`, the variable of every input is `< n`. -/
theorem inputsO_var (hΦ : ∀ c ∈ Φ, c.VarsLt n) {i : InputSeg} (hi : i ∈ inputsO n Φ) :
    i.var < n := by
  simp only [inputsO, slotInputsO, List.mem_flatMap, List.mem_range, List.mem_map] at hi
  obtain ⟨c, hc, t, ht, rfl⟩ := hi
  obtain ⟨hm, hg⟩ := gadAt_mem hc
  have hv := hΦ _ hm
  show (cVars (gadAt Φ c)).getD t.role 0 < n
  generalize gadAt Φ c = g at hg hv ht ⊢
  cases g with
  | one x => simp [isGad] at hg
  | invGe x y | invRevLe x y =>
    simp only [Constraint.VarsLt] at hv
    simp only [cKind, oTmplInputs, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp [cVars] <;> omega
  | addLe x y z | addGe x y z =>
    simp only [Constraint.VarsLt] at hv
    simp only [cKind, oTmplInputs, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp [cVars] <;> omega

/-! ### The counting witnesses -/

/-- The counting witnesses: template groups, and two per copy nook (`true`: the AAM helper). -/
abbrev CIdx (n : ℕ) (Φ : List Constraint) : Type :=
  TIdx n Φ ⊕ (Fin (inputsO n Φ).length × Bool)

/-- The certificate of a copy-nook witness. -/
def nookWC : Bool → GCert
  | true => nookBW
  | false => nookCW

/-- The grid point of a copy-nook witness. -/
def nookWP : Bool → ℕ × ℕ
  | true => (4, 18)
  | false => (11, 2)

theorem nookWC_A (b : Bool) : (nookWC b).A = ((nookWP b).1, (nookWP b).1, (nookWP b).2, (nookWP b).2) := by
  cases b <;> rfl

theorem nookWC_ok (b : Bool) : (nookWC b).ok 20 19 nookOr = true := by
  cases b
  · exact nookCW_ok
  · exact nookBW_ok

theorem nookWC_cs (b : Bool) : (nookWC b).cs.map Prod.fst = cnRR := by
  cases b
  · exact nookCW_cs
  · exact nookBW_cs

theorem nookWC_U (b : Bool) : (nookWC b).U = [nookBox] := by cases b <;> rfl

theorem nookWC_C (b : Bool) : (nookWC b).C = none := by cases b <;> rfl

/-- The witness of a copy nook. -/
noncomputable def nwit (j : Fin (inputsO n Φ).length) (b : Bool) : Point :=
  gpt (iφ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j])
    (iψ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j]) (nookWP b)

/-- The counting witness of an index. -/
noncomputable def cwit : CIdx n Φ → Point
  | .inl X => twit X
  | .inr (j, b) => nwit j b

theorem gpt_mem_degenerate (φ ψ : ℕ → ℝ) (p : ℕ × ℕ) :
    gpt φ ψ p ∈ (realR φ ψ (p.1, p.1, p.2, p.2)).set := by
  simp [Rect.set, realR, gpt]

/-- **The viewers of a copy-nook witness** lie in the open box of the nook's zone, and in a
piece of its certificate. -/
theorem nwit_viewer (hΦ : ∀ c ∈ Φ, c.VarsLt n) (j : Fin (inputsO n Φ).length) (b : Bool)
    {p : Point} (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (nwit j b) p) :
    ∃ q ∈ (nookWC b).cs,
      p ∈ (realR (iφ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j])
        (iψ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j]) q.1).set ∧
      p ∈ gcones (iφ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j])
        (iψ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j]) (nwit j b) q.2.2 ∧
      p ∈ nookBox.set (iφ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j])
        (iψ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j]) := by
  have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
  have hk := inputsO_var hΦ hi
  have hw := gpt_mem_degenerate (iφ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j])
    (iψ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j]) (nookWP b)
  rw [← nookWC_A] at hw
  rcases sees_nookCert hk hi rfl (nookWC_ok b) (nookWC_cs b) (nookWC_U b) hw hs with h | ⟨h, -⟩
  · exact h
  · rw [nookWC_C] at h; exact absurd h (by simp [goptCone])

/-- The viewers of a copy-nook witness lie in `x_N − 3 < x < x_N + 7`. -/
theorem nwit_viewer_x (hΦ : ∀ c ∈ Φ, c.VarsLt n) (j : Fin (inputsO n Φ).length) (b : Bool)
    {p : Point} (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (nwit j b) p) :
    ((nookX (varA Φ (inputsO n Φ)[j].var) (inputsO n Φ)[j].b (inputsO n Φ)[j].ge : ℚ) : ℝ) - 3 < p.1 ∧
      p.1 < ((nookX (varA Φ (inputsO n Φ)[j].var) (inputsO n Φ)[j].b (inputsO n Φ)[j].ge : ℚ) : ℝ) + 7 := by
  have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
  have hk := inputsO_var hΦ hi
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  have hH := paramH_ge_q n Φ
  obtain ⟨-, -, -, -, hU⟩ := nwit_viewer hΦ j b hs
  have hb := (nookBox_set (ge := (inputsO n Φ)[j].ge)).1 hU
  have hL := nzone_L hH d1 d2 (inputsO n Φ)[j].ge
  have hR := nzone_R hH d1 d2 (inputsO n Φ)[j].ge
  push_cast at hL hR ⊢
  constructor <;> linarith [hb.1, hb.2.1]

/-! ### Layout of the copy nooks -/

/-- The x-range of the nook of an input lies left of every template strip but the basin's, and
right of the basin's. -/
theorem nookX_bounds (hΦ : ∀ c ∈ Φ, c.VarsLt n) {i : InputSeg} (hi : i ∈ inputsO n Φ) :
    (xL n Φ : ℝ) + 100 ≤ (nookX (varA Φ i.var) i.b i.ge : ℚ) ∧
      ((nookX (varA Φ i.var) i.b i.ge : ℚ) : ℝ) + 100 ≤ 0 := by
  have hk := inputsO_var hΦ hi
  obtain ⟨h3, h4⟩ := inputO_nookX hi hk
  have hH := paramH_ge_q n Φ
  have hx : (xL n Φ : ℚ) = -3 * (paramH n Φ : ℚ) := by simp [xL]
  have hC : (0 : ℚ) ≤ paramC Φ := by positivity
  constructor
  · have : (xL n Φ : ℚ) + 100 ≤ nookX (varA Φ i.var) i.b i.ge := by rw [hx]; linarith
    exact_mod_cast this
  · obtain ⟨c, hc, -⟩ := inputsO_b hi
    have hC1 : (1 : ℚ) ≤ paramC Φ := by exact_mod_cast (show 1 ≤ paramC Φ by omega)
    have : nookX (varA Φ i.var) i.b i.ge + 100 ≤ 0 := by linarith
    exact_mod_cast this

/-- The x-ranges of the nooks of distinct inputs are disjoint (S3). -/
theorem nookX_sep (hΦ : ∀ c ∈ Φ, c.VarsLt n) {j j' : ℕ} (hj : j < (inputsO n Φ).length)
    (hj' : j' < (inputsO n Φ).length) (hjj : j < j') :
    nookX (varA Φ (inputsO n Φ)[j'].var) (inputsO n Φ)[j'].b (inputsO n Φ)[j'].ge + 10 ≤
        nookX (varA Φ (inputsO n Φ)[j].var) (inputsO n Φ)[j].b (inputsO n Φ)[j].ge ∨
      nookX (varA Φ (inputsO n Φ)[j].var) (inputsO n Φ)[j].b (inputsO n Φ)[j].ge + 10 ≤
        nookX (varA Φ (inputsO n Φ)[j'].var) (inputsO n Φ)[j'].b (inputsO n Φ)[j'].ge := by
  set i := (inputsO n Φ)[j]
  set i' := (inputsO n Φ)[j']
  have hi : i ∈ inputsO n Φ := List.getElem_mem hj
  have hi' : i' ∈ inputsO n Φ := List.getElem_mem hj'
  have hb : i.b + 44 ≤ i'.b := List.pairwise_iff_getElem.1 inputsO_pw j j' hj hj' hjj
  have hk := inputsO_var hΦ hi
  have hk' := inputsO_var hΦ hi'
  obtain ⟨c, hc, δ, hδ0, hδ1, hbe⟩ := inputsO_b hi
  obtain ⟨c', hc', δ', hδ0', hδ1', hbe'⟩ := inputsO_b hi'
  have he := copyE_bounds i.ge
  have he' := copyE_bounds i'.ge
  rcases lt_trichotomy i.var i'.var with hv | hv | hv
  · right
    have := s3_diff (n := n) (Φ := Φ) (c := c) hv hc' hδ0 hδ1' he he'
    unfold nookX; rw [hbe, hbe']; linarith
  · left
    have := s3_same (a := (varA Φ i.var : ℚ)) hb he he'
    unfold nookX; rw [← hv]; linarith
  · left
    obtain ⟨c2, hc2, δ2, hδ02, hδ12, hbe2⟩ := inputsO_b hi'
    have := s3_diff (n := n) (Φ := Φ) (c := c') hv hc hδ0' hδ1 he' he
    unfold nookX; rw [hbe, hbe']; linarith

/-! ### Disjointness -/

/-- **No point sees two counting witnesses.** -/
theorem cwit_disjoint (hΦ : ∀ c ∈ Φ, c.VarsLt n) {X Y : CIdx n Φ} (hXY : X ≠ Y) {p : Point}
    (hp : p ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (h1 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (cwit X))
    (h2 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (cwit Y)) : False := by
  -- a template witness against a nook witness
  have tn : ∀ (X : TIdx n Φ) (j : Fin (inputsO n Φ).length) (b : Bool),
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (twit X) →
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (nwit j b) → False := by
    intro X j b s1 s2
    have v2 := nwit_viewer_x hΦ j b (sees_symm s2)
    obtain ⟨b1, b2⟩ := nookX_bounds hΦ (show (inputsO n Φ)[j] ∈ inputsO n Φ from List.getElem_mem j.isLt)
    rcases X with ⟨k, i⟩ | ⟨c, i⟩ | i <;> have v1 := twit_viewer _ (sees_symm s1)
    · simp only [tstrip] at v1
      have : (0 : ℝ) ≤ varA Φ k := by positivity
      linarith [v1.1, v2.2]
    · simp only [tstrip] at v1
      have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _)
        (inputsO_var hΦ (show (inputsO n Φ)[j] ∈ inputsO n Φ from List.getElem_mem j.isLt))
      have := var_slot_sep (n := n) (Φ := Φ) (k := 0) (c := c.1) hn
      have h0 : ((varA Φ 0 : ℕ) : ℝ) = 0 := by simp [varA]
      linarith [v1.1, v2.2]
    · simp only [tstrip] at v1
      linarith [v1.2, v2.1]
  rcases X with X | ⟨j, b⟩ <;> rcases Y with Y | ⟨j', b'⟩
  · exact twit_disjoint (fun h => hXY (by rw [h])) hp h1 h2
  · exact tn X j' b' h1 h2
  · exact tn Y j b h2 h1
  · simp only [cwit] at h1 h2
    by_cases hjj : j = j'
    · subst hjj
      have hbb : b ≠ b' := fun h => hXY (by rw [h])
      obtain ⟨q1, hq1, hp1, hc1, -⟩ := nwit_viewer hΦ j b (sees_symm h1)
      obtain ⟨q2, hq2, hp2, hc2, -⟩ := nwit_viewer hΦ j b' (sees_symm h2)
      have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
      have hk := inputsO_var hΦ hi
      obtain ⟨d1, d2⟩ := inputO_delta hi hk
      have hH := paramH_ge_q n Φ
      have hφ := nookφ_mono hH d1 d2 (inputsO n Φ)[j].ge
      have hψ := nookψ_mono hH d1 d2 (inputsO n Φ)[j].ge
      have hO := nook_sound hH d1 d2 (inputsO n Φ)[j].ge
      have hwf : ∀ b, ∀ q ∈ (nookWC b).cs, q.1.wf 20 19 = true := by
        intro b q hq
        have := nookWC_ok b
        simp only [GCert.ok, Bool.and_eq_true, List.all_eq_true] at this
        exact (this.1.2 q hq).1.1.1
      have hw : ∀ b, nwit j b ∈ (realR (iφ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j])
          (iψ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j]) (nookWC b).A).set := by
        intro b; rw [nookWC_A]; exact gpt_mem_degenerate _ _ _
      cases b <;> cases b'
      · exact hbb rfl
      · exact gdisjB_sound hφ hψ hO nook_disj (hw true) (hw false) hq2 (hwf true q2 hq2) hp2 hc2
          hq1 (hwf false q1 hq1) hp1 hc1
      · exact gdisjB_sound hφ hψ hO nook_disj (hw true) (hw false) hq1 (hwf true q1 hq1) hp1 hc1
          hq2 (hwf false q2 hq2) hp2 hc2
      · exact hbb rfl
    · have v1 := nwit_viewer_x hΦ j b (sees_symm h1)
      have v2 := nwit_viewer_x hΦ j' b' (sees_symm h2)
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjj) with h | h
      · rcases nookX_sep hΦ j.isLt j'.isLt h with s | s
        · have : ((nookX (varA Φ (inputsO n Φ)[j'].var) (inputsO n Φ)[j'].b (inputsO n Φ)[j'].ge : ℚ) : ℝ)
              + 10 ≤ ((nookX (varA Φ (inputsO n Φ)[j].var) (inputsO n Φ)[j].b (inputsO n Φ)[j].ge : ℚ) : ℝ) := by
            exact_mod_cast s
          linarith [v1.1, v2.2]
        · have : ((nookX (varA Φ (inputsO n Φ)[j].var) (inputsO n Φ)[j].b (inputsO n Φ)[j].ge : ℚ) : ℝ)
              + 10 ≤ ((nookX (varA Φ (inputsO n Φ)[j'].var) (inputsO n Φ)[j'].b (inputsO n Φ)[j'].ge : ℚ) : ℝ) := by
            exact_mod_cast s
          linarith [v1.2, v2.1]
      · rcases nookX_sep hΦ j'.isLt j.isLt h with s | s
        · have : ((nookX (varA Φ (inputsO n Φ)[j].var) (inputsO n Φ)[j].b (inputsO n Φ)[j].ge : ℚ) : ℝ)
              + 10 ≤ ((nookX (varA Φ (inputsO n Φ)[j'].var) (inputsO n Φ)[j'].b (inputsO n Φ)[j'].ge : ℚ) : ℝ) := by
            exact_mod_cast s
          linarith [v1.2, v2.1]
        · have : ((nookX (varA Φ (inputsO n Φ)[j'].var) (inputsO n Φ)[j'].b (inputsO n Φ)[j'].ge : ℚ) : ℝ)
              + 10 ≤ ((nookX (varA Φ (inputsO n Φ)[j].var) (inputsO n Φ)[j].b (inputsO n Φ)[j].ge : ℚ) : ℝ) := by
            exact_mod_cast s
          linarith [v1.1, v2.2]

/-! ### Boundary -/

/-- A copy-nook witness is a vertex of the polygon. -/
theorem nwit_boundary (hΦ : ∀ c ∈ Φ, c.VarsLt n) (j : Fin (inputsO n Φ).length) (b : Bool) :
    nwit j b ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
  have hk := inputsO_var hΦ hi
  set i := (inputsO n Φ)[j]
  -- the grid point is a vertex of the copy nook
  have hv : nwit j b ∈ (copyNookO (varA Φ i.var) i.b i.ge (paramH n Φ)).map ratPoint := by
    rw [copyNookO_eq]
    have hg : (((nookWP b).1 - 1, (nookWP b).2 - 1) : ℕ × ℕ) ∈ cnGrid := by
      cases b <;> decide
    refine List.mem_map.2 ⟨_, List.mem_map.2 ⟨_, hg, rfl⟩, ?_⟩
    have e1 := nookφ_eq (a := (varA Φ i.var : ℚ)) (b := i.b) (H := (paramH n Φ : ℚ)) i.ge
      (i := (nookWP b).1) (by cases b <;> decide)
    have e2 := nookψ_eq (a := (varA Φ i.var : ℚ)) (b := i.b) (H := (paramH n Φ : ℚ)) i.ge
      (j := (nookWP b).2) (by cases b <;> decide)
    simp only [nwit, gpt, iφ, iψ, ratPoint]
    rw [e1, e2]
    cases b <;> rfl
  refine mem_vertices_boundary ?_
  show nwit j b ∈ (polyO n Φ).map ratPoint
  obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hv
  rw [← hqe]
  refine List.mem_map_of_mem ?_
  simp only [polyO, ceilFeatsO, List.mem_append, List.mem_flatten, List.mem_flatMap,
    List.mem_map, List.mem_filter, List.mem_reverse, List.mem_range, beq_iff_eq]
  exact Or.inl (Or.inr ⟨_, Or.inr ⟨i.var, hk, i, ⟨hi, rfl⟩, rfl⟩, hq⟩)

theorem cwit_boundary (hΦ : ∀ c ∈ Φ, c.VarsLt n) (X : CIdx n Φ) :
    cwit X ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  rcases X with X | ⟨j, b⟩
  · exact twit_boundary X
  · exact nwit_boundary hΦ j b

/-! ### The guard number and the lower bound -/

/-- **The guard number** of the orthogonal polygon: the counting witnesses of the variables,
the slots and the basin, and two per copy nook. -/
def guardsO (n : ℕ) (Φ : List Constraint) : ℕ :=
  n * gVarWs.length + ((List.range (paramC Φ)).map fun c => (slotWs (cKind (gadAt Φ c))).length).sum +
    gBasinWs.length + 2 * (inputsO n Φ).length

theorem card_CIdx (n : ℕ) (Φ : List Constraint) : Fintype.card (CIdx n Φ) = guardsO n Φ := by
  simp only [CIdx, TIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_sigma, guardsO]
  rw [Fin.sum_univ_eq_sum_range (fun c => (slotWs (cKind (gadAt Φ c))).length),
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  ring

/-- **Lower bound (a)**: every boundary guard set of the orthogonal polygon has at least
`guardsO n Φ` points. -/
theorem card_le_guardsO (hΦ : ∀ c ∈ Φ, c.VarsLt n) (G : Finset Point)
    (hG : (Polygon.mk ((polyO n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point)) :
    guardsO n Φ ≤ G.card := by
  rw [← card_CIdx]
  exact card_le_of_boundaryGuardSet G hG cwit (cwit_boundary hΦ)
    (fun X Y hXY p hp h1 h2 => cwit_disjoint hΦ hXY hp h1 h2)

end

end ArtGallery.Orthogonal.Hard
