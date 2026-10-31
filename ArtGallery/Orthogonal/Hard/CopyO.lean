module

public import ArtGallery.Orthogonal.Hard.CopyData
public import ArtGallery.Orthogonal.Hard.CopyRoom
public import ArtGallery.Stade.LowerCopy

/-!
# Copy nooks: exclusion and the copy inequality

For the input `m` of slot `c` (abscissa `b = g_c + δ_m`), copying the variable `k` (abscissa
`a`), with a guard assignment `A`:

* **Exclusion** (`copyO_excl`): a guard seeing a point of Stade's nook segment strictly inside
  the orthogonal nook edge (rows `6`–`12`) is the guard of `k` or of the input:
  - guards left of `x_N` (the nook's own helpers, the basin guard) see nothing of the edge
    (`nook_wall`);
  - other guards are outside the room of the nook (strips), so they see the point through the
    mouth and lie in Stade's partial-visibility region `copyPV`, which contains no other variable
    or input guard (band lemmas), no guard above the ceiling, no helper of a variable or a slot
    below the floor (`copyPV_low`, spot certificates `spot_far`) and no box of a slot
    (`boxPVB`, `copyPV_low_upper'`);
* **The copy inequality** (`copyO_rel`): by Stade's shadow lemmas through the room of the nook.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-- Below the input band down to `y = −140`, the partial-visibility region stays left of
`b + 400`. -/
theorem copyPV_low_upper' {H a b : ℝ} {ge : Bool} (hp : CopyParams H a b) {p : Point}
    (hpv : p ∈ copyPV ge H a b) (hy1 : -140 ≤ p.2) (hy2 : p.2 ≤ 0) : p.1 ≤ b + 400 := by
  have hH := hp.hH; have hlo := hp.hlo; have hhi := hp.hhi
  by_contra hc; push Not at hc
  cases ge
  · obtain ⟨-, h2⟩ := copyLE_PV_poly hp hpv
    have hQ : 0 ≤ (2 * H - 3) * (b - a + 16) := by nlinarith
    have h3 : -p.2 * ((2 * H - 3) * (b - a + 16)) ≤ 140 * ((2 * H - 3) * (b - a + 16)) :=
      mul_le_mul_of_nonneg_right (by linarith) hQ
    have h4 : 0 < (2 * H - 1) * (H - 3) := by nlinarith
    have h5 : 400 * ((2 * H - 1) * (H - 3)) < (p.1 - b) * ((2 * H - 1) * (H - 3)) :=
      mul_lt_mul_of_pos_right (by linarith) h4
    nlinarith
  · obtain ⟨-, h2⟩ := copyGE_PV_poly hp hpv
    have hQ : 0 ≤ (2 * H - 3) * (b - a - 6) := by nlinarith
    have h3 : (6 - p.2) * ((2 * H - 3) * (b - a - 6)) ≤ 146 * ((2 * H - 3) * (b - a - 6)) :=
      mul_le_mul_of_nonneg_right (by linarith) hQ
    have h4 : 0 < (H - 1) * (H - 3) := by nlinarith
    have h5 : 400 * ((H - 1) * (H - 3)) < (p.1 - b) * ((H - 1) * (H - 3)) :=
      mul_lt_mul_of_pos_right (by linarith) h4
    nlinarith

/-- The partial-visibility region lies right of the nook segment. -/
theorem copyPV_right {H a b : ℝ} {ge : Bool} (hp : CopyParams H a b) {p : Point}
    (hpv : p ∈ copyPV ge H a b) : copyXN ge a b < p.1 := by
  obtain ⟨hy, hL, -⟩ := hpv
  have hLR := copyLm_lt_Rm ge hp
  obtain ⟨hxL, -⟩ : copyXN ge a b < (copyLm ge H a b).1 ∧ copyXN ge a b < (copyRm ge H a b).1 := by
    obtain ⟨h1, h2, -, -⟩ := copy_mouth_order ge hp
    cases ge
    · exact ⟨h2, h1⟩
    · exact ⟨h1, h2⟩
  have h3 := hp.pos3
  have he : 0 < 3 / (2 * H - 3) := div_pos (by norm_num) h3
  simp only [det, copyNtop, copyLm_snd] at hL
  by_contra hc; push Not at hc
  nlinarith

/-! ### Grid points of a copy nook and Stade's copy points -/

theorem nook_gpt_Lm (a b : ℚ) (ge : Bool) (H : ℚ) :
    gpt (nookφ a b ge H) (nookψ a b ge H) (16, 3) = copyLm ge (H : ℝ) (a : ℝ) (b : ℝ) := by
  have e1 := nookφ_eq (a := a) (b := b) (H := H) ge (i := 16) (by norm_num)
  have e2 := nookψ_eq (a := a) (b := b) (H := H) ge (j := 3) (by norm_num)
  simp only [gpt]
  rw [e1, e2]
  simp only [cnXe, cnXs, cnYe, cnYs, List.getD_cons_succ, List.getD_cons_zero, List.cons_append]
  cases ge
  · rw [copyLm_false, ← ratPoint_nookPt]
    simp only [ratPoint, nookG, nookLm, Bool.false_eq_true, ↓reduceIte, nookPt]
    push_cast; ext <;> simp only <;> ring
  · rw [copyLm_true, ← ratPoint_nookPs]
    simp only [ratPoint, nookG, nookLm, ↓reduceIte, nookPs]
    push_cast; ext <;> simp only <;> ring

theorem nook_gpt_Rm (a b : ℚ) (ge : Bool) (H : ℚ) :
    gpt (nookφ a b ge H) (nookψ a b ge H) (17, 3) = copyRm ge (H : ℝ) (a : ℝ) (b : ℝ) := by
  have e1 := nookφ_eq (a := a) (b := b) (H := H) ge (i := 17) (by norm_num)
  have e2 := nookψ_eq (a := a) (b := b) (H := H) ge (j := 3) (by norm_num)
  simp only [gpt]
  rw [e1, e2]
  simp only [cnXe, cnXs, cnYe, cnYs, List.getD_cons_succ, List.getD_cons_zero, List.cons_append]
  cases ge
  · rw [copyRm_false, ← ratPoint_nookPs]
    simp only [ratPoint, nookU, nookRm, Bool.false_eq_true, ↓reduceIte, nookPs]
    push_cast; ext <;> simp only <;> ring
  · rw [copyRm_true, ← ratPoint_nookPt]
    simp only [ratPoint, nookU, nookRm, ↓reduceIte, nookPt]
    push_cast; ext <;> simp only <;> ring

theorem nook_φ15 (a b : ℚ) (ge : Bool) (H : ℚ) :
    nookφ a b ge H 15 = copyXN ge (a : ℝ) (b : ℝ) := by
  rw [nookφ_eq ge (by norm_num), ← nookX_cast]
  simp [cnXe, cnXs]

theorem nook_ψ12 (a b : ℚ) (ge : Bool) (H : ℚ) :
    nookψ a b ge H 12 = (copyNtop ge (H : ℝ) (a : ℝ) (b : ℝ)).2 := by
  rw [nookψ_eq ge (by norm_num)]
  simp [cnYe, cnYs, copyNtop]; ring

theorem nook_ψ3 (a b : ℚ) (ge : Bool) (H : ℚ) : nookψ a b ge H 3 = 2 * (H : ℝ) := by
  rw [nookψ_eq ge (by norm_num)]
  simp [cnYe, cnYs]

theorem nook_ψ6_lt {a b H : ℚ} (hH : 1000 ≤ H) (ge : Bool) :
    nookψ a b ge H 6 < (copyNbot ge (H : ℝ) (a : ℝ) (b : ℝ)).2 := by
  rw [nookψ_eq ge (by norm_num)]
  simp only [cnYe, cnYs, List.getD_cons_succ, List.getD_cons_zero, copyNbot]
  have h3 : (0 : ℝ) < 2 * H - 3 := by
    have : (1000 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  have he : (0 : ℝ) < 3 / (2 * H - 3) := div_pos (by norm_num) h3
  have he' : (3 : ℝ) / (2 * H - 3) < 1 / 100 := by
    rw [div_lt_iff₀ h3]
    have : (1000 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  push_cast
  nlinarith

/-! ### The input of a slot and its copy nook -/

variable {n : ℕ} {Φ : List Constraint}

/-- The input segment of input `m` of slot `c`. -/
def slotIn (c : Fin (paramC Φ)) {m : ℕ} (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) :
    InputSeg :=
  ⟨(slotG n Φ c : ℚ) + (oTmplInputs (cKind (gadAt Φ c)))[m].lx, (oTmplInputs (cKind (gadAt Φ c)))[m].pos,
    (cVars (gadAt Φ c)).getD (oTmplInputs (cKind (gadAt Φ c)))[m].role 0,
    (oTmplInputs (cKind (gadAt Φ c)))[m].ge, c, (oTmplInputs (cKind (gadAt Φ c)))[m].role⟩

theorem slotIn_mem (c : Fin (paramC Φ)) {m : ℕ} (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) :
    slotIn (n := n) c hm ∈ inputsO n Φ := by
  unfold inputsO slotInputsO
  exact List.mem_flatMap.2 ⟨c, List.mem_range.2 c.isLt, List.mem_map.2 ⟨_, List.getElem_mem hm, rfl⟩⟩

theorem slotIn_lx (c : Fin (paramC Φ)) {m : ℕ} (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) :
    30 ≤ (oTmplInputs (cKind (gadAt Φ c)))[m].lx ∧ (oTmplInputs (cKind (gadAt Φ c)))[m].lx ≤ 600 :=
  oTmplInputs_x (List.getElem_mem hm)

/-- An even witness index of a slot is the index of an input guard. -/
theorem inIdx_of_even {c : Fin (paramC Φ)} {i : Fin (slotWs (cKind (gadAt Φ c))).length}
    (hev : i.1 % 2 = 0) (hlt : i.1 / 2 < (oTmplInputs (cKind (gadAt Φ c))).length) :
    (.inl (.inr (.inl ⟨c, i⟩)) : CIdx n Φ) = inIdx c hlt := by
  have e : i = ⟨2 * (i.1 / 2), slotIn_lt hlt⟩ := Fin.ext (by simp only; omega)
  unfold inIdx
  rw [Sum.inl.injEq, Sum.inr.injEq, Sum.inl.injEq, Sigma.mk.inj_iff]
  exact ⟨rfl, heq_of_eq e⟩

theorem inIdx_congr {c : Fin (paramC Φ)} {m m' : ℕ} (h : m = m')
    (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length)
    (hm' : m' < (oTmplInputs (cKind (gadAt Φ c))).length) : (inIdx c hm : CIdx n Φ) = inIdx c hm' := by
  subst h; rfl

/-- `g_c ≥ 1000` (there is a variable). -/
theorem slotG_ge {c : ℕ} (hn : 0 < n) : (1000 : ℝ) ≤ slotG n Φ c := by
  have := var_slot_sep (n := n) (Φ := Φ) (k := 0) (c := c) hn
  have h0 : ((varA Φ 0 : ℕ) : ℝ) = 0 := by simp [varA]
  linarith

section Copy

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n) {G : Finset Point} (A : AssignO n Φ G)
  (c : Fin (paramC Φ)) {m : ℕ} (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length)
include hΦ

/-- **Exclusion for a copy nook.** A guard seeing a point of Stade's nook segment strictly inside
the nook edge is the guard of the copied variable or of the input. -/
theorem copyO_excl {s : Point}
    (hsN : s ∈ ArtGallery.segment
      (copyNbot (slotIn (n := n) c hm).ge ((paramH n Φ : ℚ) : ℝ) ((varA Φ (slotIn (n := n) c hm).var : ℚ) : ℝ)
        (((slotIn (n := n) c hm).b : ℚ) : ℝ))
      (copyNtop (slotIn (n := n) c hm).ge ((paramH n Φ : ℚ) : ℝ) ((varA Φ (slotIn (n := n) c hm).var : ℚ) : ℝ)
        (((slotIn (n := n) c hm).b : ℚ) : ℝ)))
    (hs12 : s.2 < (copyNtop (slotIn (n := n) c hm).ge ((paramH n Φ : ℚ) : ℝ)
      ((varA Φ (slotIn (n := n) c hm).var : ℚ) : ℝ) (((slotIn (n := n) c hm).b : ℚ) : ℝ)).2)
    {X : CIdx n Φ} (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    X = varIdx ⟨(slotIn (n := n) c hm).var, inputsO_var hΦ (slotIn_mem c hm)⟩ ∨ X = inIdx c hm := by
  set i := slotIn (n := n) c hm with hi_def
  have hi := slotIn_mem (n := n) c hm
  have hk := inputsO_var hΦ hi
  set k := i.var
  obtain ⟨hφ, hψ, -⟩ := nook_grid hk hi rfl
  obtain ⟨hδ0, hδ1⟩ := slotIn_lx c hm
  have hp : CopyParams ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ) :=
    copyParams_of_input hk c.isLt hδ0 hδ1
  have hH := paramH_ge_q n Φ
  have hHr : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := by exact_mod_cast hH
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hk
  obtain ⟨hs1, hsb, hst⟩ := (copy_nook_iff i.ge hp).1 hsN
  have e15 := nook_φ15 (varA Φ k : ℚ) i.b i.ge (paramH n Φ)
  have e12 := nook_ψ12 (varA Φ k : ℚ) i.b i.ge (paramH n Φ)
  have e3 := nook_ψ3 (varA Φ k : ℚ) i.b i.ge (paramH n Φ)
  have e6 := nook_ψ6_lt (a := (varA Φ k : ℚ)) (b := i.b) hH i.ge
  have hs1' : s.1 = iφ Φ (paramH n Φ) k i 15 := by rw [hs1]; exact e15.symm
  have hs6 : iψ Φ (paramH n Φ) k i 6 < s.2 := lt_of_lt_of_le e6 hsb
  have hs12' : s.2 < iψ Φ (paramH n Φ) k i 12 := by
    show s.2 < nookψ (varA Φ k) i.b i.ge (paramH n Φ) 12; rw [e12]; exact hs12
  -- the nook segment is far left
  have hxN : ((nookX (varA Φ k) i.b i.ge : ℚ) : ℝ) ≤ -18 := by
    have := (inputO_nookX hi hk).2
    have hC : (0 : ℚ) ≤ paramC Φ := by positivity
    exact_mod_cast (by linarith : nookX (varA Φ k) i.b i.ge ≤ -18)
  have hs1x : s.1 = ((nookX (varA Φ k) i.b i.ge : ℚ) : ℝ) := by rw [hs1, nookX_cast]
  -- guards left of the nook edge
  have hleft : ¬ (A.γ X).1 < iφ Φ (paramH n Φ) k i 15 := fun h =>
    nook_wall hk hi rfl hs1' hs6 hs12' h hX
  have hxNφ : iφ Φ (paramH n Φ) k i 15 = ((nookX (varA Φ k) i.b i.ge : ℚ) : ℝ) := by
    rw [← hs1', hs1x]
  -- the point lies in the room
  have hsR : s ∈ nookRoom n Φ k i := by
    have e : s = (iφ Φ (paramH n Φ) k i 15, s.2) := Prod.ext hs1' rfl
    rw [e]
    refine nook_col_room hk hi rfl ?_ ?_
    · show nookψ (varA Φ k) i.b i.ge (paramH n Φ) 3 ≤ s.2
      rw [e3]
      have := copyNbot_snd_gt i.ge hp
      linarith
    · exact (hs12'.le).trans (hψ.monotoneOn (by simp) (by simp) (by norm_num))
  -- the room lies in the strip of the nook
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  have hroom : ∀ y ∈ nookRoom n Φ k i, ((nookX (varA Φ k) i.b i.ge : ℚ) : ℝ) - 3 < y.1 ∧
      y.1 < ((nookX (varA Φ k) i.b i.ge : ℚ) : ℝ) + 7 := by
    intro y hy
    have hb := (nookBox_set (ge := i.ge)).1 (nookRoom_box hk hi rfl hy)
    have hL := nzone_L hH d1 d2 i.ge
    have hR := nzone_R hH d1 d2 i.ge
    push_cast at hL hR ⊢
    constructor <;> linarith [hb.1, hb.2.1]
  -- the index of the input in `inputsO`
  obtain ⟨j, hj, hji⟩ := List.getElem_of_mem hi
  have hjX : jX n Φ ⟨j, hj⟩ = ((nookX (varA Φ k) i.b i.ge : ℚ) : ℝ) := by
    simp only [jX, Fin.getElem_fin, hji] <;> rfl
  -- outside the room: the partial-visibility region
  have hpv_of : (A.γ X) ∉ nookRoom n Φ k i →
      A.γ X ∈ copyPV i.ge ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ) := by
    intro hgR
    obtain ⟨q, hqD, hq⟩ := cross_of_sees_room (nook_room hk hi rfl) hsR hgR hX
    have hL := nook_gpt_Lm (varA Φ k : ℚ) i.b i.ge (paramH n Φ)
    have hR := nook_gpt_Rm (varA Φ k : ℚ) i.b i.ge (paramH n Φ)
    simp only [iφ, iψ] at hqD
    rw [hL, hR] at hqD
    exact mem_copyPV_of_cross i.ge hp hsN hqD (by rw [ArtGallery.Geometry.segment_comm]; exact hq)
  -- a guard of another strip is outside the room
  have hout : (stripO X).2 ≤ ((nookX (varA Φ k) i.b i.ge : ℚ) : ℝ) - 3 ∨
      ((nookX (varA Φ k) i.b i.ge : ℚ) : ℝ) + 7 ≤ (stripO X).1 → A.γ X ∉ nookRoom n Φ k i := by
    intro h hR
    have := hroom _ hR
    have hs := A.strip hΦ X
    rcases h with h | h <;> linarith [this.1, this.2, hs.1, hs.2]
  rcases X with t | ⟨j', b'⟩
  · -- a template guard
    have hgR : A.γ (.inl t) ∉ nookRoom n Φ k i := by
      apply hout
      have := stripO_disj hΦ (X := .inl t) (Y := .inr (⟨j, hj⟩, false))
        (by rcases t with ⟨_, _⟩ | ⟨_, _⟩ | _ <;> simp [grpO, tgrp])
      simp only [stripO] at this ⊢
      rw [hjX] at this
      rcases this with h | h
      · left; linarith
      · right; linarith
    have hpv := hpv_of hgR
    have hPV2 := hpv.1
    have hbG : (1000 : ℝ) + 30 ≤ ((i.b : ℚ) : ℝ) - (slotG n Φ c : ℝ) + 1000 := by
      have : ((i.b : ℚ) : ℝ) = (slotG n Φ c : ℝ) + ((oTmplInputs (cKind (gadAt Φ c)))[m].lx : ℝ) := by
        simp only [hi_def, slotIn]; push_cast; ring
      have : (30 : ℝ) ≤ (oTmplInputs (cKind (gadAt Φ c)))[m].lx := by exact_mod_cast hδ0
      linarith
    have hbx : ((i.b : ℚ) : ℝ) = (slotG n Φ c : ℝ) + ((oTmplInputs (cKind (gadAt Φ c)))[m].lx : ℝ) := by
      simp only [hi_def, slotIn]; push_cast; ring
    have hlx0 : (30 : ℝ) ≤ (oTmplInputs (cKind (gadAt Φ c)))[m].lx := by exact_mod_cast hδ0
    have hlx1 : ((oTmplInputs (cKind (gadAt Φ c)))[m].lx : ℝ) ≤ 600 := by exact_mod_cast hδ1
    have hNb := copyNbot_snd_gt i.ge hp
    rcases t with ⟨k', i'⟩ | ⟨c', i'⟩ | i'
    · -- a variable group
      rcases i' with ⟨_ | _ | _ | i'', hi''⟩
      · -- the variable guard
        left
        have hv := A.varPos k'
        have hb := copyPV_var_band i.ge hp hpv (by simp only [varIdx] at hv; linarith [hv.2.1])
          (by simp only [varIdx] at hv; linarith [hv.2.2])
        simp only [varIdx] at hv
        rw [hv.1] at hb
        have hk' : k'.1 = k := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · have := varA_sep (Φ := Φ) h
            rw [varA_cast, varA_cast] at hb
            linarith [hb.1, hb.2]
          · have := varA_sep (Φ := Φ) h
            rw [varA_cast, varA_cast] at hb
            linarith [hb.1, hb.2]
        simp only [varIdx]
        congr
        exact Fin.ext hk'
      · -- the ceiling helper
        exfalso
        have h := A.tspot (t := .inl (k', ⟨1, hi''⟩)) (by simp [tgrp])
        simp only [tinst, gVarD] at h
        rw [gVarSps_helpers.1] at h
        obtain ⟨-, -, h3, -⟩ := h
        simp only [LR.real, AH.ev] at h3
        have e01 : A.γ (.inl (.inl (k', ⟨0 + 1, hi''⟩))) = A.γ (.inl (.inl (k', ⟨1, hi''⟩))) := rfl
        rw [e01] at hPV2
        have hH' : (1000 : ℝ) ≤ (paramH n Φ : ℝ) := by exact_mod_cast hH
        push_cast at h3 hPV2
        linarith
      · -- the floor helper
        exfalso
        have h := A.tspot (t := .inl (k', ⟨2, hi''⟩)) (by simp [tgrp])
        simp only [tinst, gVarD] at h
        obtain ⟨-, hx1, -, hy1⟩ := h
        obtain ⟨-, ex1, ey12, ey11⟩ := gVarSps_helpers
        simp only [LR.real, AH.ev] at hx1 hy1
        rw [ex1] at hx1
        have hy12 : ((gVarSps.getD 2 LR.dflt).y1.2 : ℝ) ≤ 0 := by exact_mod_cast ey12
        have hy11 : ((gVarSps.getD 2 LR.dflt).y1.1 : ℝ) ≤ 0 := by exact_mod_cast ey11
        have hy : (A.γ (.inl (.inl (k', ⟨2, hi''⟩)))).2 ≤ 0 := by
          have : ((gVarSps.getD 2 LR.dflt).y1.2 : ℝ) * Hr n Φ ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hy12 (by linarith [Hr_ge n Φ])
          linarith
        have hlow := copyPV_low i.ge hp hpv hy
        have := var_slot_sep (n := n) (Φ := Φ) (c := c.1) k'.isLt
        rw [varA_cast] at hx1
        push_cast at hx1
        nlinarith
      · exfalso; rw [gVarWs_len] at hi''; omega
    · -- a slot group
      have hcl := slotClass_ok (cKind (gadAt Φ c'))
      simp only [slotClassB, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
        List.any_eq_true] at hcl
      have hi'L : i'.1 < (slotD (cKind (gadAt Φ c'))).Ws.length := by rw [slotD_Ws]; exact i'.isLt
      have hG' : (1000 : ℝ) ≤ slotG n Φ c' := slotG_ge hn
      rcases hcl i'.1 hi'L with (⟨hev, hlt⟩ | ⟨p, hpm, hpi⟩) | hbox
      · -- an input guard
        have hi'eq : i' = ⟨2 * (i'.1 / 2), slotIn_lt hlt⟩ := Fin.ext (by simp only; omega)
        have hXe : (.inl (.inr (.inl ⟨c', i'⟩)) : CIdx n Φ) = inIdx c' hlt := by
          exact inIdx_of_even hev hlt
        rw [hXe] at hpv ⊢
        have hpos := A.inPos c' hlt
        have hb := copyPV_in_band i.ge hp hpv (by linarith [hpos.2.1]) (by linarith [hpos.2.2])
        rw [hpos.1] at hb
        have hl0 : (30 : ℝ) ≤ (oTmplInputs (cKind (gadAt Φ c')))[i'.1 / 2].lx := by
          exact_mod_cast (slotIn_lx c' hlt).1
        have hl1 : ((oTmplInputs (cKind (gadAt Φ c')))[i'.1 / 2].lx : ℝ) ≤ 600 := by
          exact_mod_cast (slotIn_lx c' hlt).2
        push_cast at hb
        by_cases hcc : c' = c
        · subst hcc
          by_cases hmm : i'.1 / 2 = m
          · right
            exact inIdx_congr hmm hlt hm
          · exfalso
            have hsep := oTmplInputs_sep (cKind (gadAt Φ c'))
            simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hsep
            rcases hsep _ hlt m hm with h | h
            · exact hmm h
            · rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hm] at h
              have h' : (44 : ℝ) ≤ |((oTmplInputs (cKind (gadAt Φ c')))[i'.1 / 2].lx : ℝ) -
                  ((oTmplInputs (cKind (gadAt Φ c')))[m].lx : ℝ)| := by exact_mod_cast h
              rw [hbx] at hb
              rcases le_abs.1 h' with h2 | h2 <;> linarith [hb.1, hb.2]
        · exfalso
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hcc) with h | h
          · have := slotG_sep (n := n) (Φ := Φ) h; rw [hbx] at hb; linarith [hb.1, hb.2]
          · have := slotG_sep (n := n) (Φ := Φ) h; rw [hbx] at hb; linarith [hb.1, hb.2]
      · -- a helper with a spot certificate
        exfalso
        have hsc := slotSCs_ok _ p hpm
        have hsp := A.tspot (t := .inr (.inl ⟨c', i'⟩)) (by simp [tgrp])
        simp only [tinst] at hsp
        rw [← hpi] at hsp
        have hfar : (-10 : ℚ) ≤ (slotG n Φ c' : ℚ) + (slotD (cKind (gadAt Φ c'))).x0 := by
          rw [slotD_x0]
          have : (1000 : ℚ) ≤ slotG n Φ c' := by exact_mod_cast hG'
          linarith
        have := spot_far (slotD_valid _) (by rw [slotD_gs]; exact slotZ_in c'.isLt)
          (by positivity) hfar hsc hsp hX (by simp only [Hr]; linarith)
        linarith
      · -- a box
        exfalso
        simp only [boxPVB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hbox
        obtain ⟨⟨r0, r1, r2, r3, r4, r5⟩, hins⟩ := hbox
        have hsp := A.tspot (t := .inr (.inl ⟨c', i'⟩)) (by simp [tgrp])
        simp only [tinst] at hsp
        obtain ⟨g1, g2, g3, g4⟩ := hsp
        simp only [LR.real, AH.ev] at g1 g2 g3 g4
        rw [r0] at g3; rw [r1] at g4
        set r := (slotD (cKind (gadAt Φ c'))).sps.getD i'.1 LR.dflt
        have r2' : (-140 : ℝ) ≤ r.y0.1 := by exact_mod_cast r2
        have r3' : (r.y1.1 : ℝ) ≤ 0 := by exact_mod_cast r3
        have r4' : (-100 : ℝ) ≤ r.x0 := by exact_mod_cast r4
        have r5' : (r.x1 : ℝ) ≤ 560 := by exact_mod_cast r5
        push_cast at g1 g2 g3 g4
        have hy0 : (A.γ (.inl (.inr (.inl ⟨c', i'⟩)))).2 ≤ 0 := by linarith
        have hlow := copyPV_low i.ge hp hpv hy0
        rcases lt_trichotomy c'.1 c.1 with h | h | h
        · have := slotG_sep (n := n) (Φ := Φ) h; rw [hbx] at hlow; nlinarith
        · have hcc : c' = c := Fin.ext h
          subst hcc
          rcases hins _ (List.getElem_mem hm) with h1 | ⟨hge, h2⟩
          · have h1' : ((r.x1 : ℚ) : ℝ) <
                (((oTmplInputs (cKind (gadAt Φ c')))[m].lx - 14 - 9 / 10 * r.y1.1 : ℚ) : ℝ) := by
              exact_mod_cast h1
            push_cast at h1'
            rw [hbx] at hlow
            nlinarith
          · have h2' : ((r.x1 : ℚ) : ℝ) <
                (((oTmplInputs (cKind (gadAt Φ c')))[m].lx - r.y1.1 : ℚ) : ℝ) := by
              exact_mod_cast h2
            push_cast at h2'
            have hge' : i.ge = false := by simp only [hi_def, slotIn]; exact hge
            have hpv' := hpv
            rw [hge'] at hpv'
            have := copyPV_low_LE hp hpv' hy0
            rw [hbx] at this
            linarith
        · have := slotG_sep (n := n) (Φ := Φ) h
          have hup := copyPV_low_upper' hp hpv (by linarith) hy0
          rw [hbx] at hup
          linarith
    · -- the basin
      exfalso
      apply hleft
      have hs := A.strip hΦ (.inl (.inr (.inr i')))
      simp only [stripO, tstrip] at hs
      obtain ⟨b1, -⟩ := nookX_bounds hΦ hi
      rw [hxNφ]
      have : ((xL n Φ : ℚ) : ℝ) + 100 ≤ ((nookX (varA Φ k) i.b i.ge : ℚ) : ℝ) := b1
      linarith [hs.2]
  · -- a copy-nook guard
    have hpos := A.nookPos hΦ j' b'
    by_cases hjj : (⟨j, hj⟩ : Fin (inputsO n Φ).length) = j'
    · subst hjj
      exfalso
      apply hleft
      rw [hpos]
      simp only [gpt, jφ, Fin.getElem_fin, hji]
      cases b' <;> simp only [nookQ] <;>
        exact hφ (by simp) (by simp) (by norm_num)
    · exfalso
      have hgR : A.γ (.inr (j', b')) ∉ nookRoom n Φ k i := by
        apply hout
        have := stripO_disj hΦ (X := .inr (j', b')) (Y := .inr (⟨j, hj⟩, false))
          (by simp only [grpO, ne_eq, Prod.mk.injEq, true_and]; exact fun h => hjj (Fin.ext h.symm))
        simp only [stripO] at this ⊢
        rw [hjX] at this
        rcases this with h | h
        · left; linarith
        · right; linarith
      have hpv := hpv_of hgR
      have h1 := hpv.1
      rw [hpos] at h1
      simp only [gpt, jψ] at h1
      have hi' : (inputsO n Φ)[j'] ∈ inputsO n Φ := List.getElem_mem j'.isLt
      generalize (inputsO n Φ)[j'] = q at hi' h1
      have hk' := inputsO_var hΦ hi'
      obtain ⟨-, hψ', -⟩ := nook_grid hk' hi' rfl
      have e3' := nook_ψ3 (varA Φ q.var : ℚ) q.b q.ge (paramH n Φ)
      have : iψ Φ (paramH n Φ) q.var q 3 < iψ Φ (paramH n Φ) q.var q (nookQ b').2 := by
        cases b' <;> exact hψ' (by simp) (by simp [nookQ]) (by simp [nookQ])
      simp only [iψ] at this h1
      rw [e3'] at this
      linarith

/-- The value `(y − H + 1)/2` of the guard of the variable copied by input `m` of slot `c`. -/
noncomputable def AssignO.cval : ℝ :=
  ((A.γ (varIdx ⟨(slotIn (n := n) c hm).var, inputsO_var hΦ (slotIn_mem c hm)⟩)).2 - Hr n Φ + 1) / 2

/-- The value `(y + 2)/4` of the guard of input `m` of slot `c`. -/
noncomputable def AssignO.ival : ℝ := ((A.γ (inIdx c hm)).2 + 2) / 4

theorem AssignO.cval_mem : 1 / 2 ≤ A.cval hΦ c hm ∧ A.cval hΦ c hm ≤ 2 := by
  have := A.varPos ⟨(slotIn (n := n) c hm).var, inputsO_var hΦ (slotIn_mem c hm)⟩
  unfold AssignO.cval; constructor <;> linarith [this.2.1, this.2.2]

omit hΦ in
theorem AssignO.ival_mem : 1 / 2 ≤ A.ival c hm ∧ A.ival c hm ≤ 2 := by
  have := A.inPos c hm
  unfold AssignO.ival; constructor <;> linarith [this.2.1, this.2.2]

/-- **Copy nooks: coverage ⇒ copy inequality.** For input `m` of slot `c`: `w ≤ v` (type GE),
`v ≤ w` (type LE). -/
theorem copyO_rel (hG : (Polygon.mk ((polyO n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point)) :
    ((slotIn (n := n) c hm).ge = true → A.ival c hm ≤ A.cval hΦ c hm) ∧
      ((slotIn (n := n) c hm).ge = false → A.cval hΦ c hm ≤ A.ival c hm) := by
  set i := slotIn (n := n) c hm with hi_def
  have hi := slotIn_mem (n := n) c hm
  have hk := inputsO_var hΦ hi
  set k := i.var
  obtain ⟨hφ, hψ, -⟩ := nook_grid hk hi rfl
  obtain ⟨hδ0, hδ1⟩ := slotIn_lx c hm
  have hp : CopyParams ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ) :=
    copyParams_of_input hk c.isLt hδ0 hδ1
  have hH := paramH_ge_q n Φ
  have hHr : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := by exact_mod_cast hH
  set v := A.cval hΦ c hm
  set w := A.ival c hm
  obtain ⟨hv1, hv2⟩ := A.cval_mem hΦ c hm
  obtain ⟨hw1, hw2⟩ := A.ival_mem c hm
  have hvp := A.varPos ⟨k, hk⟩
  have hip := A.inPos c hm
  have eσ : varPt ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) v = A.γ (varIdx ⟨k, hk⟩) := by
    refine Prod.ext hvp.1.symm ?_
    simp only [varPt_snd, v, AssignO.cval, Hr]; ring
  have eτ : inPt ((i.b : ℚ) : ℝ) w = A.γ (inIdx c hm) := by
    refine Prod.ext ?_ ?_
    · rw [hip.1]; simp only [inPt_fst, hi_def, slotIn]; push_cast; ring
    · simp only [inPt_snd, w, AssignO.ival]; ring
  have hR : (Polygon.mk ((polyO n Φ).map ratPoint)).IsRoom (nookRoom n Φ k i)
      (ArtGallery.segment (copyLm i.ge ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ))
        (copyRm i.ge ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ))) := by
    have h := nook_room hk hi rfl
    simp only [iφ, iψ] at h
    rwa [nook_gpt_Lm, nook_gpt_Rm] at h
  have e15 := nook_φ15 (varA Φ k : ℚ) i.b i.ge (paramH n Φ)
  have e12 := nook_ψ12 (varA Φ k : ℚ) i.b i.ge (paramH n Φ)
  have e3 := nook_ψ3 (varA Φ k : ℚ) i.b i.ge (paramH n Φ)
  have e6 := nook_ψ6_lt (a := (varA Φ k : ℚ)) (b := i.b) hH i.ge
  have hNb := copyNbot_snd_gt i.ge hp
  have hNN := copyNbot_lt_Ntop i.ge hp
  have h1215 : nookψ (varA Φ k) i.b i.ge (paramH n Φ) 12 ≤ nookψ (varA Φ k) i.b i.ge (paramH n Φ) 15 :=
    hψ.monotoneOn (by simp) (by simp) (by norm_num)
  have hNR : ArtGallery.segment (copyNbot i.ge ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ))
      (copyNtop i.ge ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ)) ⊆ nookRoom n Φ k i := by
    intro s hs
    obtain ⟨hs1, hsb, hst⟩ := (copy_nook_iff i.ge hp).1 hs
    have e : s = (iφ Φ (paramH n Φ) k i 15, s.2) := Prod.ext (by rw [hs1]; exact e15.symm) rfl
    rw [e]
    refine nook_col_room hk hi rfl ?_ ?_
    · show nookψ (varA Φ k) i.b i.ge (paramH n Φ) 3 ≤ s.2
      rw [e3]; linarith
    · show s.2 ≤ nookψ (varA Φ k) i.b i.ge (paramH n Φ) 15
      rw [← e12] at hst; linarith
  have hlowR : ∀ p : Point, p.2 ≤ Hr n Φ + 6 → p ∉ nookRoom n Φ k i := by
    intro p hp2 hpR
    have := (nookBox_set (ge := i.ge)).1 (nookRoom_box hk hi rfl hpR)
    simp only [Hr] at hp2
    linarith [this.2.2]
  have hσR : varPt ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) v ∉ nookRoom n Φ k i := by
    apply hlowR; simp only [varPt_snd, Hr]; linarith
  have hτR : inPt ((i.b : ℚ) : ℝ) w ∉ nookRoom n Φ k i := by
    apply hlowR; simp only [inPt_snd, Hr]; linarith
  have hcov : ∀ h : ℝ, (copyNbot i.ge ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ)).2 ≤ h →
      h < (copyNtop i.ge ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ)).2 →
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (varPt ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) v)
        (copyXN i.ge ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ), h) ∨
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (inPt ((i.b : ℚ) : ℝ) w)
        (copyXN i.ge ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ), h) := by
    intro h hh1 hh2
    have hsN : ((copyXN i.ge ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ), h) : Point) ∈ ArtGallery.segment
        (copyNbot i.ge ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ))
        (copyNtop i.ge ((paramH n Φ : ℚ) : ℝ) ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ)) :=
      (copy_nook_iff i.ge hp).2 ⟨rfl, hh1, hh2.le⟩
    have hbd : ((copyXN i.ge ((varA Φ k : ℚ) : ℝ) ((i.b : ℚ) : ℝ), h) : Point) ∈
        (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
      rw [← e15]
      refine nook_edge_bd hk hi rfl ?_ ?_
      · exact (e6.trans_le hh1).le
      · show h ≤ nookψ (varA Φ k) i.b i.ge (paramH n Φ) 12
        rw [e12]; exact hh2.le
    obtain ⟨q, hqG, hqs⟩ := hG.2 _ hbd
    obtain ⟨X, rfl⟩ := A.onto q hqG
    rcases copyO_excl hΦ A c hm hsN hh2 hqs with rfl | rfl
    · left; rw [eσ]; exact hqs
    · right; rw [eτ]; exact hqs
  constructor
  · intro hge
    rw [hge] at hR hNR hcov
    refine copyGE_rel_of_shadows hp hv1 hv2 hw1 hw2 (fun h hh1 hh2 => ?_)
    rcases eq_or_lt_of_le hh2 with he | hlt
    · left; rw [he]; exact (copyShadow_mem hp hv1 hv2).2
    · rcases hcov h hh1 hlt with hs | hs
      · left
        exact copyGE_sig_sees hp hR hNR hv1 hv2 hσR ((copy_nook_iff true hp (s := (copyXN true _ _, h))).2 ⟨rfl, hh1, hlt.le⟩) hs
      · right
        exact copyGE_tau_sees hp hR hNR hw1 hw2 hτR ((copy_nook_iff true hp (s := (copyXN true _ _, h))).2 ⟨rfl, hh1, hlt.le⟩) hs
  · intro hge
    rw [hge] at hR hNR hcov
    refine copyLE_rel_of_shadows hp hv1 hv2 hw1 hw2 (fun h hh1 hh2 => ?_)
    rcases eq_or_lt_of_le hh2 with he | hlt
    · right; rw [he]; exact (copyShadow_mem hp hw1 hw2).2
    · rcases hcov h hh1 hlt with hs | hs
      · left
        exact copyLE_sig_sees hp hR hNR hv1 hv2 hσR ((copy_nook_iff false hp (s := (copyXN false _ _, h))).2 ⟨rfl, hh1, hlt.le⟩) hs
      · right
        exact copyLE_tau_sees hp hR hNR hw1 hw2 hτR ((copy_nook_iff false hp (s := (copyXN false _ _, h))).2 ⟨rfl, hh1, hlt.le⟩) hs

end Copy

end

end ArtGallery.Orthogonal.Hard
