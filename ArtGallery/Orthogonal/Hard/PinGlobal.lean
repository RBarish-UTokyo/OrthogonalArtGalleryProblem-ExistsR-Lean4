module

public import ArtGallery.Orthogonal.Hard.GroupsD
public import ArtGallery.Orthogonal.Hard.NookPins

/-!
# Guard positions (global pinning)

For a boundary guard set `G` of cardinality `guardsO n Φ`, every guard `q ∈ G` seeing the
counting witness of an index `X` sees all pin targets `WO X` of `X` (`pinnedO`): the two-stage
argument `Stade.pinned_of_covers` with the order `rO` (indices of one group instance, by rank).

* Pin targets: for a template index, its counting witness and the pin sets of its pins
  (`GData.W`); for a copy-nook index, its counting witness and the three other arm tips of its
  helper.
* Exclusion inside a template group instance: `GData.excl`, using the spots of earlier witnesses
  (`GData.spot`).  Inside a copy nook: the pins of the chain helper are separated from the AAM
  witness by the grid certificates; the pins of the AAM helper are not seen from the point of
  the chain helper (`nook_unseen`).  Across group instances: the viewers lie in disjoint strips.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Template indices -/

/-- The group data, the frame origin and the witness of a template index. -/
def tinst : TIdx n Φ → GData × ℚ × ℕ
  | .inl (k, i) => (gVarD, (varA Φ k : ℚ), i.1)
  | .inr (.inl ⟨c, i⟩) => (slotD (cKind (gadAt Φ c)), (slotG n Φ c : ℚ), i.1)
  | .inr (.inr i) => (gBasinD, xL n Φ, i.1)

/-- The group instance of a template index. -/
def tgrp : TIdx n Φ → ℕ × ℕ
  | .inl (k, _) => (0, k.1)
  | .inr (.inl ⟨c, _⟩) => (1, c.1)
  | .inr (.inr _) => (2, 0)

theorem tinst_valid (t : TIdx n Φ) : (tinst t).1.Valid := by
  rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i
  · exact gVarD_valid
  · exact slotD_valid _
  · exact gBasinD_valid

theorem tinst_in (t : TIdx n Φ) : ∀ g ∈ (tinst t).1.gs, g.InPoly n Φ (tinst t).2.1 := by
  rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i
  · exact varZ_in k.isLt
  · simp only [tinst]; rw [slotD_gs]; exact slotZ_in c.isLt
  · exact basinZ_in

theorem tinst_vtx (t : TIdx n Φ) : (tinst t).1.Ws.all (vtxB (tinst t).1.gs) = true := by
  rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i
  · exact gVarD_vtx
  · exact slotD_vtx _
  · exact gBasinD_vtx

theorem tinst_lt (t : TIdx n Φ) : (tinst t).2.2 < (tinst t).1.Ws.length := by
  rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i
  · exact i.isLt
  · simp only [tinst]; rw [slotD_Ws]; exact i.isLt
  · exact i.isLt

theorem twit_eq (t : TIdx n Φ) :
    twit t = ((tinst t).1.Ws.getD (tinst t).2.2 WCert.dflt).a.real ((tinst t).2.1 : ℝ) (Hr n Φ) := by
  rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i
  · show _ = (gVarWs.getD i.1 WCert.dflt).a.real (((varA Φ k : ℚ)) : ℝ) (Hr n Φ)
    rw [List.getD_eq_getElem _ _ i.isLt]
    simp only [twit]; push_cast; rfl
  · simp only [twit, tinst]
    rw [List.getD_eq_getElem _ _ (by rw [slotD_Ws]; exact i.isLt)]
    have e : (slotD (cKind (gadAt Φ c))).Ws = slotWs (cKind (gadAt Φ c)) := slotD_Ws _
    simp only [e]; push_cast; rfl
  · show _ = (gBasinWs.getD i.1 WCert.dflt).a.real ((xL n Φ : ℚ) : ℝ) (Hr n Φ)
    rw [List.getD_eq_getElem _ _ i.isLt]
    simp only [twit]; rfl

/-- Two template indices of the same group instance have the same data, and distinct witnesses
if they are distinct. -/
theorem tgrp_eq {t t' : TIdx n Φ} (h : tgrp t = tgrp t') :
    (tinst t).1 = (tinst t').1 ∧ (tinst t).2.1 = (tinst t').2.1 ∧
      (t ≠ t' → (tinst t).2.2 ≠ (tinst t').2.2) := by
  rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i <;> rcases t' with ⟨k', i'⟩ | ⟨c', i'⟩ | i' <;>
    simp only [tgrp, Prod.mk.injEq] at h <;> (try (exfalso; omega))
  · have hk : k = k' := Fin.ext h.2
    subst hk
    refine ⟨rfl, rfl, fun hne he => hne ?_⟩
    rw [Fin.ext he]
  · have hc : c = c' := Fin.ext h.2
    subst hc
    refine ⟨rfl, rfl, fun hne he => hne ?_⟩
    rw [Fin.ext he]
  · refine ⟨rfl, rfl, fun hne he => hne ?_⟩
    rw [Fin.ext he]

/-- The strip of a template index. -/
noncomputable def tstripO (t : TIdx n Φ) : ℝ × ℝ :=
  (((tinst t).2.1 : ℝ) + (tinst t).1.x0, ((tinst t).2.1 : ℝ) + (tinst t).1.x1)

theorem tstripO_eq (t : TIdx n Φ) : tstripO t = tstrip t := by
  rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i
  · simp only [tstripO, tinst, tstrip, gVarD]; push_cast; ring_nf
  · simp only [tstripO, tinst, tstrip, slotD_x0, slotD_x1]; push_cast; ring_nf
  · simp only [tstripO, tinst, tstrip, gBasinD]; push_cast; ring_nf

/-- Distinct template group instances have disjoint strips. -/
theorem tstrip_disj {t t' : TIdx n Φ} (h : tgrp t ≠ tgrp t') :
    (tstrip t).2 ≤ (tstrip t').1 ∨ (tstrip t').2 ≤ (tstrip t).1 := by
  rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i <;> rcases t' with ⟨k', i'⟩ | ⟨c', i'⟩ | i' <;>
    simp only [tstrip, tgrp, ne_eq, Prod.mk.injEq, not_and, true_and, not_true_eq_false,
      forall_const] at h ⊢
  · rcases lt_or_gt_of_ne h with h | h
    · left; have := varA_sep (Φ := Φ) h; linarith
    · right; have := varA_sep (Φ := Φ) h; linarith
  · left; have := var_slot_sep (n := n) (Φ := Φ) (c := c'.1) k.isLt; linarith
  · right; have := xL_var_sep (n := n) (Φ := Φ) k.1; linarith
  · right; have := var_slot_sep (n := n) (Φ := Φ) (c := c.1) k'.isLt; linarith
  · rcases lt_or_gt_of_ne h with h | h
    · left; have := slotG_sep (n := n) (Φ := Φ) h; linarith
    · right; have := slotG_sep (n := n) (Φ := Φ) h; linarith
  · right; have := xL_slot_sep (n := n) (Φ := Φ) c.1; linarith
  · left; have := xL_var_sep (n := n) (Φ := Φ) k'.1; linarith
  · left; have := xL_slot_sep (n := n) (Φ := Φ) c'.1; linarith

/-! ### Copy-nook indices -/

/-- The pin certificates of a copy-nook helper (`true`: the AAM helper). -/
def nookPins : Bool → List GCert
  | true => [nookPB0, nookPB1, nookPB2]
  | false => [nookPC0, nookPC1, nookPC2]

theorem nookPins_facts (b : Bool) : ∀ c ∈ nookPins b, c.ok 20 19 nookOr = true ∧
    c.cs.map Prod.fst = cnRR ∧ c.U = [nookBox] ∧ c.C = none ∧
    ∃ m < 46, c.A = ((cnG1.getD m (0, 0)).1, (cnG1.getD m (0, 0)).1, (cnG1.getD m (0, 0)).2,
      (cnG1.getD m (0, 0)).2) := by
  cases b <;> simp only [nookPins, List.mem_cons, List.not_mem_nil, or_false] <;>
    rintro c (rfl | rfl | rfl)
  · exact ⟨nookPC0_ok, nookPC0_cs, rfl, rfl, 24, by decide, rfl⟩
  · exact ⟨nookPC1_ok, nookPC1_cs, rfl, rfl, 34, by decide, rfl⟩
  · exact ⟨nookPC2_ok, nookPC2_cs, rfl, rfl, 29, by decide, rfl⟩
  · exact ⟨nookPB0_ok, nookPB0_cs, rfl, rfl, 3, by decide, rfl⟩
  · exact ⟨nookPB1_ok, nookPB1_cs, rfl, rfl, 13, by decide, rfl⟩
  · exact ⟨nookPB2_ok, nookPB2_cs, rfl, rfl, 18, by decide, rfl⟩

/-- The grid abscissae of the copy nook of input `j`. -/
noncomputable abbrev jφ (n : ℕ) (Φ : List Constraint) (j : Fin (inputsO n Φ).length) : ℕ → ℝ :=
  iφ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j]

/-- The grid ordinates of the copy nook of input `j`. -/
noncomputable abbrev jψ (n : ℕ) (Φ : List Constraint) (j : Fin (inputsO n Φ).length) : ℕ → ℝ :=
  iψ Φ (paramH n Φ) (inputsO n Φ)[j].var (inputsO n Φ)[j]

/-- The pin targets of a copy-nook index. -/
noncomputable def nookW (j : Fin (inputsO n Φ).length) (b : Bool) : Set Point :=
  {nwit j b} ∪ {w | ∃ c ∈ nookPins b, w = gpt (jφ n Φ j) (jψ n Φ j) (c.A.1, c.A.2.2.1)}

/-- The point of a copy-nook helper. -/
def nookQ : Bool → ℕ × ℕ
  | true => (4, 15)
  | false => (11, 8)

/-- The x-coordinate of the copy nook of input `j`. -/
noncomputable def jX (n : ℕ) (Φ : List Constraint) (j : Fin (inputsO n Φ).length) : ℝ :=
  ((nookX (varA Φ (inputsO n Φ)[j].var) (inputsO n Φ)[j].b (inputsO n Φ)[j].ge : ℚ) : ℝ)

section NookIdx

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n)
include hΦ

theorem nookW_bd (j : Fin (inputsO n Φ).length) (b : Bool) {w : Point} (hw : w ∈ nookW j b) :
    w ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
  have hk := inputsO_var hΦ hi
  rcases hw with hw | ⟨c, hc, rfl⟩
  · rw [mem_singleton_iff] at hw; subst hw; exact nwit_boundary hΦ j b
  · obtain ⟨-, -, -, -, m, hm, hA⟩ := nookPins_facts b c hc
    rw [hA]
    exact nook_vtx_boundary hk hi rfl hm

theorem nookW_viewer (j : Fin (inputsO n Φ).length) (b : Bool) {w p : Point} (hw : w ∈ nookW j b)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p) :
    jX n Φ j - 3 < p.1 ∧ p.1 < jX n Φ j + 7 := by
  have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
  have hk := inputsO_var hΦ hi
  rcases hw with hw | ⟨c, hc, rfl⟩
  · rw [mem_singleton_iff] at hw; subst hw; exact nwit_viewer_x hΦ j b hs
  · obtain ⟨hok, hcs, hU, hC, m, hm, hA⟩ := nookPins_facts b c hc
    refine nook_viewer_x hk hi rfl hok hcs hU hC ?_ hs
    rw [hA]; simp only [Rect.set, realR, gpt, mem_ofPred_eq]; exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

end NookIdx

/-! ### The global data -/

/-- The pin targets of an index. -/
noncomputable def WO : CIdx n Φ → Set Point
  | .inl t => (tinst t).1.W (tinst t).2.1 (Hr n Φ) (tinst t).2.2
  | .inr (j, b) => nookW j b

/-- The group instance of an index. -/
def grpO : CIdx n Φ → ℕ × ℕ
  | .inl t => tgrp t
  | .inr (j, _) => (3, j.1)

/-- The rank of an index in its group instance. -/
def rkO : CIdx n Φ → ℕ
  | .inl t => (tinst t).1.rks.getD (tinst t).2.2 0
  | .inr (_, b) => if b then 1 else 0

/-- The pinning order: earlier indices of the same group instance. -/
def rO (Y X : CIdx n Φ) : Prop := grpO Y = grpO X ∧ rkO Y < rkO X

theorem rO_wf : WellFounded (rO (n := n) (Φ := Φ)) :=
  Subrelation.wf (fun h => h.2) (InvImage.wf rkO wellFounded_lt)

/-- The strip of an index. -/
noncomputable def stripO : CIdx n Φ → ℝ × ℝ
  | .inl t => tstrip t
  | .inr (j, _) => (jX n Φ j - 3, jX n Φ j + 7)

theorem cwit_mem_WO (X : CIdx n Φ) : cwit X ∈ WO X := by
  rcases X with t | ⟨j, b⟩
  · left; rw [mem_singleton_iff]; exact twit_eq t
  · left; rfl

theorem WO_bd (hΦ : ∀ c ∈ Φ, c.VarsLt n) (X : CIdx n Φ) {w : Point} (hw : w ∈ WO X) :
    w ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  rcases X with t | ⟨j, b⟩
  · exact GData.W_bd (tinst_valid t) (tinst_in t) (tinst_vtx t) (tinst_lt t) hw
  · exact nookW_bd hΦ j b hw

theorem WO_viewer (hΦ : ∀ c ∈ Φ, c.VarsLt n) (X : CIdx n Φ) {w p : Point} (hw : w ∈ WO X)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p) :
    (stripO X).1 < p.1 ∧ p.1 < (stripO X).2 := by
  rcases X with t | ⟨j, b⟩
  · have := GData.W_viewer (tinst_valid t) (tinst_in t) (tinst_lt t) hw hs
    have e := tstripO_eq t
    simp only [tstripO, Prod.ext_iff] at e
    simp only [stripO]
    rw [← e.1, ← e.2]; exact this
  · exact nookW_viewer hΦ j b hw hs

/-- Distinct group instances have disjoint strips. -/
theorem stripO_disj (hΦ : ∀ c ∈ Φ, c.VarsLt n) {X Y : CIdx n Φ} (h : grpO X ≠ grpO Y) :
    (stripO X).2 ≤ (stripO Y).1 ∨ (stripO Y).2 ≤ (stripO X).1 := by
  -- a template strip against a nook strip
  have tn : ∀ (t : TIdx n Φ) (j : Fin (inputsO n Φ).length),
      (jX n Φ j + 7 ≤ (tstrip t).1) ∨ (tstrip t).2 ≤ jX n Φ j - 3 := by
    intro t j
    obtain ⟨b1, b2⟩ := nookX_bounds hΦ (show (inputsO n Φ)[j] ∈ inputsO n Φ from List.getElem_mem j.isLt)
    simp only [jX]
    rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i <;> simp only [tstrip]
    · left
      have : (0 : ℝ) ≤ varA Φ k := by positivity
      linarith
    · left
      have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _)
        (inputsO_var hΦ (show (inputsO n Φ)[j] ∈ inputsO n Φ from List.getElem_mem j.isLt))
      have := var_slot_sep (n := n) (Φ := Φ) (k := 0) (c := c.1) hn
      have h0 : ((varA Φ 0 : ℕ) : ℝ) = 0 := by simp [varA]
      linarith
    · right; linarith
  rcases X with t | ⟨j, b⟩ <;> rcases Y with t' | ⟨j', b'⟩
  · exact tstrip_disj h
  · rcases tn t j' with h' | h'
    · right; exact h'
    · left; exact h'
  · rcases tn t' j with h' | h'
    · left; exact h'
    · right; exact h'
  · simp only [grpO, ne_eq, Prod.mk.injEq, true_and] at h
    simp only [stripO]
    have hX : ∀ (a : Fin (inputsO n Φ).length) (b : Fin (inputsO n Φ).length), a.1 < b.1 →
        jX n Φ b + 7 ≤ jX n Φ a - 3 ∨ jX n Φ a + 7 ≤ jX n Φ b - 3 := by
      intro a b hab
      rcases nookX_sep hΦ a.isLt b.isLt hab with s | s
      · left
        have : jX n Φ b + 10 ≤ jX n Φ a := by simp only [jX]; exact_mod_cast s
        linarith
      · right
        have : jX n Φ a + 10 ≤ jX n Φ b := by simp only [jX]; exact_mod_cast s
        linarith
    rcases lt_or_gt_of_ne h with h' | h'
    · rcases hX j j' h' with s | s
      · right; exact s
      · left; exact s
    · rcases hX j' j h' with s | s
      · left; exact s
      · right; exact s

/-! ### Exclusion in a copy nook -/

theorem nookPins_true_unseen : ∀ c ∈ nookPins true, gptUnseenB nookOr c (11, 8) = true := by
  simp only [nookPins, List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl)
  · exact nookPB0_unseen
  · exact nookPB1_unseen
  · exact nookPB2_unseen

theorem nookPins_false_disj : ∀ c ∈ nookPins false, gdisjB nookOr 4 c nookBW = true := by
  simp only [nookPins, List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl)
  · exact nookPC0_disj
  · exact nookPC1_disj
  · exact nookPC2_disj

section NookExcl

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n)
include hΦ

/-- **The point of the chain helper.** A point seeing the four arm tips of the chain helper is
its point. -/
theorem nook_spot_false (j : Fin (inputsO n Φ).length) {p : Point}
    (hall : ∀ w ∈ nookW j false, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p w) :
    p = gpt (jφ n Φ j) (jψ n Φ j) (nookQ false) := by
  have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
  have hk := inputsO_var hΦ hi
  refine nook_helper_spot hk hi rfl nookQC_0 nookQC_1 nookQC_2 nookQC_3 ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro m (rfl | rfl | rfl | rfl)
  · rw [nookTC_0]; exact hall _ (Or.inr ⟨nookPC2, by simp [nookPins], rfl⟩)
  · rw [nookTC_1]; exact hall _ (Or.inl rfl)
  · rw [nookTC_2]; exact hall _ (Or.inr ⟨nookPC1, by simp [nookPins], rfl⟩)
  · rw [nookTC_3]; exact hall _ (Or.inr ⟨nookPC0, by simp [nookPins], rfl⟩)

/-- **The point of the AAM helper.** -/
theorem nook_spot_true (j : Fin (inputsO n Φ).length) {p : Point}
    (hall : ∀ w ∈ nookW j true, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p w) :
    p = gpt (jφ n Φ j) (jψ n Φ j) (nookQ true) := by
  have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
  have hk := inputsO_var hΦ hi
  refine nook_helper_spot hk hi rfl nookQB_0 nookQB_1 nookQB_2 nookQB_3 ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro m (rfl | rfl | rfl | rfl)
  · rw [nookTB_0]; exact hall _ (Or.inr ⟨nookPB2, by simp [nookPins], rfl⟩)
  · rw [nookTB_1]; exact hall _ (Or.inl rfl)
  · rw [nookTB_2]; exact hall _ (Or.inr ⟨nookPB0, by simp [nookPins], rfl⟩)
  · rw [nookTB_3]; exact hall _ (Or.inr ⟨nookPB1, by simp [nookPins], rfl⟩)

/-- The AAM pins are not seen from the point of the chain helper. -/
theorem nook_early (j : Fin (inputsO n Φ).length) {w : Point} (hw : w ∈ nookW j true) {p : Point}
    (hp : p ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (hall : ∀ w ∈ nookW j false, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p w)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p w) : False := by
  have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
  have hk := inputsO_var hΦ hi
  rcases hw with hw | ⟨c, hc, rfl⟩
  · rw [mem_singleton_iff] at hw; subst hw
    exact cwit_disjoint hΦ (X := .inr (j, true)) (Y := .inr (j, false)) (by simp) hp hs
      (hall _ (Or.inl rfl))
  · have hpq := nook_spot_false hΦ j hall
    obtain ⟨hok, hcs, hU, -, m, hm, hA⟩ := nookPins_facts true c hc
    refine nook_unseen hk hi rfl hok hcs hU (z := (11, 8)) (by decide)
      (nookPins_true_unseen c hc) (w := gpt (jφ n Φ j) (jψ n Φ j) (c.A.1, c.A.2.2.1)) ?_ ?_
    · rw [hA]; simp only [Rect.set, realR, gpt, mem_ofPred_eq]; exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
    · rw [← show nookQ false = (11, 8) from rfl, ← hpq]; exact sees_symm hs

/-- The chain-helper pins are not seen by the viewers of the AAM witness. -/
theorem nook_late (j : Fin (inputsO n Φ).length) {w : Point} (hw : w ∈ nookW j false) {p : Point}
    (hp : p ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (hm : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (nwit j true))
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p w) : False := by
  have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
  have hk := inputsO_var hΦ hi
  rcases hw with hw | ⟨c, hc, rfl⟩
  · rw [mem_singleton_iff] at hw; subst hw
    exact cwit_disjoint hΦ (X := .inr (j, false)) (Y := .inr (j, true)) (by simp) hp hs hm
  · obtain ⟨d1, d2⟩ := inputO_delta hi hk
    have hH := paramH_ge_q n Φ
    have hφ := nookφ_mono hH d1 d2 (inputsO n Φ)[j].ge
    have hψ := nookψ_mono hH d1 d2 (inputsO n Φ)[j].ge
    have hO := nook_sound hH d1 d2 (inputsO n Φ)[j].ge
    obtain ⟨hok, hcs, hU, hC, m, hmm, hA⟩ := nookPins_facts false c hc
    have hwc : gpt (jφ n Φ j) (jψ n Φ j) (c.A.1, c.A.2.2.1) ∈
        (realR (jφ n Φ j) (jψ n Φ j) c.A).set := by
      rw [hA]; simp only [Rect.set, realR, gpt, mem_ofPred_eq]; exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
    obtain ⟨q1, hq1, hp1, hc1, -⟩ := nook_viewer hk hi rfl hok hcs hU hC hwc (sees_symm hs)
    obtain ⟨q2, hq2, hp2, hc2, -⟩ := nwit_viewer hΦ j true (sees_symm hm)
    have hwf : ∀ (c : GCert), c.ok 20 19 nookOr = true → ∀ q ∈ c.cs, q.1.wf 20 19 = true := by
      intro c hc q hq
      simp only [GCert.ok, Bool.and_eq_true, List.all_eq_true] at hc
      exact (hc.1.2 q hq).1.1.1
    have hw2 : nwit j true ∈ (realR (jφ n Φ j) (jψ n Φ j) (nookWC true).A).set := by
      rw [nookWC_A]; exact gpt_mem_degenerate _ _ _
    exact gdisjB_sound hφ hψ hO (nookPins_false_disj c hc) hwc hw2 hq1 (hwf c hok q1 hq1) hp1 hc1
      hq2 (hwf _ (nookWC_ok true) q2 hq2) hp2 hc2

end NookExcl

/-! ### Pinning -/

/-- The spot of an index: the points seeing all its pin targets. -/
def SpotO (X : CIdx n Φ) : Set Point :=
  {p | ∀ w ∈ WO X, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p w}

/-- The spot of a template witness of a variable or slot group is its spot rectangle. -/
theorem tinst_spot {t : TIdx n Φ} (hb : tgrp t ≠ (2, 0)) {p : Point}
    (hp : p ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled) (hS : p ∈ SpotO (.inl t)) :
    p ∈ (((tinst t).1.sps.getD (tinst t).2.2 LR.dflt).real (tinst t).2.1 (Hr n Φ)).set := by
  rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i
  · exact GData.spot gVarD_valid (varZ_in k.isLt) gVarD_spots i.isLt hp hS
  · exact GData.spot (slotD_valid _) (by rw [slotD_gs]; exact slotZ_in c.isLt) (slotD_spots _)
      (by rw [slotD_Ws]; exact i.isLt) hp hS
  · exact absurd rfl hb

theorem rkO_basin {t : TIdx n Φ} (hb : tgrp t = (2, 0)) : rkO (.inl t) = 0 := by
  rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i
  · simp [tgrp] at hb
  · simp [tgrp] at hb
  · rfl

/-- Two template witnesses of the same group instance: a viewer of the earlier one (in its spot
if it is ranked lower) does not see a pin target of the other. -/
theorem tmpl_excl {t t' : TIdx n Φ} (hg : tgrp t' = tgrp t) (hne : t' ≠ t) {w : Point}
    (hw : w ∈ WO (n := n) (Φ := Φ) (.inl t)) {p : Point}
    (hpm : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (cwit (n := n) (Φ := Φ) (.inl t')))
    (hsp : rkO (n := n) (Φ := Φ) (.inl t') < rkO (.inl t) →
      p ∈ (((tinst t').1.sps.getD (tinst t').2.2 LR.dflt).real (tinst t').2.1 (Hr n Φ)).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p w) : False := by
  obtain ⟨eD, eo, ei⟩ := tgrp_eq hg
  have hij := ei hne
  have hj := tinst_lt t'
  rw [eD] at hj
  have hp' : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p
      (((tinst t).1.Ws[(tinst t').2.2]'hj).a.real ((tinst t).2.1 : ℝ) (Hr n Φ)) := by
    have h := hpm
    simp only [cwit] at h
    rw [twit_eq, eD, eo, List.getD_eq_getElem _ _ hj] at h
    exact h
  refine GData.excl (tinst_valid t) (tinst_in t) (tinst_lt t) hj (Ne.symm hij) hw hp' ?_ hs
  intro hlt
  have h := hsp (by simp only [rkO]; rw [eD]; exact hlt)
  rw [eD, eo] at h
  exact h

/-- **Guard positions.** For a boundary guard set with `guardsO n Φ` points, every guard seeing
the counting witness of an index sees all its pin targets. -/
theorem pinnedO (hΦ : ∀ c ∈ Φ, c.VarsLt n) (G : Finset Point)
    (hG : (Polygon.mk ((polyO n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point))
    (hcard : G.card = guardsO n Φ) :
    ∀ X : CIdx n Φ, ∀ q ∈ G, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees q (cwit X) → q ∈ SpotO X := by
  refine pinned_of_covers G (covers_of_boundaryGuardSet hG) cwit (cwit_boundary hΦ)
    (fun X Y hXY p hp h1 h2 => cwit_disjoint hΦ hXY hp h1 h2) (by rw [card_CIdx]; exact hcard)
    WO (fun X w hw => WO_bd hΦ X hw) SpotO (fun X p _ h => h) rO rO_wf ?_ ?_
  · -- earlier indices
    intro X Y hYX hr w hw p hp hpS hpm hs
    rcases X with t | ⟨j, b⟩ <;> rcases Y with t' | ⟨j', b'⟩
    · have hg : tgrp t' = tgrp t := hr.1
      by_cases hb : tgrp t' = (2, 0)
      · have hb' : tgrp t = (2, 0) := by rw [← hg]; exact hb
        have h1 := rkO_basin hb
        have h2 := rkO_basin hb'
        have := hr.2; rw [h1, h2] at this; exact absurd this (lt_irrefl 0)
      exact tmpl_excl hg (fun h => hYX (by rw [h])) hw hpm (fun _ => tinst_spot hb hp hpS) hs
    · exact absurd hr.1 (by rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i <;> simp [grpO, tgrp])
    · exact absurd hr.1 (by rcases t' with ⟨k, i⟩ | ⟨c, i⟩ | i <;> simp [grpO, tgrp])
    · have hj : j = j' := Fin.ext (by simpa [grpO] using hr.1.symm)
      subst hj
      have hr2 := hr.2
      cases b <;> cases b' <;> simp [rkO] at hr2
      exact nook_early hΦ j hw hp hpS hs
  · -- later indices
    intro X Y hYX hr w hw p hp hpm hs
    by_cases hg : grpO Y = grpO X
    · rcases X with t | ⟨j, b⟩ <;> rcases Y with t' | ⟨j', b'⟩
      · exact tmpl_excl hg (fun h => hYX (by rw [h])) hw hpm (fun hlt => absurd ⟨hg, hlt⟩ hr) hs
      · exact absurd hg (by rcases t with ⟨k, i⟩ | ⟨c, i⟩ | i <;> simp [grpO, tgrp])
      · exact absurd hg (by rcases t' with ⟨k, i⟩ | ⟨c, i⟩ | i <;> simp [grpO, tgrp])
      · have hj : j = j' := Fin.ext (by simpa [grpO] using hg.symm)
        subst hj
        cases b <;> cases b'
        · exact hYX rfl
        · exact nook_late hΦ j hw hp hpm hs
        · exact hr ⟨hg, by simp [rkO]⟩
        · exact hYX rfl
    · have s1 := WO_viewer hΦ X hw (sees_symm hs)
      have s2 := WO_viewer hΦ Y (cwit_mem_WO Y) (sees_symm hpm)
      rcases stripO_disj hΦ hg with h | h <;> linarith [s1.1, s1.2, s2.1, s2.2]

/-! ### The assignment of the guards -/

/-- The guard assignment of a boundary guard set with `guardsO n Φ` points: a bijection onto
the guard set, every guard in the spot of its index. -/
structure AssignO (n : ℕ) (Φ : List Constraint) (G : Finset Point) where
  γ : CIdx n Φ → Point
  mem : ∀ X, γ X ∈ G
  onto : ∀ q ∈ G, ∃ X, γ X = q
  filled : ∀ X, γ X ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled
  spot : ∀ X, γ X ∈ SpotO X

/-- **Guard positions.** -/
theorem exists_assignO (hΦ : ∀ c ∈ Φ, c.VarsLt n) (G : Finset Point)
    (hG : (Polygon.mk ((polyO n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point))
    (hcard : G.card = guardsO n Φ) : Nonempty (AssignO n Φ G) := by
  obtain ⟨γ, hγ, -, honto, -, -⟩ := assignment_of_covers G (covers_of_boundaryGuardSet hG) cwit
    (cwit_boundary hΦ) (fun X Y hXY p hp h1 h2 => cwit_disjoint hΦ hXY hp h1 h2)
    (by rw [card_CIdx]; exact hcard)
  have hpin := pinnedO hΦ G hG hcard
  exact ⟨⟨γ, fun X => (hγ X).1, honto, fun X => hG.1 (hγ X).1,
    fun X => hpin X _ (hγ X).1 (hγ X).2⟩⟩

end

end ArtGallery.Orthogonal.Hard
