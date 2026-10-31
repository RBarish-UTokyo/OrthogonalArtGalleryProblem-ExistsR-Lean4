module

public import ArtGallery.Orthogonal.Hard.InvRoomO
public import ArtGallery.Orthogonal.Hard.GadgetExcl
public import ArtGallery.Orthogonal.Hard.CopyO

/-!
# The `invGe` gadget of the orthogonal construction

In a slot of kind `invGe` (origin `g`), Stade's nook segment `[J, I]` lies in the room of the
pocket with door `[P, Q]` (`InvRoomO.lean`).

* `igO_excl`: a guard seeing a point of the nook segment is one of the two inputs of the slot
  (the variable guards, the inputs of other slots, the boxes, the basin and the copy-nook guards
  lie outside the room and outside Stade's partial-visibility region `igPV`; the helpers are
  excluded by their spot certificates, `GadgetExcl.lean`);
* `invGeO_rel`: `1 ≤ w_x w_y` for the values `w = (y + 2)/4` of the two input guards, by Stade's
  `ig_rel_of_cover`.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Exclusion -/

section Excl

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n) {G : Finset Point} (A : AssignO n Φ G)
  {c : Fin (paramC Φ)} (hk : cKind (gadAt Φ c) = .invGe)

include hk in
/-- The two inputs of an `invGe` slot. -/
theorem ig_len : (oTmplInputs (cKind (gadAt Φ c))).length = 2 := by rw [hk]; rfl

include hk in
theorem ig_h0 : 0 < (oTmplInputs (cKind (gadAt Φ c))).length := by rw [hk]; decide

include hk in
theorem ig_h1 : 1 < (oTmplInputs (cKind (gadAt Φ c))).length := by rw [hk]; decide

include hk in
theorem ig_lx (m : ℕ) (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) :
    ((oTmplInputs (cKind (gadAt Φ c)))[m].lx = 40 ∧ m = 0) ∨
      ((oTmplInputs (cKind (gadAt Φ c)))[m].lx = 100 ∧ m = 1) := by
  have key : ∀ (l : List TInput) (hl : l = oTmplInputs .invGe) (hm : m < l.length),
      (l[m].lx = 40 ∧ m = 0) ∨ (l[m].lx = 100 ∧ m = 1) := by
    rintro _ rfl hm
    have : m < 2 := hm
    interval_cases m <;> simp [oTmplInputs]
  exact key _ (by rw [hk]) hm

/-- The witnesses of an `invGe` slot are its inputs and its helpers. -/
theorem invGe_class : ∀ i < (slotD .invGe).Ws.length,
    (i % 2 = 0 ∧ i / 2 < (oTmplInputs .invGe).length) ∨ ∃ p ∈ slotSCs .invGe, p.1 = i := by
  decide

include hΦ in
/-- The copy-nook helpers lie at most `4` above the ceiling. -/
theorem AssignO.nook_y (j : Fin (inputsO n Φ).length) (b : Bool) :
    (A.γ (.inr (j, b))).2 ≤ 2 * Hr n Φ + 4 := by
  have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
  have hk' := inputsO_var hΦ hi
  obtain ⟨-, hψ, -⟩ := nook_grid hk' hi rfl
  rw [A.nookPos hΦ j b]
  have h15 : jψ n Φ j (nookQ b).2 ≤ jψ n Φ j 15 := by
    cases b <;> exact hψ.monotoneOn (by simp [nookQ]) (by simp) (by simp [nookQ])
  refine h15.trans ?_
  simp only [jψ, iψ]
  rw [nookψ_eq _ (by norm_num)]
  have hH := paramH_ge_q n Φ
  have hH' : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := by exact_mod_cast hH
  simp only [cnYe, cnYs, List.getD_cons_succ, List.getD_cons_zero, Hr]
  have h3 : (0 : ℝ) < 2 * ((paramH n Φ : ℚ) : ℝ) - 3 := by linarith
  have he : (3 : ℝ) / (2 * ((paramH n Φ : ℚ) : ℝ) - 3) ≤ 1 := by
    rw [div_le_one h3]; linarith
  push_cast at he ⊢
  linarith

include hΦ in
/-- The copy-nook helpers lie above the ceiling. -/
theorem AssignO.nook_y_lo (j : Fin (inputsO n Φ).length) (b : Bool) :
    2 * Hr n Φ ≤ (A.γ (.inr (j, b))).2 := by
  have hi : (inputsO n Φ)[j] ∈ inputsO n Φ := List.getElem_mem j.isLt
  have hk' := inputsO_var hΦ hi
  obtain ⟨-, hψ, -⟩ := nook_grid hk' hi rfl
  rw [A.nookPos hΦ j b]
  have h3 : jψ n Φ j 3 ≤ jψ n Φ j (nookQ b).2 := by
    cases b <;> exact hψ.monotoneOn (by simp) (by simp [nookQ]) (by simp [nookQ])
  refine le_trans ?_ h3
  simp only [jψ, iψ]
  rw [nook_ψ3]

include hΦ hk in
/-- **Exclusion for the `invGe` nook.** -/
theorem igO_excl {s : Point} (hs : s ∈ segment (igJ (slotG n Φ c : ℝ)) (igI (slotG n Φ c : ℝ)))
    {X : CIdx n Φ} (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    ∃ m, ∃ hm : m < (oTmplInputs (cKind (gadAt Φ c))).length, X = inIdx c hm := by
  set g : ℝ := (slotG n Φ c : ℝ) with hg
  obtain ⟨hs1, hs2, hs3⟩ := ig_nook_iff.1 hs
  have hsR : s ∈ igRoom n Φ c := ig_nook_room hs
  have hH := paramH_ge_q n Φ
  have hHr : (1000 : ℝ) ≤ Hr n Φ := by simp only [Hr]; exact_mod_cast hH
  -- outside the room: the partial-visibility region
  have hpv_of : ∀ p : Point, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p s →
      p ∉ igRoom n Φ c → p ∈ igPV g := fun p hp hpR => by
    obtain ⟨q, hqD, hq⟩ := cross_of_sees_room (igO_room c.isLt hk) hsR hpR hp
    exact mem_igPV_of_cross hs hqD (by rw [segment_comm]; exact hq)
  have hupR : ∀ p : Point, -6 < p.2 → p ∉ igRoom n Φ c := fun p hp hR => by
    have := (mem_igRoom.1 hR).2.2.2; linarith
  have hxR : ∀ p : Point, p.1 < g + 43 ∨ g + 97 < p.1 → p ∉ igRoom n Φ c := fun p hp hR => by
    have := mem_igRoom.1 hR; rcases hp with hp | hp <;> linarith [this.1, this.2.1]
  have hs' : -400 ≤ s.2 ∧ s.2 ≤ 0 := by rw [hs1]; norm_num
  rcases X with t | ⟨j', b'⟩
  · rcases t with ⟨k', i'⟩ | ⟨c', i'⟩ | i'
    · -- a variable group
      exfalso
      have hsep : ((varA Φ k' : ℚ) : ℝ) + Hr n Φ ≤ g := by
        have := s1_lower (Φ := Φ) (c := c.1) k'.isLt
        simp only [Hr, hg]; push_cast; exact_mod_cast this
      by_cases hi0 : i'.1 = 0
      · have hXe : (.inl (.inl (k', i')) : CIdx n Φ) = varIdx k' := by
          simp only [varIdx]; congr; exact Fin.ext hi0
        rw [hXe] at hX
        have hv := A.varPos k'
        have hpv := hpv_of _ hX (hupR _ (by linarith [hv.2.1]))
        obtain ⟨-, h2, -⟩ := hpv
        rw [hv.1] at h2
        linarith [hv.2.2]
      · have := A.varh_low k' i' hi0 hX hs'.1 hs'.2
        linarith [this.2]
    · -- a slot group
      have hcl := slotClass_ok (cKind (gadAt Φ c'))
      simp only [slotClassB, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
        List.any_eq_true] at hcl
      have hi'L : i'.1 < (slotD (cKind (gadAt Φ c'))).Ws.length := by rw [slotD_Ws]; exact i'.isLt
      by_cases hcc : c' = c
      · subst hcc
        have hcl' := invGe_class i'.1 (by
          have e := congrArg (fun k => (slotD k).Ws.length) hk
          omega)
        rcases hcl' with ⟨hev, hlt⟩ | ⟨p, hpm, hpi⟩
        · have hlt' : i'.1 / 2 < (oTmplInputs (cKind (gadAt Φ c'))).length := by
            have e := congrArg (fun k => (oTmplInputs k).length) hk
            omega
          refine ⟨i'.1 / 2, hlt', ?_⟩
          exact inIdx_of_even hev hlt'
        · exfalso
          have hpm' : p ∈ slotSCs (cKind (gadAt Φ c')) := by rw [hk]; exact hpm
          have key : ∀ (l : List LR) (hl : l = oNooks (cKind (gadAt Φ c'))) (hj : 0 < l.length),
              s ∈ ((l[0]).real (slotG n Φ c' : ℚ) (Hr n Φ)).set := by
            rintro l hl hj
            subst hl
            have e : ∀ (l' : List LR) (hl' : l' = oNooks .invGe) (hj' : 0 < l'.length),
                l'[0] = ⟨61, 79, (-78, 0), (-78, 0)⟩ := by
              rintro _ rfl _; rfl
            rw [e _ (by rw [hk]) hj]
            simp only [LR.real, AH.ev, Rect.set, mem_setOf_eq]
            push_cast
            refine ⟨by linarith, by linarith, by linarith, by linarith⟩
          have hj : 0 < (oNooks (cKind (gadAt Φ c'))).length := by rw [hk]; simp [oNooks]
          exact A.sc_unseen hpm' hpi hj (by rw [hk]; simp [nookExempt]) (key _ rfl hj) hX
      · exfalso
        have hsep : g + 1200 ≤ (slotG n Φ c' : ℝ) ∨ (slotG n Φ c' : ℝ) + 1200 ≤ g := by
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hcc) with h | h
          · right; exact slotG_sep h
          · left; exact slotG_sep h
        rcases hcl i'.1 hi'L with (⟨hev, hlt⟩ | ⟨p, hpm, hpi⟩) | hbox
        · -- an input of another slot
          have hi'eq : i' = ⟨2 * (i'.1 / 2), slotIn_lt hlt⟩ := Fin.ext (by simp only; omega)
          have hXe : (.inl (.inr (.inl ⟨c', i'⟩)) : CIdx n Φ) = inIdx c' hlt := by exact inIdx_of_even hev hlt
          rw [hXe] at hX
          have hpos := A.inPos c' hlt
          have hpv := hpv_of _ hX (hupR _ (by linarith [hpos.2.1]))
          have hb := igPV_in_band hpv (by linarith [hpos.2.2])
          rw [hpos.1] at hb
          have hl0 : (30 : ℝ) ≤ (oTmplInputs (cKind (gadAt Φ c')))[i'.1 / 2].lx := by
            exact_mod_cast (slotIn_lx c' hlt).1
          have hl1 : ((oTmplInputs (cKind (gadAt Φ c')))[i'.1 / 2].lx : ℝ) ≤ 600 := by
            exact_mod_cast (slotIn_lx c' hlt).2
          push_cast at hb
          rcases hsep with h | h <;> linarith [hb.1, hb.2]
        · -- a helper of another slot
          have := A.sc_low hpm hpi hX hs'.1 hs'.2
          rcases hsep with h | h <;> linarith [this.1, this.2]
        · -- a box of another slot
          simp only [boxPVB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hbox
          obtain ⟨⟨r0, r1, r2, r3, r4, r5⟩, -⟩ := hbox
          have hsp := A.tspot (t := .inr (.inl ⟨c', i'⟩)) (by simp [tgrp])
          simp only [tinst] at hsp
          obtain ⟨g1, g2, g3, g4⟩ := hsp
          simp only [LR.real, AH.ev] at g1 g2 g3 g4
          rw [r0] at g3; rw [r1] at g4
          set r := (slotD (cKind (gadAt Φ c'))).sps.getD i'.1 LR.dflt
          have r3' : (r.y1.1 : ℝ) ≤ 0 := by exact_mod_cast r3
          have r4' : (-100 : ℝ) ≤ r.x0 := by exact_mod_cast r4
          have r5' : (r.x1 : ℝ) ≤ 560 := by exact_mod_cast r5
          push_cast at g1 g2 g3 g4
          have hy0 : (A.γ (.inl (.inr (.inl ⟨c', i'⟩)))).2 ≤ 0 := by linarith
          have hR : A.γ (.inl (.inr (.inl ⟨c', i'⟩))) ∉ igRoom n Φ c := by
            apply hxR; rcases hsep with h | h
            · right; linarith
            · left; linarith
          have hb := igPV_in_band (hpv_of _ hX hR) (by linarith)
          rcases hsep with h | h <;> linarith [hb.1, hb.2]
    · -- the basin
      exfalso
      have hy := A.basin_low i'
      have hstrip := A.strip hΦ (.inl (.inr (.inr i')))
      simp only [stripO, tstrip] at hstrip
      have hsep := xL_slot_sep (n := n) (Φ := Φ) c.1
      have hR : A.γ (.inl (.inr (.inr i'))) ∉ igRoom n Φ c := hxR _ (Or.inl (by linarith [hstrip.2]))
      have hb := igPV_in_band (hpv_of _ hX hR) (by linarith)
      linarith [hb.1, hstrip.2]
  · -- a copy-nook helper
    exfalso
    have hi : (inputsO n Φ)[j'] ∈ inputsO n Φ := List.getElem_mem j'.isLt
    have hk' := inputsO_var hΦ hi
    have hy := A.nook_y hΦ j' b'
    have hstrip := A.strip hΦ (.inr (j', b'))
    simp only [stripO] at hstrip
    have hjX : jX n Φ j' + 11 ≤ 0 := by have := (nookX_bounds hΦ hi).2; simp only [jX]; linarith
    have hsep : ((varA Φ (inputsO n Φ)[j'].var : ℚ) : ℝ) + Hr n Φ ≤ g := by
      have := s1_lower (Φ := Φ) (c := c.1) hk'
      simp only [Hr, hg]; push_cast; exact_mod_cast this
    have ha : (0 : ℝ) ≤ ((varA Φ (inputsO n Φ)[j'].var : ℚ) : ℝ) := by positivity
    have hR : A.γ (.inr (j', b')) ∉ igRoom n Φ c := hxR _ (Or.inl (by linarith [hstrip.2]))
    obtain ⟨-, h2, -⟩ := hpv_of _ hX hR
    linarith [hstrip.2]

include hΦ hk in
/-- **`invGe`: `1 ≤ w_x w_y`** for the values of the two input guards of the slot. -/
theorem invGeO_rel
    (hG : (Polygon.mk ((polyO n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point)) :
    1 ≤ A.ival c (ig_h0 hk) * A.ival c (ig_h1 hk) := by
  set g : ℝ := (slotG n Φ c : ℝ) with hg
  have hR := igO_room (n := n) c.isLt hk
  have hNR := ig_nook_room (n := n) (Φ := Φ) (c := c.1)
  set v := A.ival c (ig_h0 hk)
  set w := A.ival c (ig_h1 hk)
  obtain ⟨hv1, hv2⟩ := A.ival_mem c (ig_h0 hk)
  obtain ⟨hw1, hw2⟩ := A.ival_mem c (ig_h1 hk)
  have pos : ∀ (m : ℕ) (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) (lx : ℝ),
      ((oTmplInputs (cKind (gadAt Φ c)))[m].lx : ℝ) = lx →
      inPt (g + lx) (A.ival c hm) = A.γ (inIdx c hm) := by
    intro m hm lx hlx
    have hp := A.inPos c hm
    refine Prod.ext ?_ ?_
    · rw [hp.1, hlx]; simp [hg]
    · simp only [inPt_snd, AssignO.ival]; ring
  have e0 : inPt (g + 40) v = A.γ (inIdx c (ig_h0 hk)) := by
    refine pos 0 _ 40 ?_
    rcases ig_lx hk 0 (ig_h0 hk) with ⟨h, -⟩ | ⟨-, h⟩
    · rw [h]; norm_num
    · exact absurd h (by norm_num)
  have e1 : inPt (g + 100) w = A.γ (inIdx c (ig_h1 hk)) := by
    refine pos 1 _ 100 ?_
    rcases ig_lx hk 1 (ig_h1 hk) with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (by norm_num)
    · rw [h]; norm_num
  have hout : ∀ (b u : ℝ), 1 / 2 ≤ u → inPt b u ∉ igRoom n Φ c := by
    intro b u hu hR'
    have := (mem_igRoom.1 hR').2.2.2
    simp only [inPt_snd] at this
    linarith
  have hcov : ∀ s ∈ segment (igJ g) (igI g),
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (inPt (g + 40) v) s ∨
        (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (inPt (g + 100) w) s := by
    intro s hs
    obtain ⟨q, hqG, hqs⟩ := hG.2 _ (ig_nook_bd c.isLt hk hs)
    obtain ⟨X, rfl⟩ := A.onto q hqG
    obtain ⟨m, hm, rfl⟩ := igO_excl hΦ A hk hs hqs
    rcases ig_lx hk m hm with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · left; rw [e0]; exact hqs
    · right; rw [e1]; exact hqs
  exact ig_rel_of_cover hR hNR hv1 hv2 hw1 hw2 (hout _ _ hv1) (hout _ _ hw1) hcov

end Excl

end

end ArtGallery.Orthogonal.Hard
