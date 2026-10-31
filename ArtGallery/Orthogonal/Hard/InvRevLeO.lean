module

public import ArtGallery.Orthogonal.Hard.InvGeO

/-!
# The `invRevLe` gadget of the orthogonal construction

In a slot of kind `invRevLe` (origin `g`), Stade's nook segment `[J, I]` lies in the room of the
pocket cut by the mouth line, with door `[P, Q]` (`InvRoomO.lean`).

* `irO_excl`: a guard seeing a point of the nook segment right of `J` is one of the two inputs
  of the slot.  The wall helper of `P → J` lies below the nook line (`ir_below`); the other
  helpers are excluded by their spot certificates, and the remaining guards lie outside the room
  and outside Stade's partial-visibility region `irPV`;
* `invRevLeO_rel`: `w_x (5/2 − w_y) ≤ 1` for the values of the two input guards, by Stade's
  `ir_rel_of_shadows`; the coverage of the nook segment minus `J` suffices (`cover_closed`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-- A disjunction of closed conditions on the points of an open interval holds on its closure. -/
theorem cover_closed {lo hi α β : ℝ} (hlt : lo < hi)
    (h : ∀ x, lo < x → x < hi → α ≤ x ∨ x ≤ β) : ∀ x, lo ≤ x → x ≤ hi → α ≤ x ∨ x ≤ β := by
  intro x h1 h2
  by_contra hc
  push Not at hc
  obtain ⟨ha, hb⟩ := hc
  set m := (max lo β + min hi α) / 2
  have hm1 : max lo β < min hi α := by
    simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨hlt, by linarith⟩, by linarith, by linarith⟩
  have hl : max lo β < m := by simp only [m]; linarith
  have hr : m < min hi α := by simp only [m]; linarith
  rcases h m (lt_of_le_of_lt (le_max_left _ _) hl) (lt_of_lt_of_le hr (min_le_left _ _)) with h' | h'
  · linarith [min_le_right hi α]
  · linarith [le_max_right lo β]

variable {n : ℕ} {Φ : List Constraint}

section Excl

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n) {G : Finset Point} (A : AssignO n Φ G)
  {c : Fin (paramC Φ)} (hk : cKind (gadAt Φ c) = .invRevLe)

include hk in
theorem ir_h0 : 0 < (oTmplInputs (cKind (gadAt Φ c))).length := by rw [hk]; decide

include hk in
theorem ir_h1 : 1 < (oTmplInputs (cKind (gadAt Φ c))).length := by rw [hk]; decide

include hk in
theorem ir_lx (m : ℕ) (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) :
    ((oTmplInputs (cKind (gadAt Φ c)))[m].lx = 60 ∧ m = 0) ∨
      ((oTmplInputs (cKind (gadAt Φ c)))[m].lx = 104 ∧ m = 1) := by
  have key : ∀ (l : List TInput) (hl : l = oTmplInputs .invRevLe) (hm : m < l.length),
      (l[m].lx = 60 ∧ m = 0) ∨ (l[m].lx = 104 ∧ m = 1) := by
    rintro _ rfl hm
    have : m < 2 := hm
    interval_cases m <;> simp [oTmplInputs]
  exact key _ (by rw [hk]) hm

/-- The witnesses of an `invRevLe` slot are its inputs and its helpers. -/
theorem invRevLe_class : ∀ i < (slotD .invRevLe).Ws.length,
    (i % 2 = 0 ∧ i / 2 < (oTmplInputs .invRevLe).length) ∨ ∃ p ∈ slotSCs .invRevLe, p.1 = i := by
  decide

/-- The spot of the wall helper of `P → J`. -/
theorem ir_helper0_spot : (slotD .invRevLe).sps.getD 4 LR.dflt =
    ⟨131 / 4, 131 / 4, (-109 / 4, 0), (-109 / 4, 0)⟩ := by decide +kernel

include hΦ hk in
/-- **Exclusion for the `invRevLe` nook.** -/
theorem irO_excl {s : Point} (hs : s ∈ segment (irJ (slotG n Φ c : ℝ)) (irI (slotG n Φ c : ℝ)))
    (hsJ : (slotG n Φ c : ℝ) + 38 < s.1)
    {X : CIdx n Φ} (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    ∃ m, ∃ hm : m < (oTmplInputs (cKind (gadAt Φ c))).length, X = inIdx c hm := by
  set g : ℝ := (slotG n Φ c : ℝ) with hg
  obtain ⟨hs1, hs2, hs3⟩ := ir_nook_iff.1 hs
  have hsR : s ∈ irRoom n Φ c := ir_nook_room hs
  have hH := paramH_ge_q n Φ
  have hHr : (1000 : ℝ) ≤ Hr n Φ := by simp only [Hr]; exact_mod_cast hH
  have hpv_of : ∀ p : Point, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p s →
      p ∉ irRoom n Φ c → p ∈ irPV g := fun p hp hpR => by
    obtain ⟨q, hqD, hq⟩ := cross_of_sees_room (irO_room c.isLt hk) hsR hpR hp
    exact mem_irPV_of_cross hs hqD (by rw [segment_comm]; exact hq)
  have hupR : ∀ p : Point, -3 / 4 < p.2 → p ∉ irRoom n Φ c := fun p hp hR => by
    have := (irBig_bounds hR.1).2.2.1; linarith
  have hxR : ∀ p : Point, p.1 < g + 24 ∨ g + 102 < p.1 → p ∉ irRoom n Φ c := fun p hp hR => by
    have := irBig_bounds hR.1; rcases hp with hp | hp <;> linarith [this.1, this.2.1]
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
        obtain ⟨-, -, h3⟩ := hpv_of _ hX (hupR _ (by linarith [hv.2.1]))
        rw [hv.1] at h3
        linarith [hv.2.1]
      · have := A.varh_low k' i' hi0 hX hs'.1 hs'.2
        linarith [this.2]
    · -- a slot group
      have hcl := slotClass_ok (cKind (gadAt Φ c'))
      simp only [slotClassB, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
        List.any_eq_true] at hcl
      have hi'L : i'.1 < (slotD (cKind (gadAt Φ c'))).Ws.length := by rw [slotD_Ws]; exact i'.isLt
      by_cases hcc : c' = c
      · subst hcc
        have hcl' := invRevLe_class i'.1 (by
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
          by_cases h4 : p.1 = 4
          · -- the wall helper of `P → J`: below the nook line
            have hsp := A.tspot (t := .inr (.inl ⟨c', i'⟩)) (by simp [tgrp])
            simp only [tinst] at hsp
            have e4 : (slotD (cKind (gadAt Φ c'))).sps.getD i'.1 LR.dflt =
                ⟨131 / 4, 131 / 4, (-109 / 4, 0), (-109 / 4, 0)⟩ := by
              rw [← hpi, h4, hk]; exact ir_helper0_spot
            rw [e4] at hsp
            obtain ⟨-, -, -, y4⟩ := hsp
            simp only [LR.real, AH.ev] at y4
            norm_num at y4
            exact ir_below c'.isLt hk hs hsJ (by linarith) hX
          · have key : ∀ (l : List LR) (hl : l = oNooks (cKind (gadAt Φ c'))) (hj : 0 < l.length),
                s ∈ ((l[0]).real (slotG n Φ c' : ℚ) (Hr n Φ)).set := by
              rintro l hl hj
              subst hl
              have e : ∀ (l' : List LR) (hl' : l' = oNooks .invRevLe) (hj' : 0 < l'.length),
                  l'[0] = ⟨38, 56, (-22, 0), (-22, 0)⟩ := by
                rintro _ rfl _; rfl
              rw [e _ (by rw [hk]) hj]
              simp only [LR.real, AH.ev, Rect.set, mem_ofPred_eq]
              push_cast
              refine ⟨by linarith, by linarith, by linarith, by linarith⟩
            have hj : 0 < (oNooks (cKind (gadAt Φ c'))).length := by rw [hk]; simp [oNooks]
            have hex : (p.1, 0) ∉ nookExempt (cKind (gadAt Φ c')) := by
              rw [hk]; simp only [nookExempt, List.mem_cons, List.not_mem_nil, or_false,
                Prod.mk.injEq, and_true]; exact h4
            exact A.sc_unseen hpm' hpi hj hex (key _ rfl hj) hX
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
          have hb := irPV_in_band hpv (by linarith [hpos.2.1]) (by linarith [hpos.2.2])
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
          have hR : A.γ (.inl (.inr (.inl ⟨c', i'⟩))) ∉ irRoom n Φ c := by
            apply hxR; rcases hsep with h | h
            · right; linarith
            · left; linarith
          obtain ⟨p1, p2, -⟩ := hpv_of _ hX hR
          rcases hsep with h | h <;> linarith
    · -- the basin
      exfalso
      have hy := A.basin_low i'
      have hstrip := A.strip hΦ (.inl (.inr (.inr i')))
      simp only [stripO, tstrip] at hstrip
      have hsep := xL_slot_sep (n := n) (Φ := Φ) c.1
      have hR : A.γ (.inl (.inr (.inr i'))) ∉ irRoom n Φ c := hxR _ (Or.inl (by linarith [hstrip.2]))
      obtain ⟨p1, -, -⟩ := hpv_of _ hX hR
      linarith [hstrip.2]
  · -- a copy-nook helper
    exfalso
    have hi : (inputsO n Φ)[j'] ∈ inputsO n Φ := List.getElem_mem j'.isLt
    have hk' := inputsO_var hΦ hi
    have hy := A.nook_y_lo hΦ j' b'
    have hstrip := A.strip hΦ (.inr (j', b'))
    simp only [stripO] at hstrip
    have hjX : jX n Φ j' + 11 ≤ 0 := by have := (nookX_bounds hΦ hi).2; simp only [jX]; linarith
    have hsep : ((varA Φ (inputsO n Φ)[j'].var : ℚ) : ℝ) + Hr n Φ ≤ g := by
      have := s1_lower (Φ := Φ) (c := c.1) hk'
      simp only [Hr, hg]; push_cast; exact_mod_cast this
    have ha : (0 : ℝ) ≤ ((varA Φ (inputsO n Φ)[j'].var : ℚ) : ℝ) := by positivity
    have hR : A.γ (.inr (j', b')) ∉ irRoom n Φ c := hxR _ (Or.inl (by linarith [hstrip.2]))
    obtain ⟨-, -, h3⟩ := hpv_of _ hX hR
    linarith [hstrip.2]

include hΦ hk in
/-- **`invRevLe`: `w_x (5/2 − w_y) ≤ 1`** for the values of the two input guards of the slot. -/
theorem invRevLeO_rel
    (hG : (Polygon.mk ((polyO n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point)) :
    A.ival c (ir_h0 hk) * (5 / 2 - A.ival c (ir_h1 hk)) ≤ 1 := by
  set g : ℝ := (slotG n Φ c : ℝ) with hg
  have hR := irO_room (n := n) c.isLt hk
  have hNR := ir_nook_room (n := n) (Φ := Φ) (c := c.1)
  set v := A.ival c (ir_h0 hk)
  set w := A.ival c (ir_h1 hk)
  obtain ⟨hv1, hv2⟩ := A.ival_mem c (ir_h0 hk)
  obtain ⟨hw1, hw2⟩ := A.ival_mem c (ir_h1 hk)
  have pos : ∀ (m : ℕ) (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) (lx : ℝ),
      ((oTmplInputs (cKind (gadAt Φ c)))[m].lx : ℝ) = lx →
      inPt (g + lx) (A.ival c hm) = A.γ (inIdx c hm) := by
    intro m hm lx hlx
    have hp := A.inPos c hm
    refine Prod.ext ?_ ?_
    · rw [hp.1, hlx]; simp [hg]
    · simp only [inPt_snd, AssignO.ival]; ring
  have e0 : inPt (g + 60) v = A.γ (inIdx c (ir_h0 hk)) := by
    refine pos 0 _ 60 ?_
    rcases ir_lx hk 0 (ir_h0 hk) with ⟨h, -⟩ | ⟨-, h⟩
    · rw [h]; norm_num
    · exact absurd h (by norm_num)
  have e1 : inPt (g + 104) w = A.γ (inIdx c (ir_h1 hk)) := by
    refine pos 1 _ 104 ?_
    rcases ir_lx hk 1 (ir_h1 hk) with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (by norm_num)
    · rw [h]; norm_num
  have hout : ∀ (b u : ℝ), 1 / 2 ≤ u → inPt b u ∉ irRoom n Φ c := by
    intro b u hu hR'
    have := (irBig_bounds hR'.1).2.2.1
    simp only [inPt_snd] at this
    linarith
  refine ir_rel_of_shadows (g := g) hv1 hv2 hw1 hw2 (cover_closed (by linarith) ?_)
  intro h hh1 hh2
  have hs : ((h, -22) : Point) ∈ segment (irJ g) (irI g) := ir_nook_iff.2 ⟨rfl, hh1.le, hh2.le⟩
  obtain ⟨q, hqG, hqs⟩ := hG.2 _ (ir_nook_bd c.isLt hk hs)
  obtain ⟨X, rfl⟩ := A.onto q hqG
  obtain ⟨m, hm, rfl⟩ := irO_excl hΦ A hk hs hh1 hqs
  rcases ir_lx hk m hm with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · left; rw [← e0] at hqs; exact ir_x_sees hR hNR hv1 (hout _ _ hv1) hs hqs
  · right; rw [← e1] at hqs; exact ir_y_sees hR hNR hw1 hw2 (hout _ _ hw1) hs hqs

end Excl

end

end ArtGallery.Orthogonal.Hard
