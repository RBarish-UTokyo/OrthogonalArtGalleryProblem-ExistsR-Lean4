module

public import ArtGallery.Orthogonal.Hard.InvRevLeO
public import ArtGallery.Orthogonal.Hard.DoorO

/-!
# Exclusion for the nooks of the addition gadgets (generic part)

A point `s` strictly inside a nook segment of an addition slot `c` (on the line `x = g + 30`,
in the low strip) is seen only by the aux guard of the slot or by the designated input
(`addO_excl`).  The geometry of the nook enters through a predicate `PV` (the partial-visibility
region: the room of the nook and the cones beyond its doors) satisfied by every viewer of `s`
right of the nook line (`hpv`), and through the facts that the other guards of the slot and the
guards of the slots to the right avoid `PV`; the viewers left of the nook line are excluded by
the empty box along the nook edge (`hwall`).  The guards of the groups to the left (variables,
basin, copy nooks, slots `c' < c`) lie left of the nook line by their strips.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

variable {n : ℕ} {Φ : List Constraint}

section Excl

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n) {G : Finset Point} (A : AssignO n Φ G)
include hΦ

/-- **Exclusion for a nook of an addition slot.** -/
theorem addO_excl {c : Fin (paramC Φ)} {k : TKind} (hk : cKind (gadAt Φ c) = k)
    {ia : ℕ} {iW : List ℕ} {j m0 : ℕ}
    (hcls : ∀ i < (slotD k).Ws.length, (i % 2 = 0 ∧ i / 2 < (oTmplInputs k).length) ∨
      (∃ p ∈ slotSCs k, p.1 = i) ∨ i = ia ∨ i ∈ iW)
    {s : Point} (hs1 : s.1 = (slotG n Φ c : ℝ) + 30) (hs4 : -400 ≤ s.2) (hs5 : s.2 ≤ 0)
    (hj : j < (oNooks k).length)
    (hsN : s ∈ (((oNooks k).getD j LR.dflt).real (slotG n Φ c : ℚ) (Hr n Φ)).set)
    (hwall : ∀ z : Point, z.1 < (slotG n Φ c : ℝ) + 30 →
      ¬ (Polygon.mk ((polyO n Φ).map ratPoint)).Sees z s)
    (hexempt : ∀ p ∈ slotSCs k, (p.1, j) ∈ nookExempt k → ((slotD k).sps.getD p.1 LR.dflt).x1 < 30)
    (PV : Point → Prop)
    (hpv : ∀ z, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees z s → (slotG n Φ c : ℝ) + 30 ≤ z.1 → PV z)
    (hin : ∀ m (hm : m < (oTmplInputs k).length), m ≠ m0 → ∀ y : ℝ, 0 ≤ y → y ≤ 6 →
      ¬ PV ((slotG n Φ c : ℝ) + (((oTmplInputs k)[m]).lx : ℝ), y))
    (hfarIn : ∀ z : Point, (slotG n Φ c : ℝ) + 1230 ≤ z.1 → 0 ≤ z.2 → z.2 ≤ 6 → ¬ PV z)
    (hfarBox : ∀ z : Point, (slotG n Φ c : ℝ) + 1100 ≤ z.1 → -140 ≤ z.2 → z.2 ≤ 0 → ¬ PV z)
    (hW : ∀ i ∈ iW, ∀ hi : i < (slotWs (cKind (gadAt Φ c))).length,
      ¬ (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ (.inl (.inr (.inl ⟨c, ⟨i, hi⟩⟩)))) s)
    {X : CIdx n Φ} (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    (∃ hi : ia < (slotWs (cKind (gadAt Φ c))).length, X = .inl (.inr (.inl ⟨c, ⟨ia, hi⟩⟩))) ∨
      ∃ hm : m0 < (oTmplInputs (cKind (gadAt Φ c))).length, X = inIdx c hm := by
  subst hk
  set g : ℝ := (slotG n Φ c : ℝ) with hg
  have hH := paramH_ge_q n Φ
  have hHr : (1000 : ℝ) ≤ Hr n Φ := by simp only [Hr]; exact_mod_cast hH
  have hleft : ∀ Y : CIdx n Φ, (A.γ Y).1 < g + 30 →
      ¬ (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ Y) s := fun Y h => hwall _ h
  rcases X with t | ⟨j', b'⟩
  · rcases t with ⟨k', i'⟩ | ⟨c', i'⟩ | i'
    · -- a variable group: left of the slot
      exfalso
      refine hleft _ ?_ hX
      have hstrip := A.strip hΦ (.inl (.inl (k', i')))
      simp only [stripO, tstrip] at hstrip
      have := var_slot_sep (n := n) (Φ := Φ) (c := c.1) k'.isLt
      linarith [hstrip.2]
    · -- a slot group
      rcases lt_trichotomy c'.1 c.1 with hlt | heq | hgt
      · -- a slot to the left
        exfalso
        refine hleft _ ?_ hX
        have hstrip := A.strip hΦ (.inl (.inr (.inl ⟨c', i'⟩)))
        simp only [stripO, tstrip] at hstrip
        have := slotG_sep (n := n) (Φ := Φ) hlt
        linarith [hstrip.2]
      · -- the slot itself
        have hcc : c' = c := Fin.ext heq
        subst hcc
        have hi'L : i'.1 < (slotD (cKind (gadAt Φ c'))).Ws.length := by rw [slotD_Ws]; exact i'.isLt
        rcases hcls i'.1 hi'L with ⟨hev, hlt⟩ | ⟨p, hpm, hpi⟩ | hia | hiW
        · -- an input of the slot
          have hi'eq : i' = ⟨2 * (i'.1 / 2), slotIn_lt hlt⟩ := Fin.ext (by simp only; omega)
          have hXe : (.inl (.inr (.inl ⟨c', i'⟩)) : CIdx n Φ) = inIdx c' hlt := by exact inIdx_of_even hev hlt
          by_cases hm : i'.1 / 2 = m0
          · right
            refine ⟨hm ▸ hlt, ?_⟩
            rw [hXe]
            exact inIdx_congr hm hlt _
          · exfalso
            rw [hXe] at hX
            have hpos := A.inPos c' hlt
            have hl0 : (30 : ℝ) ≤ (oTmplInputs (cKind (gadAt Φ c')))[i'.1 / 2].lx := by
              exact_mod_cast (slotIn_lx c' hlt).1
            have hpv' := hpv _ hX (by rw [hpos.1]; push_cast; linarith)
            have e : A.γ (inIdx c' hlt) =
                (g + ((oTmplInputs (cKind (gadAt Φ c')))[i'.1 / 2].lx : ℝ), (A.γ (inIdx c' hlt)).2) :=
              Prod.ext hpos.1 rfl
            rw [e] at hpv'
            exact hin _ hlt hm _ hpos.2.1 hpos.2.2 hpv'
        · -- a helper of the slot
          exfalso
          have hsp := (A.sc_data hpm hpi).2.2
          by_cases hex : (p.1, j) ∈ nookExempt (cKind (gadAt Φ c'))
          · have hx := hexempt p hpm hex
            obtain ⟨-, h2, -, -⟩ := hsp
            have hA : p.2.A = (slotD (cKind (gadAt Φ c'))).sps.getD p.1 LR.dflt := by
              have hsc := slotSCs_ok _ p hpm
              simp only [spotFarB, Bool.and_eq_true, decide_eq_true_eq] at hsc
              exact hsc.1.1.1.symm
            rw [hA] at h2
            simp only [LR.real] at h2
            have hx' : (((slotD (cKind (gadAt Φ c'))).sps.getD p.1 LR.dflt).x1 : ℝ) < 30 := by
              exact_mod_cast hx
            exact hleft _ (by push_cast at h2; linarith) hX
          · have hsN' : s ∈ (((oNooks (cKind (gadAt Φ c')))[j]).real (slotG n Φ c' : ℚ) (Hr n Φ)).set := by
              rw [← List.getD_eq_getElem _ LR.dflt hj]; exact hsN
            exact A.sc_unseen hpm hpi hj hex hsN' hX
        · -- the aux guard
          left
          refine ⟨hia ▸ i'.isLt, ?_⟩
          congr 4
          exact Fin.ext hia
        · -- a wall helper box of the slot
          exact absurd hX (hW _ hiW i'.isLt)
      · -- a slot to the right
        exfalso
        have hsep := slotG_sep (n := n) (Φ := Φ) hgt
        have hcl := slotClass_ok (cKind (gadAt Φ c'))
        simp only [slotClassB, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
          List.any_eq_true] at hcl
        have hi'L : i'.1 < (slotD (cKind (gadAt Φ c'))).Ws.length := by rw [slotD_Ws]; exact i'.isLt
        rcases hcl i'.1 hi'L with (⟨hev, hlt⟩ | ⟨p, hpm, hpi⟩) | hbox
        · have hi'eq : i' = ⟨2 * (i'.1 / 2), slotIn_lt hlt⟩ := Fin.ext (by simp only; omega)
          have hXe : (.inl (.inr (.inl ⟨c', i'⟩)) : CIdx n Φ) = inIdx c' hlt := by exact inIdx_of_even hev hlt
          rw [hXe] at hX
          have hpos := A.inPos c' hlt
          have hl0 : (30 : ℝ) ≤ (oTmplInputs (cKind (gadAt Φ c')))[i'.1 / 2].lx := by
            exact_mod_cast (slotIn_lx c' hlt).1
          have hx : g + 1230 ≤ (A.γ (inIdx c' hlt)).1 := by rw [hpos.1]; push_cast; linarith
          exact hfarIn _ hx hpos.2.1 hpos.2.2 (hpv _ hX (by linarith))
        · have := A.sc_low hpm hpi hX hs4 hs5
          linarith [this.1]
        · simp only [boxPVB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hbox
          obtain ⟨⟨r0, r1, r2, r3, r4, r5⟩, -⟩ := hbox
          have hsp := A.tspot (t := .inr (.inl ⟨c', i'⟩)) (by simp [tgrp])
          simp only [tinst] at hsp
          obtain ⟨g1, g2, g3, g4⟩ := hsp
          simp only [LR.real, AH.ev] at g1 g2 g3 g4
          rw [r0] at g3; rw [r1] at g4
          set r := (slotD (cKind (gadAt Φ c'))).sps.getD i'.1 LR.dflt
          have r2' : (-140 : ℝ) ≤ r.y0.1 := by exact_mod_cast r2
          have r3' : (r.y1.1 : ℝ) ≤ 0 := by exact_mod_cast r3
          have r4' : (-100 : ℝ) ≤ r.x0 := by exact_mod_cast r4
          push_cast at g1 g2 g3 g4
          exact hfarBox _ (by linarith) (by linarith) (by linarith) (hpv _ hX (by linarith))
    · -- the basin: left of the slots
      exfalso
      refine hleft _ ?_ hX
      have hstrip := A.strip hΦ (.inl (.inr (.inr i')))
      simp only [stripO, tstrip] at hstrip
      have := xL_slot_sep (n := n) (Φ := Φ) c.1
      linarith [hstrip.2]
  · -- a copy-nook helper: left of the variables
    exfalso
    refine hleft _ ?_ hX
    have hi : (inputsO n Φ)[j'] ∈ inputsO n Φ := List.getElem_mem j'.isLt
    have hstrip := A.strip hΦ (.inr (j', b'))
    simp only [stripO] at hstrip
    have hjX : jX n Φ j' + 11 ≤ 0 := by have := (nookX_bounds hΦ hi).2; simp only [jX]; linarith
    have : (0 : ℝ) ≤ g := by positivity
    linarith [hstrip.2]

end Excl

end

end ArtGallery.Orthogonal.Hard
