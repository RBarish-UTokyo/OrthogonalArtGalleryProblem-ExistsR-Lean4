module

public import ArtGallery.Orthogonal.Hard.PinAssm

/-!
# What a helper sees above the ceiling strip

A certificate whose target is the spot of a helper (`spotFarB`) shows that the points seen by the
helper lie in the zone boxes of its group or in an escaping cone (along the line of its wall)
that stays right of `x = ox − 10` above `y = 2H − 1/4`.  Hence a helper of a group whose boxes
lie right of `−10` sees no point above the ceiling strip left of `x = −10` (`spot_far`): in
particular no point of a copy nook.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-- The spot certificate check of witness `i`: the target is its spot, the certificate is valid,
and the escaping cone stays right of `x = −10` above `y = 2H − 1/4`. -/
def spotFarB (D : GData) (i : ℕ) (T : TCert) : Bool :=
  decide (D.sps.getD i LR.dflt = T.A) && (T.cert D.gs).ok &&
    decide (T.cones.length = (groupLR D.gs).length) &&
    match T.C with
    | none => true
    | some K => rightOfBA T.A K (-10) (-1 / 4, 2) yMax

variable {n : ℕ} {Φ : List Constraint}

/-- **A helper sees nothing above the ceiling strip left of `x = −10`.** -/
theorem spot_far {D : GData} (hD : D.Valid) {ox : ℚ} (hgs : ∀ g ∈ D.gs, g.InPoly n Φ ox)
    (hox : 0 ≤ ox) (hfar : -10 ≤ ox + D.x0) {i : ℕ} {T : TCert} (h : spotFarB D i T = true)
    {p : Point} (hp : p ∈ ((D.sps.getD i LR.dflt).real ox (Hr n Φ)).set) {s : Point}
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p s)
    (hs2 : 2 * Hr n Φ - 1 / 4 ≤ s.2) : -10 < s.1 := by
  have hH := Hr_ge n Φ
  have eH : Hr n Φ = (paramH n Φ : ℝ) := by simp [Hr]
  simp only [spotFarB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hA, ok⟩, l⟩, hC⟩ := h
  rw [hA] at hp
  have hb := (groupOK_parts hD.group).1
  have he := hD.ext
  simp only [groupExtB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Option.isNone_iff_eq_none, decide_eq_true_eq] at he
  have hox' : (0 : ℝ) ≤ ox := by exact_mod_cast hox
  have hfar' : (-10 : ℝ) ≤ ox + D.x0 := by exact_mod_cast hfar
  rcases TCert.sees hgs ok l hb hp hs with ⟨q, hq, -, -, hpU⟩ | ⟨hCs, -⟩
  · have hk' : q.2.1 < (D.gs.map GZ.box).length := LCert.box_lt ok hq
    have hpU' : s ∈ ((D.gs.map GZ.box).getD q.2.1 LBox.default).set ox (Hr n Φ) := hpU
    rw [List.getD_eq_getElem _ _ hk', List.getElem_map] at hpU'
    have hk'' : q.2.1 < D.gs.length := by simpa using hk'
    have hbx := he.1 _ (List.getElem_mem hk'')
    obtain ⟨hx0, -, -, -⟩ := hpU'
    revert hbx hx0
    cases (D.gs[q.2.1]).box.x0 with
    | none => intro hbx; simp at hbx
    | some a =>
      cases (D.gs[q.2.1]).box.x1 with
      | none => intro hbx; simp at hbx
      | some b =>
        intro hbx hx0
        simp only [decide_eq_true_eq] at hbx
        have h0 := hx0 a rfl
        have : (D.x0 : ℝ) ≤ a := by exact_mod_cast hbx.1
        linarith
  · cases hTC : T.C with
    | none => rw [hTC] at hCs; exact absurd hCs (by simp [optCone])
    | some K =>
      rw [hTC] at hCs hC
      have hY := strip_bound n Φ s (mem_filled_of_sees hs)
      have := rightOfBA_sound hC hH ox hp hCs
        (by simp only [AH.ev]; push_cast; linarith)
        (by simp only [yMax, AH.ev] at hY ⊢; push_cast at hY ⊢; linarith [hY.2])
      push_cast at this
      linarith

end

end ArtGallery.Orthogonal.Hard
