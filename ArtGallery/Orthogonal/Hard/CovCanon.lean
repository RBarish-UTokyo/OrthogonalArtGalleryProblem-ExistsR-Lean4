module

public import ArtGallery.Orthogonal.Hard.PosO
public import ArtGallery.Orthogonal.Hard.CovCanonBase

/-!
# Completeness: the canonical guards

For values `v` of the variables, the canonical guard `canonO v X` of a counting index `X`:

* the guard of variable `k` at `(a_k, H + 2 v_k − 1)`, an input guard of a slot at
  `(g_c + δ, 4 v − 2)` (`v` the value of the variable it copies);
* the aux guard of an addition slot at the canonical point `I(v_x, v_y)` (`alOI`, `agOI`);
* the wall helpers `W`, `W₂` of an addition slot at the centre of their spot;
* every other helper at its (one-point) spot, the basin helper at `H_L`, the copy-nook helpers
  at their grid points.

The coverage certificates (`CovGroup`) only know the *range* of a guard: a list of points whose
convex hull contains the guard for all admissible values (`wRange`).  `canon_mem_convex` is that
fact for every template witness.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Ranges -/

/-- How the canonical guard of a witness sits in its spot. -/
inductive WTag
  /-- anywhere in the spot rectangle (its four corners are the range) -/
  | spot
  /-- at the centre of the spot -/
  | centre
  /-- the aux point of an addition slot -/
  | aux
  /-- the z input of `addLe`: in the upper part `[2, 6]` of its segment -/
  | trunc
  deriving DecidableEq

/-- The tags of the witnesses of a slot of kind `k`: inputs `2m`, cups `2m + 1`, helpers, and
for the addition slots the aux guard `15` and the wall helpers `16`, `17`. -/
def slotTag (k : TKind) (i : ℕ) : WTag :=
  if (k = .addLe ∨ k = .addGe) ∧ i = 15 then .aux
  else if (k = .addLe ∨ k = .addGe) ∧ (i = 16 ∨ i = 17) then .centre
  else if k = .addLe ∧ i = 4 then .trunc
  else .spot

/-- The centre of a spot. -/
def LR.centre (r : LR) : LP :=
  ((r.x0 + r.x1) / 2, ((r.y0.1 + r.y1.1) / 2, (r.y0.2 + r.y1.2) / 2))

/-- The sample values of the aux point (frame coordinates): `addLe` at `(1/2, 1/2)`,
`(3/2, 1/2)`, `(1/2, 3/2)`; `addGe` at the four corners of `[1/2, 2]²`. -/
def auxSamples : TKind → List LP
  | .addLe => [(16990 / 71, (-3942 / 71, 0)), (10114 / 41, (-2106 / 41, 0)),
      (51770 / 229, (-13410 / 229, 0))]
  | .addGe => [(131550 / 1607, (-50139 / 1607, 0)), (26790 / 331, (-10383 / 331, 0)),
      (130350 / 1583, (-48291 / 1583, 0)), (132750 / 1631, (-50067 / 1631, 0))]
  | _ => []

/-- The range of a witness with spot `sp` and tag `t`. -/
def tagRange (k : TKind) (sp : LR) : WTag → List LP
  | .spot => sp.corners
  | .centre => [sp.centre]
  | .aux => auxSamples k
  | .trunc => (⟨sp.x0, sp.x1, (2, 0), sp.y1⟩ : LR).corners

/-- The range of witness `i` of a slot of kind `k`. -/
def slotRange (k : TKind) (i : ℕ) : List LP :=
  tagRange k ((slotD k).sps.getD i LR.dflt) (slotTag k i)

/-- The range of witness `i` of a variable group. -/
def varRange (i : ℕ) : List LP := (gVarD.sps.getD i LR.dflt).corners

/-- The range of the basin helper. -/
def basinRange : List LP := [(25 / 2, (-5 / 2, 0))]

/-! ### The canonical guards -/

/-- The value of the variable of role `r` of slot `c`. -/
noncomputable def roleVal (v : ℕ → ℝ) (c : Fin (paramC Φ)) (r : ℕ) : ℝ :=
  v ((cVars (gadAt Φ c)).getD r 0)

/-- The input `m` of a slot of kind `k`. -/
def tIn (k : TKind) (m : ℕ) : TInput := (oTmplInputs k).getD m ⟨0, false, 0, false⟩

/-- The canonical guard of witness `i` of slot `c`. -/
noncomputable def canonSlot (v : ℕ → ℝ) (c : Fin (paramC Φ)) (i : ℕ) : Point :=
  let k := cKind (gadAt Φ c)
  let g : ℝ := slotG n Φ c
  if i % 2 = 0 ∧ i / 2 < (oTmplInputs k).length then
    (g + (tIn k (i / 2)).lx, 4 * roleVal v c (tIn k (i / 2)).role - 2)
  else
    match slotTag k i with
    | .aux => if k = .addLe then alOI g (roleVal v c 0) (roleVal v c 1)
        else agOI g (roleVal v c 0) (roleVal v c 1)
    | .centre => ((slotD k).sps.getD i LR.dflt).centre.real g (Hr n Φ)
    | _ => (((slotD k).sps.getD i LR.dflt).corners.headD (0, (0, 0))).real g (Hr n Φ)

/-- The canonical guard of witness `i` of variable `k`. -/
noncomputable def canonVar (v : ℕ → ℝ) (k : Fin n) (i : ℕ) : Point :=
  if i = 0 then ((varA Φ k : ℝ), Hr n Φ + 2 * v k - 1)
  else ((gVarD.sps.getD i LR.dflt).corners.headD (0, (0, 0))).real (varA Φ k) (Hr n Φ)

/-- **The canonical guard of a counting index.** -/
noncomputable def canonO (v : ℕ → ℝ) : CIdx n Φ → Point
  | .inl (.inl (k, i)) => canonVar (Φ := Φ) v k i.1
  | .inl (.inr (.inl ⟨c, i⟩)) => canonSlot (n := n) v c i.1
  | .inl (.inr (.inr _)) => hL n Φ
  | .inr (j, b) => gpt (jφ n Φ j) (jψ n Φ j) (nookQ b)

/-! ### The slot guards -/

section Slot

variable {v : ℕ → ℝ} (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v)

theorem slotTag_aux {k : TKind} {i : ℕ} (h : slotTag k i = .aux) :
    (k = .addLe ∨ k = .addGe) ∧ i = 15 := by
  unfold slotTag at h; split_ifs at h with h1; exact h1

theorem slotTag_trunc {k : TKind} {i : ℕ} (h : slotTag k i = .trunc) : k = .addLe ∧ i = 4 := by
  unfold slotTag at h; split_ifs at h with h1 h2 h3; exact h3

include hv hsol in
/-- **The canonical guard of a slot witness lies in every convex set containing its range.** -/
theorem canonSlot_mem (c : Fin (paramC Φ)) (i : ℕ) {S : Set Point} (hS : Convex ℝ S)
    (hR : ∀ p ∈ slotRange (cKind (gadAt Φ c)) i, p.real (slotG n Φ c) (Hr n Φ) ∈ S) :
    canonSlot (n := n) v c i ∈ S := by
  have hgc := (gadAt_mem c.isLt).1
  have hHolds := hsol _ hgc
  have hlen : (oTmplInputs (cKind (gadAt Φ c))).length ≤ 3 := by
    cases cKind (gadAt Φ c) <;> decide
  unfold canonSlot
  simp only
  by_cases hin : i % 2 = 0 ∧ i / 2 < (oTmplInputs (cKind (gadAt Φ c))).length
  · simp only [hin, and_self, ↓reduceIte]
    -- an input guard: in its segment `{δ} × [0, 6]` (`[2, 6]` for the z input of `addLe`)
    obtain ⟨h2, hm⟩ := hin
    have hi2 : 2 * (i / 2) = i := by omega
    have hsp := slotIn_sps hm
    rw [hi2] at hsp
    have hlx : (oTmplInputs (cKind (gadAt Φ c)))[i / 2].lx = (tIn (cKind (gadAt Φ c)) (i / 2)).lx := by
      unfold tIn; rw [List.getD_eq_getElem _ _ hm]
    rw [hlx] at hsp
    obtain ⟨hv1, hv2⟩ := hv ((cVars (gadAt Φ c)).getD (tIn (cKind (gadAt Φ c)) (i / 2)).role 0)
    unfold slotRange at hR
    rw [hsp] at hR
    by_cases ht : slotTag (cKind (gadAt Φ c)) i = .trunc
    · obtain ⟨hk, rfl⟩ := slotTag_trunc ht
      rw [ht] at hR
      -- the z input of `addLe`: `v_z ≥ v_x + v_y ≥ 1`
      have hz : 1 ≤ roleVal v c (tIn (cKind (gadAt Φ c)) 2).role := by
        rw [hk]
        have hr : (tIn .addLe 2).role = 2 := rfl
        rw [hr]
        unfold roleVal
        revert hHolds hk
        cases gadAt Φ c <;> intro hHolds hk <;> simp [cKind] at hk
        rename_i x y z
        simp only [Constraint.Holds] at hHolds
        simp only [cVars, List.getD_cons_succ, List.getD_cons_zero]
        linarith [(hv x).1, (hv y).1]
      have e42 : (4 : ℕ) / 2 = 2 := rfl
      rw [e42] at hR
      have := LR.real_subset_convex (r := ⟨(tIn (cKind (gadAt Φ c)) 2).lx,
        (tIn (cKind (gadAt Φ c)) 2).lx, (2, 0), (6, 0)⟩) hS hR
      apply this
      simp only [LR.real, Rect.set, mem_ofPred_eq, AH.ev, e42]
      have hz2 := (hv ((cVars (gadAt Φ c)).getD (tIn (cKind (gadAt Φ c)) 2).role 0)).2
      unfold roleVal at hz ⊢
      push_cast
      refine ⟨le_rfl, le_rfl, by linarith, by linarith⟩
    · have hsp' : slotTag (cKind (gadAt Φ c)) i = .spot := by
        unfold slotTag at ht ⊢
        split_ifs at ht ⊢ with a1 a2 a3 <;>
          first | rfl | (exfalso; have := a1.2; omega) | (exfalso; have := a2.2; omega) | simp at ht
      rw [hsp'] at hR
      have := LR.real_subset_convex hS hR
      apply this
      simp only [LR.real, Rect.set, mem_ofPred_eq, AH.ev, roleVal]
      push_cast
      refine ⟨le_rfl, le_rfl, by linarith, by linarith⟩
  · simp only [hin, ↓reduceIte]
    unfold slotRange at hR
    cases ht : slotTag (cKind (gadAt Φ c)) i with
    | aux =>
      rw [ht] at hR
      obtain ⟨hk, rfl⟩ := slotTag_aux ht
      rcases hk with hk | hk
      · rw [hk] at hR
        simp only [hk, ↓reduceIte]
        simp only [tagRange, auxSamples, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          LP.real, AH.ev] at hR
        push_cast at hR
        obtain ⟨h1, h2, h3⟩ := hR
        revert hHolds hk
        unfold roleVal
        cases gadAt Φ c <;> intro hHolds hk <;> simp [cKind] at hk
        rename_i x y z
        simp only [Constraint.Holds] at hHolds
        simp only [cVars, List.getD_cons_zero, List.getD_cons_succ]
        refine alOI_mem_convex hS ?_ ?_ ?_ (hv x).1 (hv y).1 (by linarith [(hv z).2])
        · rw [alOI_s00]; convert h1 using 2; ring
        · rw [alOI_s10]; convert h2 using 2; ring
        · rw [alOI_s01]; convert h3 using 2; ring
      · rw [hk] at hR
        simp only [hk, reduceCtorEq, ↓reduceIte]
        simp only [tagRange, auxSamples, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          LP.real, AH.ev] at hR
        push_cast at hR
        obtain ⟨h1, h2, h3, h4⟩ := hR
        refine agOI_mem_convex hS ?_ ?_ ?_ ?_ (hv _).1 (hv _).2 (hv _).1 (hv _).2
        · rw [agOI_s00]; convert h1 using 2; ring
        · rw [agOI_s02]; convert h2 using 2; ring
        · rw [agOI_s20]; convert h3 using 2; ring
        · rw [agOI_s22]; convert h4 using 2; ring
    | centre =>
      rw [ht] at hR
      exact hR _ (List.mem_singleton_self _)
    | spot =>
      rw [ht] at hR
      exact hR _ (by simp [tagRange, LR.corners])
    | trunc =>
      exfalso
      obtain ⟨hk, rfl⟩ := slotTag_trunc ht
      exact hin ⟨rfl, by rw [hk]; decide⟩

end Slot

/-! ### The variable and basin guards -/

/-- **The canonical guards of a variable group lie in the hulls of their ranges.** -/
theorem canonVar_mem {v : ℕ → ℝ} (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (k : Fin n) (i : ℕ)
    {S : Set Point} (hS : Convex ℝ S)
    (hR : ∀ p ∈ varRange i, p.real (varA Φ k) (Hr n Φ) ∈ S) :
    canonVar (Φ := Φ) (n := n) v k i ∈ S := by
  unfold canonVar
  split_ifs with h0
  · subst h0
    unfold varRange at hR
    have e : gVarD.sps.getD 0 LR.dflt = ⟨0, 0, (0, 1), (3, 1)⟩ := gVarSps_W1
    rw [e] at hR
    apply LR.real_subset_convex hS hR
    simp only [LR.real, Rect.set, mem_ofPred_eq, AH.ev]
    push_cast
    obtain ⟨h1, h2⟩ := hv k
    refine ⟨by simp, by simp, by linarith, by linarith⟩
  · exact hR _ (by simp [varRange, LR.corners])

end

end ArtGallery.Orthogonal.Hard
