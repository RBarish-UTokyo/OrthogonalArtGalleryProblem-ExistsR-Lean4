module

public import ArtGallery.Orthogonal.Hard.CovInvO
public import ArtGallery.Orthogonal.Hard.CovAddLe
public import ArtGallery.Orthogonal.Hard.CovAddGe

/-!
# Completeness: the addition slots

The three pockets of an addition room (the nooks of the x-, y- and z-inputs) are seen by the aux
guard `I(v_x, v_y)` and the input guard (`AddPocketO`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

/-- The canonical aux guard of an addition slot. -/
theorem canonSlot_aux {v : ℕ → ℝ} (c : Fin (paramC Φ)) :
    canonSlot (n := n) v c 15 = if cKind (gadAt Φ c) = .addLe then
      alOI (slotG n Φ c) (roleVal v c 0) (roleVal v c 1)
    else if cKind (gadAt Φ c) = .addGe then
      agOI (slotG n Φ c) (roleVal v c 0) (roleVal v c 1)
    else canonSlot (n := n) v c 15 := by
  split_ifs with h1 h2
  · have ht : slotTag (cKind (gadAt Φ c)) 15 = .aux := by rw [h1]; decide
    unfold canonSlot
    dsimp only
    rw [if_neg (by omega), ht, if_pos h1]
  · have ht : slotTag (cKind (gadAt Φ c)) 15 = .aux := by rw [h2]; decide
    unfold canonSlot
    dsimp only
    rw [if_neg (by omega), ht, if_neg h1]
  · rfl

/-- The pockets of `addLe` (frame coordinates): x (aux, input `1`), y (aux, input `0`), z (aux,
input `2`). -/
def addLePockets : List PocketD :=
  [⟨(30, (-3327 / 32, 0)), (50, (-99, 0)), (50, (-195 / 2, 0)), (30, (-3313 / 32, 0)), 15, 2⟩,
   ⟨(30, (-174, 0)), (50, (-162, 0)), (50, (-154, 0)), (30, (-2771 / 16, 0)), 15, 0⟩,
   ⟨(30, (-3049 / 24, 0)), (50, (-6083 / 50, 0)), (50, (-120, 0)), (30, (-6083 / 48, 0)), 15, 4⟩]

/-- The pockets of `addGe` (frame coordinates): x (aux, input `2`), y (aux, input `1`), z (aux,
input `0`). -/
def addGePockets : List PocketD :=
  [⟨(30, (-2649 / 64, 0)), (47, (-153 / 4, 0)), (50, (-37, 0)), (30, (-2589 / 64, 0)), 15, 4⟩,
   ⟨(30, (-855 / 8, 0)), (50, (-94, 0)), (50, (-77, 0)), (30, (-1689 / 16, 0)), 15, 2⟩,
   ⟨(30, (-6001 / 96, 0)), (50, (-151 / 3, 0)), (65 / 2, (-5977 / 100, 0)),
    (30, (-5941 / 96, 0)), 15, 0⟩]

set_option maxRecDepth 100000 in
theorem addLe_facts : SlotFacts .addLe gCovAddLe addLePockets := ⟨gCovAddLe_ok, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem addGe_facts : SlotFacts .addGe gCovAddGe addGePockets := ⟨gCovAddGe_ok, by decide +kernel⟩

/-- **The nook conditions of `addLe`.** -/
theorem addLe_spec {v : ℕ → ℝ} (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v)
    (c : Fin (paramC Φ)) (hk : cKind (gadAt Φ c) = .addLe) :
    ∀ p ∈ addLePockets, p.Spec ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ) (canonSlot (n := n) v c p.a)
      (canonSlot (n := n) v c p.b) := by
  have hgc := gadAt_mem (Φ := Φ) c.isLt
  -- the values of the three roles and the constraint
  obtain ⟨vx, vy, vz, ex, ey, ez, hrel⟩ : ∃ vx vy vz, roleVal v c 0 = vx ∧ roleVal v c 1 = vy ∧
      roleVal v c 2 = vz ∧ vx + vy ≤ vz := by
    have hH := hsol _ hgc.1
    unfold roleVal
    clear hsol hv
    revert hH hk
    cases gadAt Φ c <;> simp [cKind, cVars, Constraint.Holds]
  have bx := hv ((cVars (gadAt Φ c)).getD 0 0)
  have by' := hv ((cVars (gadAt Φ c)).getD 1 0)
  have bz := hv ((cVars (gadAt Φ c)).getD 2 0)
  unfold roleVal at ex ey ez
  rw [ex] at bx; rw [ey] at by'; rw [ez] at bz
  have hxy : vx + vy ≤ 2 := by linarith
  have eA : canonSlot (n := n) v c 15 = alOI (slotG n Φ c) vx vy := by
    rw [canonSlot_aux, if_pos hk]; unfold roleVal; rw [ex, ey]
  have hm : ∀ m, m < 3 → m < (oTmplInputs (cKind (gadAt Φ c))).length := by
    intro m hm; rw [hk]; simpa [oTmplInputs] using hm
  have e0 := canonSlot_in (n := n) (v := v) c (hm 0 (by norm_num))
  have e1 := canonSlot_in (n := n) (v := v) c (hm 1 (by norm_num))
  have e2 := canonSlot_in (n := n) (v := v) c (hm 2 (by norm_num))
  simp only [hk, tIn, oTmplInputs, List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2
  unfold roleVal at e0 e1 e2
  rw [ey] at e0; rw [ex] at e1; rw [ez] at e2
  norm_num at e0 e1 e2
  set G : ℝ := (slotG n Φ c : ℝ)
  intro p hp
  simp only [addLePockets, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp only [PocketD.Spec, eA, e0, e1, e2, LP.real_mk] <;> push_cast <;>
    refine ⟨by unfold det; norm_num, by unfold det; norm_num, by unfold det; norm_num,
      by unfold det; norm_num, ?_⟩
  · intro s hs
    have := alO_nook_x (G := G) bx.1 by'.1 hxy (s := s) (by convert hs using 2 <;> ring_nf)
    simpa [alOP, alON1] using this
  · intro s hs
    have := alO_nook_y (G := G) bx.1 by'.1 hxy (s := s) (by convert hs using 2 <;> ring_nf)
    simpa [alOR, alON3] using this
  · intro s hs
    have := alO_nook_z (G := G) bx.1 by'.1 hxy hrel bz.2 (s := s) (by convert hs using 2 <;> ring_nf)
    simpa [alON2, alOQ] using this

/-- **The nook conditions of `addGe`.** -/
theorem addGe_spec {v : ℕ → ℝ} (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v)
    (c : Fin (paramC Φ)) (hk : cKind (gadAt Φ c) = .addGe) :
    ∀ p ∈ addGePockets, p.Spec ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ) (canonSlot (n := n) v c p.a)
      (canonSlot (n := n) v c p.b) := by
  have hgc := gadAt_mem (Φ := Φ) c.isLt
  obtain ⟨vx, vy, vz, ex, ey, ez, hrel⟩ : ∃ vx vy vz, roleVal v c 0 = vx ∧ roleVal v c 1 = vy ∧
      roleVal v c 2 = vz ∧ vz ≤ vx + vy := by
    have hH := hsol _ hgc.1
    unfold roleVal
    clear hsol hv
    revert hH hk
    cases gadAt Φ c <;> simp [cKind, cVars, Constraint.Holds]
  have bx := hv ((cVars (gadAt Φ c)).getD 0 0)
  have by' := hv ((cVars (gadAt Φ c)).getD 1 0)
  have bz := hv ((cVars (gadAt Φ c)).getD 2 0)
  unfold roleVal at ex ey ez
  rw [ex] at bx; rw [ey] at by'; rw [ez] at bz
  have eA : canonSlot (n := n) v c 15 = agOI (slotG n Φ c) vx vy := by
    rw [canonSlot_aux, if_neg (by rw [hk]; decide), if_pos hk]; unfold roleVal; rw [ex, ey]
  have hm : ∀ m, m < 3 → m < (oTmplInputs (cKind (gadAt Φ c))).length := by
    intro m hm; rw [hk]; simpa [oTmplInputs] using hm
  have e0 := canonSlot_in (n := n) (v := v) c (hm 0 (by norm_num))
  have e1 := canonSlot_in (n := n) (v := v) c (hm 1 (by norm_num))
  have e2 := canonSlot_in (n := n) (v := v) c (hm 2 (by norm_num))
  simp only [hk, tIn, oTmplInputs, List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2
  unfold roleVal at e0 e1 e2
  rw [ez] at e0; rw [ey] at e1; rw [ex] at e2
  norm_num at e0 e1 e2
  set G : ℝ := (slotG n Φ c : ℝ)
  intro p hp
  simp only [addGePockets, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp only [PocketD.Spec, eA, e0, e1, e2, LP.real_mk] <;> push_cast <;>
    refine ⟨by unfold det; norm_num, by unfold det; norm_num, by unfold det; norm_num,
      by unfold det; norm_num, ?_⟩
  · intro s hs
    have := agO_nook_x (G := G) bx.1 bx.2 by'.1 by'.2 (s := s) (by convert hs using 2 <;> ring_nf)
    simpa [agON1, agOP] using this
  · intro s hs
    have := agO_nook_y (G := G) bx.1 bx.2 by'.1 by'.2 (s := s) (by convert hs using 2 <;> ring_nf)
    simpa [agON3, agOR] using this
  · intro s hs
    have := agO_nook_z (G := G) bx.1 bx.2 by'.1 by'.2 hrel bz.1 (s := s)
      (by convert hs using 2 <;> ring_nf)
    simpa [agOQ, agON2] using this

end

end ArtGallery.Orthogonal.Hard
