module

public import ArtGallery.Orthogonal.Hard.CovSlotO
public import ArtGallery.Orthogonal.Hard.CovInvGe
public import ArtGallery.Orthogonal.Hard.CovInvRevLe

/-!
# Completeness: the inversion slots

The pocket of an inversion slot is Stade's pocket `I Q P J`; its two guards are the input guards,
and the inversion constraint gives the nook condition (`ig_nook`, `ir_nook`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

/-- The canonical guard of input `m` of a slot. -/
theorem canonSlot_in {v : ℕ → ℝ} (c : Fin (paramC Φ)) {m : ℕ}
    (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) :
    canonSlot (n := n) v c (2 * m) = inPt ((slotG n Φ c : ℝ) + (tIn (cKind (gadAt Φ c)) m).lx)
      (roleVal v c (tIn (cKind (gadAt Φ c)) m).role) := by
  have h2 : 2 * m % 2 = 0 := by omega
  have h3 : 2 * m / 2 = m := by omega
  unfold canonSlot
  simp only [h2, h3, true_and, hm, ↓reduceIte, inPt]

/-- The pocket of `invGe` (frame coordinates). -/
def invGePockets : List PocketD := [⟨(79, (-78, 0)), (97, (-6, 0)), (43, (-6, 0)), (61, (-78, 0)), 0, 2⟩]

/-- The pocket of `invRevLe` (frame coordinates). -/
def invRevLePockets : List PocketD :=
  [⟨(56, (-22, 0)), (80, (-8, 0)), (59, (-1, 0)), (38, (-22, 0)), 0, 2⟩]

set_option maxRecDepth 100000 in
theorem invGe_facts : SlotFacts .invGe gCovInvGe invGePockets := ⟨gCovInvGe_ok, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem invRevLe_facts : SlotFacts .invRevLe gCovInvRevLe invRevLePockets :=
  ⟨gCovInvRevLe_ok, by decide +kernel⟩

theorem LP.real_mk (ox H : ℝ) (x a : ℚ) : LP.real ox H (x, (a, 0)) = (ox + x, (a : ℝ)) := by
  simp [LP.real, AH.ev]

/-- **The nook condition of `invGe`.** -/
theorem invGe_spec {v : ℕ → ℝ} (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v)
    (c : Fin (paramC Φ)) (hk : cKind (gadAt Φ c) = .invGe) :
    ∀ p ∈ invGePockets, p.Spec ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ) (canonSlot (n := n) v c p.a)
      (canonSlot (n := n) v c p.b) := by
  intro p hp
  simp only [invGePockets, List.mem_singleton] at hp
  subst hp
  have hm0 : 0 < (oTmplInputs (cKind (gadAt Φ c))).length := by rw [hk]; decide
  have hm1 : 1 < (oTmplInputs (cKind (gadAt Φ c))).length := by rw [hk]; decide
  have e0 := canonSlot_in (n := n) (v := v) c hm0
  have e1 := canonSlot_in (n := n) (v := v) c hm1
  simp only [Nat.mul_zero, Nat.mul_one] at e0 e1
  simp only [hk, tIn, oTmplInputs, List.getD_cons_zero, List.getD_cons_succ] at e0 e1
  simp only [PocketD.Spec, e0, e1, LP.real_mk]
  obtain ⟨h1, h2, h3, h4⟩ := ig_pocket_ccw (G := (slotG n Φ c : ℝ))
  have hgc := gadAt_mem (Φ := Φ) c.isLt
  have hrel : 1 ≤ roleVal v c 0 * roleVal v c 1 := by
    have hH := hsol _ hgc.1
    have hg := hgc.2
    unfold roleVal
    clear hsol hv e0 e1 h1 h2 h3 h4 hm0 hm1
    revert hH hk hg
    cases gadAt Φ c <;> simp [cKind, isGad, cVars, Constraint.Holds]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [igI, igQ, igP] using h1
  · simpa [igQ, igP, igJ] using h2
  · simpa [igP, igJ, igI] using h3
  · simpa [igJ, igI, igQ] using h4
  · have := ig_nook (G := (slotG n Φ c : ℝ)) (hv _).1 (hv _).2 (hv _).1 (hv _).2 hrel
    simpa [igI, igJ, igQ, igP, roleVal] using this

/-- **The nook condition of `invRevLe`.** -/
theorem invRevLe_spec {v : ℕ → ℝ} (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v)
    (c : Fin (paramC Φ)) (hk : cKind (gadAt Φ c) = .invRevLe) :
    ∀ p ∈ invRevLePockets, p.Spec ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ) (canonSlot (n := n) v c p.a)
      (canonSlot (n := n) v c p.b) := by
  intro p hp
  simp only [invRevLePockets, List.mem_singleton] at hp
  subst hp
  have hm0 : 0 < (oTmplInputs (cKind (gadAt Φ c))).length := by rw [hk]; decide
  have hm1 : 1 < (oTmplInputs (cKind (gadAt Φ c))).length := by rw [hk]; decide
  have e0 := canonSlot_in (n := n) (v := v) c hm0
  have e1 := canonSlot_in (n := n) (v := v) c hm1
  simp only [Nat.mul_zero, Nat.mul_one] at e0 e1
  simp only [hk, tIn, oTmplInputs, List.getD_cons_zero, List.getD_cons_succ] at e0 e1
  simp only [PocketD.Spec, e0, e1, LP.real_mk]
  obtain ⟨h1, h2, h3, h4⟩ := ir_pocket_ccw (G := (slotG n Φ c : ℝ))
  have hgc := gadAt_mem (Φ := Φ) c.isLt
  have hrel : roleVal v c 0 * (5 / 2 - roleVal v c 1) ≤ 1 := by
    have hH := hsol _ hgc.1
    unfold roleVal
    clear hsol hv e0 e1 h1 h2 h3 h4 hm0 hm1
    revert hH hk
    cases gadAt Φ c <;> simp [cKind, cVars, Constraint.Holds]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [irI, irQ, irP] using h1
  · simpa [irQ, irP, irJ] using h2
  · simpa [irP, irJ, irI] using h3
  · simpa [irJ, irI, irQ] using h4
  · have := ir_nook (G := (slotG n Φ c : ℝ)) (hv _).1 (hv _).2 (hv _).1 (hv _).2 hrel
    simpa [irI, irJ, irQ, irP, roleVal] using this

end

end ArtGallery.Orthogonal.Hard
