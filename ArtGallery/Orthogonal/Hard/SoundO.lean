module

public import ArtGallery.Orthogonal.Hard.AddGeO
public import ArtGallery.Orthogonal.Hard.InvRevLeO
public import ArtGallery.Stade.Lower

/-!
# Soundness of the orthogonal construction (statement (c))

A boundary guard set `G` of `polyO n Φ` with `|G| = guardsO n Φ` encodes a solution of the
one-free instance `Φ`: the guard assignment (`exists_assignO`) puts the guard of variable `k` at
`(a_k, H + 2 v_k − 1)` (`AssignO.varPos`), and
* copy nooks: `w ≤ v` (type GE) resp. `v ≤ w` (type LE) (`copyO_rel`);
* gadgets: `invGeO_rel`, `invRevLeO_rel`, `addLeO_rel`, `addGeO_rel`;
* composition with the copy inequalities by monotonicity, as in Stade's `Assign.holds`.
-/

@[expose] public section

namespace ArtGallery.Orthogonal.Hard

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade

variable {n : ℕ} {Φ : List Constraint}

section Sat

variable {G : Finset Point} (A : AssignO n Φ G)

/-- The candidate solution: the values of the variable guards. -/
noncomputable def AssignO.sol (i : ℕ) : ℝ :=
  if h : i < n then ((A.γ (varIdx ⟨i, h⟩)).2 - Hr n Φ + 1) / 2 else 1

theorem AssignO.sol_eq {i : ℕ} (h : i < n) :
    A.sol i = ((A.γ (varIdx ⟨i, h⟩)).2 - Hr n Φ + 1) / 2 := dif_pos h

theorem AssignO.sol_mem {i : ℕ} (h : i < n) : 1 / 2 ≤ A.sol i ∧ A.sol i ≤ 2 := by
  rw [A.sol_eq h]
  have := A.varPos ⟨i, h⟩
  constructor <;> linarith [this.2.1, this.2.2]

/-- The value of the variable copied by an input is the candidate solution at that variable. -/
theorem AssignO.cval_eq (hΦ : ∀ c ∈ Φ, c.VarsLt n) (c : Fin (paramC Φ)) {m : ℕ}
    (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) :
    A.cval hΦ c hm = A.sol (slotIn (n := n) c hm).var := by
  rw [A.sol_eq (inputsO_var hΦ (slotIn_mem c hm))]; rfl

/-- Copy inequalities in terms of the candidate solution, for a slot input with known variable
and type. -/
theorem AssignO.copy (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hG : (Polygon.mk ((polyO n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point))
    (c : Fin (paramC Φ)) {m : ℕ} (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) {x : ℕ}
    (hvar : (cVars (gadAt Φ c)).getD (oTmplInputs (cKind (gadAt Φ c)))[m].role 0 = x) :
    ((oTmplInputs (cKind (gadAt Φ c)))[m].ge = true → A.ival c hm ≤ A.sol x) ∧
      ((oTmplInputs (cKind (gadAt Φ c)))[m].ge = false → A.sol x ≤ A.ival c hm) := by
  have h := copyO_rel hΦ A c hm hG
  rw [A.cval_eq hΦ c hm] at h
  have e : (slotIn (n := n) c hm).var = x := hvar
  rw [e] at h
  exact h

/-- The template input `m` of a slot of kind `k`, by its data. -/
theorem tmplIn_eq {k : TKind} {c : Fin (paramC Φ)} (hk : cKind (gadAt Φ c) = k) {m : ℕ}
    (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) :
    (oTmplInputs (cKind (gadAt Φ c)))[m] = (oTmplInputs k)[m]'(by rw [← hk]; exact hm) := by
  have : ∀ (l : List TInput) (hl : l = oTmplInputs k) (h1 : m < l.length),
      l[m] = (oTmplInputs k)[m]'(hl ▸ h1) := by
    rintro _ rfl _; rfl
  exact this _ (by rw [hk]) hm

/-- Every constraint of a one-free instance holds for the candidate solution. -/
theorem AssignO.holds (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hone : ∀ c ∈ Φ, isGad c = true)
    (hG : (Polygon.mk ((polyO n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point))
    {c : Constraint} (hcΦ : c ∈ Φ) : c.Holds A.sol := by
  have hvl := hΦ c hcΦ
  cases c with
  | one x => exact absurd (hone _ hcΦ) (by simp [isGad])
  | invGe x y =>
    obtain ⟨hx, hy⟩ := hvl
    obtain ⟨s, hs, hgad⟩ := exists_slot hcΦ rfl
    set c : Fin (paramC Φ) := ⟨s, hs⟩
    have hk : cKind (gadAt Φ c) = .invGe := by simp only [c]; rw [hgad]; rfl
    have hvars : cVars (gadAt Φ c) = [x, y] := by simp only [c]; rw [hgad]; rfl
    have h1 := (A.copy hΦ hG c (ig_h0 hk) (x := x) (by rw [tmplIn_eq hk, hvars]; rfl)).1
      (by rw [tmplIn_eq hk]; rfl)
    have h2 := (A.copy hΦ hG c (ig_h1 hk) (x := y) (by rw [tmplIn_eq hk, hvars]; rfl)).1
      (by rw [tmplIn_eq hk]; rfl)
    have hr := invGeO_rel hΦ A hk hG
    have := A.ival_mem c (ig_h0 hk)
    have := A.ival_mem c (ig_h1 hk)
    show 1 ≤ A.sol x * A.sol y
    nlinarith
  | invRevLe x y =>
    obtain ⟨hx, hy⟩ := hvl
    obtain ⟨s, hs, hgad⟩ := exists_slot hcΦ rfl
    set c : Fin (paramC Φ) := ⟨s, hs⟩
    have hk : cKind (gadAt Φ c) = .invRevLe := by simp only [c]; rw [hgad]; rfl
    have hvars : cVars (gadAt Φ c) = [x, y] := by simp only [c]; rw [hgad]; rfl
    have h1 := (A.copy hΦ hG c (ir_h0 hk) (x := x) (by rw [tmplIn_eq hk, hvars]; rfl)).2
      (by rw [tmplIn_eq hk]; rfl)
    have h2 := (A.copy hΦ hG c (ir_h1 hk) (x := y) (by rw [tmplIn_eq hk, hvars]; rfl)).1
      (by rw [tmplIn_eq hk]; rfl)
    have hr := invRevLeO_rel hΦ A hk hG
    have := A.ival_mem c (ir_h0 hk)
    have := A.ival_mem c (ir_h1 hk)
    have := A.sol_mem hx
    have := A.sol_mem hy
    show A.sol x * (5 / 2 - A.sol y) ≤ 1
    nlinarith [mul_le_mul h1 (by linarith : 5 / 2 - A.sol y ≤ 5 / 2 - A.ival c (ir_h1 hk))
      (by linarith) (by linarith)]
  | addLe x y z =>
    obtain ⟨hx, hy, hz⟩ := hvl
    obtain ⟨s, hs, hgad⟩ := exists_slot hcΦ rfl
    set c : Fin (paramC Φ) := ⟨s, hs⟩
    have hk : cKind (gadAt Φ c) = .addLe := by simp only [c]; rw [hgad]; rfl
    have hvars : cVars (gadAt Φ c) = [x, y, z] := by simp only [c]; rw [hgad]; rfl
    have h0 := (A.copy hΦ hG c (al_hm hk 0 (by norm_num)) (x := y)
      (by rw [tmplIn_eq hk, hvars]; rfl)).2 (by rw [tmplIn_eq hk]; rfl)
    have h1 := (A.copy hΦ hG c (al_hm hk 1 (by norm_num)) (x := x)
      (by rw [tmplIn_eq hk, hvars]; rfl)).2 (by rw [tmplIn_eq hk]; rfl)
    have h2 := (A.copy hΦ hG c (al_hm hk 2 (by norm_num)) (x := z)
      (by rw [tmplIn_eq hk, hvars]; rfl)).1 (by rw [tmplIn_eq hk]; rfl)
    have hr := addLeO_rel hΦ A hk hG
    show A.sol x + A.sol y ≤ A.sol z
    linarith
  | addGe x y z =>
    obtain ⟨hx, hy, hz⟩ := hvl
    obtain ⟨s, hs, hgad⟩ := exists_slot hcΦ rfl
    set c : Fin (paramC Φ) := ⟨s, hs⟩
    have hk : cKind (gadAt Φ c) = .addGe := by simp only [c]; rw [hgad]; rfl
    have hvars : cVars (gadAt Φ c) = [x, y, z] := by simp only [c]; rw [hgad]; rfl
    have h0 := (A.copy hΦ hG c (ag_hm hk 0 (by norm_num)) (x := z)
      (by rw [tmplIn_eq hk, hvars]; rfl)).2 (by rw [tmplIn_eq hk]; rfl)
    have h1 := (A.copy hΦ hG c (ag_hm hk 1 (by norm_num)) (x := y)
      (by rw [tmplIn_eq hk, hvars]; rfl)).1 (by rw [tmplIn_eq hk]; rfl)
    have h2 := (A.copy hΦ hG c (ag_hm hk 2 (by norm_num)) (x := x)
      (by rw [tmplIn_eq hk, hvars]; rfl)).1 (by rw [tmplIn_eq hk]; rfl)
    have hr := addGeO_rel hΦ A hk hG
    show A.sol z ≤ A.sol x + A.sol y
    linarith

/-- The guard of variable `i` is `(a_i, H + 2 v_i − 1)`. -/
theorem AssignO.var_mem {i : ℕ} (hi : i < n) :
    (((varA Φ i : ℚ) : ℝ), Hr n Φ + 2 * A.sol i - 1) ∈ G := by
  have e : (((varA Φ i : ℚ) : ℝ), Hr n Φ + 2 * A.sol i - 1) = A.γ (varIdx ⟨i, hi⟩) := by
    refine Prod.ext (A.varPos ⟨i, hi⟩).1.symm ?_
    simp only [A.sol_eq hi]; ring
  rw [e]
  exact A.mem _

end Sat

/-- **(c) Soundness.**  A boundary guard set of `polyO n Φ` of cardinality `guardsO n Φ` encodes a
solution of the one-free instance `Φ`, the guard of variable `i` being `(a_i, H + 2 v_i − 1)`. -/
theorem sat_of_boundaryGuardO (n : ℕ) (Φ : List Constraint) (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hone : ∀ c ∈ Φ, isGad c = true) (G : Finset Point)
    (hG : (Polygon.mk ((polyO n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point))
    (hcard : G.card = guardsO n Φ) :
    ∃ v : ℕ → ℝ, (∀ i < n, 1 / 2 ≤ v i ∧ v i ≤ 2) ∧ (∀ c ∈ Φ, c.Holds v) ∧
      ∀ i < n, (((varA Φ i : ℚ) : ℝ), Hr n Φ + 2 * v i - 1) ∈ G := by
  obtain ⟨A⟩ := exists_assignO hΦ G hG hcard
  exact ⟨A.sol, fun i hi => A.sol_mem hi, fun c hc => A.holds hΦ hone hG hc,
    fun i hi => A.var_mem hi⟩

end ArtGallery.Orthogonal.Hard

end
