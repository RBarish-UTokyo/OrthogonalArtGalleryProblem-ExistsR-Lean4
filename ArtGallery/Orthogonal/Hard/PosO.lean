module

public import ArtGallery.Orthogonal.Hard.PinGlobal

/-!
# Guard positions

For a guard assignment `A` (`AssignO`):

* every guard lies in the strip of its index (`AssignO.strip`);
* a template guard (other than the basin's) lies in the spot rectangle of its witness
  (`AssignO.tspot`); in particular the guard of variable `k` lies on `{a_k} × [H, H + 3]`
  (`AssignO.varPos`) and the guard of input `m` of slot `c` on `{g_c + δ_m} × [0, 6]`
  (`AssignO.inPos`);
* a copy-nook guard is the point of its helper (`AssignO.nookPos`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Data facts -/

theorem gVarSps_W1 : gVarSps.getD 0 LR.dflt = ⟨0, 0, (0, 1), (3, 1)⟩ := by decide

theorem gVarWs_len : gVarWs.length = 3 := by decide

/-- The input witnesses of a slot: witness `2m` is input `m`, with the spot `{δ_m} × [0, 6]`. -/
def slotInB (k : TKind) : Bool :=
  (List.range (oTmplInputs k).length).all fun m =>
    decide (2 * m < (slotD k).Ws.length) &&
    decide ((slotD k).sps.getD (2 * m) LR.dflt =
      ⟨((oTmplInputs k).getD m ⟨0, false, 0, false⟩).lx, ((oTmplInputs k).getD m ⟨0, false, 0, false⟩).lx,
        (0, 0), (6, 0)⟩)

theorem slotIn_ok (k : TKind) : slotInB k = true := by cases k <;> decide +kernel

theorem slotIn_lt {k : TKind} {m : ℕ} (hm : m < (oTmplInputs k).length) :
    2 * m < (slotWs k).length := by
  have h := slotIn_ok k
  simp only [slotInB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← slotD_Ws]; exact (h m hm).1

theorem slotIn_sps {k : TKind} {m : ℕ} (hm : m < (oTmplInputs k).length) :
    (slotD k).sps.getD (2 * m) LR.dflt =
      ⟨(oTmplInputs k)[m].lx, (oTmplInputs k)[m].lx, (0, 0), (6, 0)⟩ := by
  have h := slotIn_ok k
  simp only [slotInB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [(h m hm).2, List.getD_eq_getElem _ _ hm]

/-! ### Indices -/

/-- The index of the guard of variable `k`. -/
def varIdx (k : Fin n) : CIdx n Φ := .inl (.inl (k, ⟨0, by rw [gVarWs_len]; decide⟩))

/-- The index of the guard of input `m` of slot `c`. -/
def inIdx (c : Fin (paramC Φ)) {m : ℕ} (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) :
    CIdx n Φ :=
  .inl (.inr (.inl ⟨c, ⟨2 * m, slotIn_lt hm⟩⟩))

/-! ### Positions -/

section Pos

variable {G : Finset Point} (A : AssignO n Φ G)

/-- **Every guard lies in the strip of its index.** -/
theorem AssignO.strip (hΦ : ∀ c ∈ Φ, c.VarsLt n) (X : CIdx n Φ) :
    (stripO X).1 < (A.γ X).1 ∧ (A.γ X).1 < (stripO X).2 :=
  WO_viewer hΦ X (cwit_mem_WO X) (sees_symm (A.spot X _ (cwit_mem_WO X)))

/-- **A template guard lies in the spot rectangle of its witness.** -/
theorem AssignO.tspot {t : TIdx n Φ} (hb : tgrp t ≠ (2, 0)) :
    A.γ (.inl t) ∈ (((tinst t).1.sps.getD (tinst t).2.2 LR.dflt).real (tinst t).2.1 (Hr n Φ)).set :=
  tinst_spot hb (A.filled _) (A.spot _)

/-- **The guard of variable `k` lies on its segment.** -/
theorem AssignO.varPos (k : Fin n) :
    (A.γ (varIdx k)).1 = ((varA Φ k : ℚ) : ℝ) ∧ Hr n Φ ≤ (A.γ (varIdx k)).2 ∧
      (A.γ (varIdx k)).2 ≤ Hr n Φ + 3 := by
  have h : A.γ (varIdx k) ∈ _ := A.tspot (t := .inl (k, ⟨0, by rw [gVarWs_len]; decide⟩)) (by simp [tgrp])
  simp only [tinst] at h
  have e : gVarD.sps.getD 0 LR.dflt = ⟨0, 0, (0, 1), (3, 1)⟩ := gVarSps_W1
  rw [e] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [LR.real, AH.ev] at h1 h2 h3 h4
  push_cast at h1 h2 h3 h4 ⊢
  exact ⟨le_antisymm (by linarith) (by linarith), by linarith, by linarith⟩

/-- **The guard of input `m` of slot `c` lies on its segment.** -/
theorem AssignO.inPos (c : Fin (paramC Φ)) {m : ℕ}
    (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) :
    (A.γ (inIdx c hm)).1 = ((slotG n Φ c : ℚ) : ℝ) + ((oTmplInputs (cKind (gadAt Φ c)))[m].lx : ℝ) ∧
      0 ≤ (A.γ (inIdx c hm)).2 ∧ (A.γ (inIdx c hm)).2 ≤ 6 := by
  have h : A.γ (inIdx c hm) ∈ _ := A.tspot (t := .inr (.inl ⟨c, ⟨2 * m, slotIn_lt hm⟩⟩)) (by simp [tgrp])
  simp only [tinst] at h
  rw [slotIn_sps hm] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [LR.real, AH.ev] at h1 h2 h3 h4
  push_cast at h1 h2 h3 h4 ⊢
  exact ⟨le_antisymm (by linarith) (by linarith), by linarith, by linarith⟩

/-- **A copy-nook guard is the point of its helper.** -/
theorem AssignO.nookPos (hΦ : ∀ c ∈ Φ, c.VarsLt n) (j : Fin (inputsO n Φ).length) (b : Bool) :
    A.γ (.inr (j, b)) = gpt (jφ n Φ j) (jψ n Φ j) (nookQ b) := by
  have h := A.spot (.inr (j, b))
  cases b
  · exact nook_spot_false hΦ j h
  · exact nook_spot_true hΦ j h

end Pos

end

end ArtGallery.Orthogonal.Hard
