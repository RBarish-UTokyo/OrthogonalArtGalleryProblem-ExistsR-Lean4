module

public import ArtGallery.Orthogonal.Hard.CovCanon
public import ArtGallery.Orthogonal.Hard.CovRegion
public import ArtGallery.Orthogonal.Hard.CovVar
public import ArtGallery.Stade.Guarding

/-!
# Completeness: the variable groups

Every point of the region in a zone box of the group of variable `k` is seen by one of the
three canonical guards of the group (the variable guard and its two helpers), or lies in the
strips `[−1, 2H]` (covered by `CovSeen`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

set_option maxRecDepth 100000 in
theorem gCovVar_good : gCovVar.frame.good = (groupLR varZ).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovVar_guard : guardB varRange gVarWs.length gCovVar = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovVar_rngs_ne : (List.range gCovVar.items.length).all
    (fun k => !(gCovVar.rngs.getD k []).isEmpty) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gCovVar_strips : gCovVar.frame.strips =
    [⟨1 / 8, 25 / 16, (-1, 0), (-1 / 4, 0)⟩, ⟨-25 / 16, -1 / 8, (-1 / 4, 2), (0, 2)⟩] := by
  decide +kernel

theorem gCovVar_hall : gCovVar.frame.hall = ⟨-49 / 16, 49 / 16, (-1 / 4, 0), (-1 / 4, 2)⟩ := by
  decide +kernel

theorem varA_nonneg (k : ℕ) : (0 : ℝ) ≤ (varA Φ k : ℝ) := Nat.cast_nonneg _

theorem hH_nonneg' : (0 : ℝ) ≤ hH n Φ := by
  unfold hH; positivity

/-- The strips of the variable group are in the region. -/
theorem var_strips (hΦ : ∀ c ∈ Φ, c.VarsLt n) {k : ℕ} (hk : k < n) :
    ∀ R ∈ gCovVar.frame.strips, ((R.real ((varA Φ k : ℚ) : ℝ) (Hr n Φ)).set) ⊆ PO n Φ := by
  have hH := Hr_ge' (n := n) (Φ := Φ)
  have hxL : (xL n Φ : ℝ) ≤ -3000 := by exact_mod_cast xL_neg n Φ
  have hxR := varA_le_xR (n := n) (Φ := Φ) hk
  have h0 := varA_nonneg (Φ := Φ) k
  have hh := hH_nonneg' (n := n) (Φ := Φ)
  rw [gCovVar_strips]
  intro R hR p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl <;>
    simp only [LR.real, Rect.set, mem_ofPred_eq, AH.ev] at hp <;> push_cast at hp <;>
    obtain ⟨p1, p2, p3, p4⟩ := hp
  · rcases floor_band (p := p) (by linarith) (by linarith) (by linarith) (by linarith) with h |
      ⟨c, -, -, w1, -, -⟩
    · exact h
    · have := var_slot_sep (n := n) (Φ := Φ) (c := c) hk; linarith
  · have eH : Hr n Φ = (paramH n Φ : ℝ) := by simp [Hr]
    rcases ceil_band (n := n) (Φ := Φ) (p := p) (by linarith) (by linarith) (by linarith)
      (by linarith) with h | ⟨i, hi, w1, w2, -⟩
    · exact h
    · obtain ⟨-, e16, -, e0⟩ := nook_window (n := n) (Φ := Φ) hΦ hi
      linarith

/-- The hall part of the frame of the variable group is in the region. -/
theorem var_hall {k : ℕ} (hk : k < n) :
    ((gCovVar.frame.hall.real ((varA Φ k : ℚ) : ℝ) (Hr n Φ)).set) ⊆ PO n Φ := by
  have hxL : (xL n Φ : ℝ) ≤ -3000 := by exact_mod_cast xL_neg n Φ
  have hxR := varA_le_xR (n := n) (Φ := Φ) hk
  have h0 := varA_nonneg (Φ := Φ) k
  have hh := hH_nonneg' (n := n) (Φ := Φ)
  rw [gCovVar_hall]
  intro p hp
  simp only [LR.real, Rect.set, mem_ofPred_eq, AH.ev] at hp
  push_cast at hp
  obtain ⟨p1, p2, p3, p4⟩ := hp
  have eH : Hr n Φ = (paramH n Φ : ℝ) := by simp [Hr]
  exact hall_filled (by linarith) (by linarith) (by linarith) (by linarith)

theorem gCovVar_x : gCovVar.frame.good.all
    (fun R => decide (-49 / 16 ≤ R.x0) && decide (R.x1 ≤ 49 / 16)) = true := by
  decide +kernel

/-- **The variable groups.** -/
theorem var_cover (hΦ : ∀ c ∈ Φ, c.VarsLt n) {v : ℕ → ℝ} (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2)
    (k : Fin n) {g : GZ} (hg : g ∈ varZ) {l : LR} (hl : l ∈ g.rects) {z : Point}
    (hz : z ∈ (l.real ((varA Φ k : ℚ) : ℝ) (Hr n Φ)).set) :
    (∃ i < gVarWs.length, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (canonVar (Φ := Φ) v k i) z) ∨
      BandOK n Φ z := by
  rcases groupCov_canon_rect (varZ_in k.isLt) gCovVar_ok gCovVar_good (var_strips hΦ k.isLt)
    (var_hall k.isLt) gCovVar_guard (γ := canonVar (Φ := Φ) v k)
    (fun i _ S hS hR => canonVar_mem hv k i hS hR) hg hl hz with
    h | ⟨j, hj, hne, -⟩ | ⟨i, hi, hzi, -, h1, h2⟩
  · exact Or.inl h
  · exfalso
    have := List.all_eq_true.1 gCovVar_rngs_ne j (List.mem_range.2 hj)
    rw [hne] at this
    simp at this
  · right
    have hx := List.all_eq_true.1 gCovVar_x _ (List.getElem_mem hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    have hx0 : ((-49 / 16 : ℚ) : ℝ) ≤ ((gCovVar.frame.good[i]).x0 : ℝ) := by exact_mod_cast hx.1
    have hx1 : ((gCovVar.frame.good[i]).x1 : ℝ) ≤ ((49 / 16 : ℚ) : ℝ) := by exact_mod_cast hx.2
    push_cast at hx0 hx1
    obtain ⟨z1, z2, -, -⟩ := hzi
    simp only [LR.real] at z1 z2
    push_cast at z1 z2
    have h0 := varA_nonneg (Φ := Φ) k
    exact ⟨h1, h2, var_noW k.isLt (by linarith), right_noE hΦ (by linarith)⟩

end

end ArtGallery.Orthogonal.Hard
