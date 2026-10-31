module

public import ArtGallery.Orthogonal.Hard.CovCanonBase
public import ArtGallery.Orthogonal.Hard.CovRegion
public import ArtGallery.Orthogonal.Hard.CovBasin

/-!
# Completeness: the basin

Every point of a rectangle of the basin zone is seen by `H_L` or is a band point.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

set_option maxRecDepth 100000 in
theorem gCovBasin_good : gCovBasin.frame.good = (groupLR basinZ).map Prod.fst := by decide +kernel

theorem gCovBasin_guard : guardB (fun _ => [(25 / 2, (-5 / 2, 0))]) 1 gCovBasin = true := by
  decide +kernel

theorem gCovBasin_rngs_ne : (List.range gCovBasin.items.length).all
    (fun k => !(gCovBasin.rngs.getD k []).isEmpty) = true := by decide +kernel

theorem gCovBasin_strips : gCovBasin.frame.strips = [] := by decide +kernel

theorem gCovBasin_hall : gCovBasin.frame.hall = ⟨15 / 8, 161 / 8, (-1 / 4, 0), (-1 / 4, 2)⟩ := by
  decide +kernel

theorem gCovBasin_x : gCovBasin.frame.good.all (fun R => decide (R.x1 ≤ 161 / 8)) = true := by
  decide +kernel

theorem basinZ_in' : ∀ g ∈ basinZ, g.InPoly n Φ (xL n Φ) := basinZ_in

theorem basin_hall : ((gCovBasin.frame.hall.real (xL n Φ) (Hr n Φ)).set) ⊆ PO n Φ := by
  have hH := Hr_ge' (n := n) (Φ := Φ)
  have hxL := xL_eq (n := n) (Φ := Φ)
  have hxR : (100 : ℝ) ≤ xR n Φ := by exact_mod_cast xR_pos n Φ
  rw [gCovBasin_hall]
  intro p hp
  simp only [LR.real, Rect.set, mem_ofPred_eq, AH.ev] at hp
  push_cast at hp
  obtain ⟨p1, p2, p3, p4⟩ := hp
  have eH : Hr n Φ = (paramH n Φ : ℝ) := by simp [Hr]
  exact hall_filled (by linarith) (by linarith) (by linarith) (by linarith)

/-- **The basin.** -/
theorem basin_cover (hΦ : ∀ c ∈ Φ, c.VarsLt n) {g : GZ} (hg : g ∈ basinZ) {l : LR}
    (hl : l ∈ g.rects) {z : Point} (hz : z ∈ (l.real (xL n Φ) (Hr n Φ)).set) :
    (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (hL n Φ) z ∨ BandOK n Φ z := by
  rcases groupCov_canon_rect basinZ_in gCovBasin_ok gCovBasin_good
    (by rw [gCovBasin_strips]; simp) basin_hall gCovBasin_guard (γ := fun _ => hL n Φ)
    (fun i _ S _ hR => by
      have := hR _ (List.mem_singleton_self _)
      simp only [LP.real, AH.ev] at this
      push_cast at this
      convert this using 2 <;> simp [hL]) hg hl hz with
    ⟨_, _, h⟩ | ⟨j, hj, hne, -⟩ | ⟨i, hi, hzi, -, h1, h2⟩
  · exact Or.inl h
  · exfalso
    have := List.all_eq_true.1 gCovBasin_rngs_ne j (List.mem_range.2 hj)
    rw [hne] at this
    simp at this
  · right
    have hx := List.all_eq_true.1 gCovBasin_x _ (List.getElem_mem hi)
    simp only [decide_eq_true_eq] at hx
    have hx' : ((gCovBasin.frame.good[i]).x1 : ℝ) ≤ ((161 / 8 : ℚ) : ℝ) := by exact_mod_cast hx
    push_cast at hx'
    obtain ⟨-, z2, -, -⟩ := hzi
    simp only [LR.real] at z2
    exact ⟨h1, h2, basin_noW (by linarith), basin_noE hΦ (by linarith)⟩

end

end ArtGallery.Orthogonal.Hard
