module

public import ArtGallery.Orthogonal.Hard.Simple
public import ArtGallery.Stade.Counting

/-!
# Orientation of the orthogonal polygon

`interiorLeftO n Φ`: the interior of `polyO n Φ` lies to the left of every edge.  The closing edge
`(x_L, 2H) → (x_L, −1)` (the left wall) lies on the line `x = x_L`, all vertices have abscissa
`≥ x_L` (`polyO_fst_ge`), and it is traversed downwards; `interiorLeft_of_left_edge` applies.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational

variable {n : ℕ} {Φ : List Constraint}

/-- Every vertex of the orthogonal polygon has abscissa at least `x_L`. -/
theorem polyO_fst_ge : ∀ p ∈ (polyO n Φ).map ratPoint, ((xL n Φ : ℚ) : ℝ) ≤ p.1 := by
  have hx : (xL n Φ : ℝ) < xR n Φ := by exact_mod_cast xL_lt_xR n Φ
  rw [polyO_map]
  intro p hp
  simp only [List.mem_append, List.mem_cons, List.mem_flatten, List.mem_map,
    List.not_mem_nil, or_false] at hp
  rcases hp with (((rfl | ⟨f, ⟨g, hg, rfl⟩, hpf⟩) | (rfl | rfl)) | ⟨f, ⟨g, hg, rfl⟩, hpf⟩) | rfl
  · exact le_rfl
  · have h := (floor_featureO g hg).1
    exact (h.2.2.2.2.2.2 p (mem_chainSet_of_mem hpf (by simpa using h.1))).1.le
  · exact hx.le
  · exact hx.le
  · have h := (ceil_featureO g hg).1
    exact (h.2.2.2.2.2.2 p (mem_chainSet_of_mem hpf (by simpa using h.1))).1.le
  · exact le_rfl

theorem polyO_length_ge : 4 ≤ (polyO n Φ).length := by
  simp [polyO]; omega

theorem polyO_head : (polyO n Φ).headD 0 = (xL n Φ, -1) := by simp [polyO]

theorem polyO_last : (polyO n Φ).getD ((polyO n Φ).length - 1) 0 = (xL n Φ, 2 * (paramH n Φ : ℚ)) := by
  have e : polyO n Φ = ([(xL n Φ, -1)] ++ (floorFeatsO n Φ).flatten ++
      [(xR n Φ, -1), (xR n Φ, 2 * (paramH n Φ : ℚ))] ++ (ceilFeatsO n Φ).flatten) ++
      [(xL n Φ, 2 * (paramH n Φ : ℚ))] := rfl
  rw [e, List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

/-- **The interior of the orthogonal polygon lies to the left of every edge.** -/
theorem interiorLeftO (n : ℕ) (Φ : List Constraint) :
    (Polygon.mk ((polyO n Φ).map ratPoint)).InteriorLeft := by
  have hP := simpleO n Φ
  have hn : (Polygon.mk ((polyO n Φ).map ratPoint)).n = (polyO n Φ).length := n_map_ratPoint _
  have hlen := polyO_length_ge (n := n) (Φ := Φ)
  have hH := paramH_ge_q n Φ
  have hlast := polyO_last (n := n) (Φ := Φ)
  have hhead : (polyO n Φ).getD 0 0 = (xL n Φ, -1) := by
    rw [← polyO_head]; cases h : polyO n Φ with
    | nil => simp [h] at hlen
    | cons a l => rfl
  refine interiorLeft_of_left_edge hP (i := (polyO n Φ).length - 1) (by omega)
    (x₀ := (xL n Φ : ℝ)) ?_ ?_ ?_ ?_
  · intro j hj
    rw [hn] at hj
    rw [vtx_map_ratPoint]
    have hm : ratPoint ((polyO n Φ).getD j 0) ∈ (polyO n Φ).map ratPoint := by
      rw [List.getD_eq_getElem _ _ hj]
      exact List.mem_map_of_mem (List.getElem_mem hj)
    exact polyO_fst_ge _ hm
  · rw [vtx_map_ratPoint, hlast]; rfl
  · rw [hn, show (polyO n Φ).length - 1 + 1 = (polyO n Φ).length by omega, Nat.mod_self,
      vtx_map_ratPoint, hhead]; rfl
  · rw [hn, show (polyO n Φ).length - 1 + 1 = (polyO n Φ).length by omega, Nat.mod_self,
      vtx_map_ratPoint, vtx_map_ratPoint, hhead, hlast]
    show (((-1 : ℚ)) : ℝ) < ((2 * (paramH n Φ : ℚ) : ℚ) : ℝ)
    exact_mod_cast (by linarith : (-1 : ℚ) < 2 * (paramH n Φ : ℚ))

end

end ArtGallery.Orthogonal.Hard
