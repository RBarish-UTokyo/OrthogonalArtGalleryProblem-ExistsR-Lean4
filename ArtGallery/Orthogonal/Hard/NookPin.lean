module

public import ArtGallery.Orthogonal.Hard.LowerO
public import ArtGallery.Orthogonal.Hard.QuadO

/-!
# Pinning in the copy nooks (generic part)

The two helpers of a copy nook are pinned as the template helpers: the four arm tips of a helper
are convex corners of the nook whose quadrants meet in its point `q` (`nookQuadB`,
`nook_sees_quad`, `nook_helper_spot`).  The pin targets of the chain helper are not seen by the
viewers of the AAM witness (grid disjointness, `gdisjB`); the pin targets of the AAM helper are
not seen from the point of the chain helper, pinned first (`gptUnseenB`, `nook_unseen`).  The
viewers of all these targets lie in the nook box (`nook_viewer_x`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-- The grid indices of the vertices of the copy nook in the grid of `nookφ`, `nookψ`. -/
def cnG1 : List (ℕ × ℕ) := cnGrid.map fun p => (p.1 + 1, p.2 + 1)

theorem cnG1_length : cnG1.length = 46 := rfl

theorem cnG1_bound : ∀ p ∈ cnG1, p.1 < 20 ∧ p.2 < 19 := by decide

/-- The corner `k` of the copy nook is convex and its cone lies in the half-plane `d` at the
grid point `q` (`0`: `x ≤ q.x`, `1`: `x ≥ q.x`, `2`: `y ≤ q.y`, otherwise `y ≥ q.y`). -/
def nookQuadB (O : GOr) (k : ℕ) (q : ℕ × ℕ) (d : ℕ) : Bool :=
  let u := cnG1.getD (k - 1) (0, 0)
  let v := cnG1.getD k (0, 0)
  let w := cnG1.getD (k + 1) (0, 0)
  decide (0 < k ∧ k + 1 < cnG1.length ∧ q.1 < 20 ∧ q.2 < 19) && O.pos u v w &&
  match d with
  | 0 => decide (v.1 ≤ q.1 ∧ w.1 ≤ v.1 ∧ u.1 ≤ v.1)
  | 1 => decide (q.1 ≤ v.1 ∧ v.1 ≤ w.1 ∧ v.1 ≤ u.1)
  | 2 => decide (v.2 ≤ q.2 ∧ w.2 ≤ v.2 ∧ u.2 ≤ v.2)
  | _ => decide (q.2 ≤ v.2 ∧ v.2 ≤ w.2 ∧ v.2 ≤ u.2)

/-- No point of the grid point `z` sees a target of the certificate (no escaping cone; every
piece containing `z` has a half-plane of each cone robustly missing `z`). -/
def gptUnseenB (O : GOr) (c : GCert) (z : ℕ × ℕ) : Bool :=
  c.C.isNone && c.cs.all fun q => q.2.2.isEmpty ||
    !(decide (q.1.1 ≤ z.1 ∧ z.1 ≤ q.1.2.1 ∧ q.1.2.2.1 ≤ z.2 ∧ z.2 ≤ q.1.2.2.2)) ||
    q.2.2.all fun K => K.any fun h => ghNeg O c.A h (GRect.corners (z.1, z.1, z.2, z.2))

variable {n : ℕ} {Φ : List Constraint}

theorem cnXe_succ (xN u G e : ℚ) {i : ℕ} (hi : i < 18) :
    (cnXe xN u G e).getD (i + 1) 0 = (cnXs xN u G e).getD i 0 := by
  simp only [cnXe, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ (by simpa [cnXs] using hi)]

theorem cnYe_succ (G e H : ℚ) (j : ℕ) : (cnYe G e H).getD (j + 1) 0 = (cnYs G e H).getD j 0 := by
  simp only [cnYe, List.getD_cons_succ]

section Nook

variable {k : ℕ} (hk : k < n) {i : InputSeg} (hi : i ∈ inputsO n Φ) (hik : i.var = k)
include hk hi hik

/-- The copy nook is a feature of the ceiling. -/
theorem nook_feat_mem : copyNookO (varA Φ k) i.b i.ge (paramH n Φ) ∈ ceilFeatsO n Φ := by
  simp only [ceilFeatsO, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_reverse, List.mem_range, beq_iff_eq]
  exact Or.inr ⟨k, hk, i, ⟨hi, hik⟩, rfl⟩

/-- The copy nook is a contiguous part of the vertex list. -/
theorem nook_infix :
    (copyNookO (varA Φ k) i.b i.ge (paramH n Φ)).map ratPoint <:+: (polyO n Φ).map ratPoint := by
  refine List.IsInfix.map _ ((List.infix_of_mem_flatten (nook_feat_mem hk hi hik)).trans ?_)
  unfold polyO
  exact ⟨[(xL n Φ, -1)] ++ (floorFeatsO n Φ).flatten ++
    [(xR n Φ, -1), (xR n Φ, 2 * (paramH n Φ : ℚ))], [(xL n Φ, 2 * (paramH n Φ : ℚ))], by simp⟩

/-- The vertices of the copy nook are the grid points `cnG1`. -/
theorem nook_vtx {j : ℕ} (hj : j < 46) :
    ((copyNookO (varA Φ k) i.b i.ge (paramH n Φ)).map ratPoint).getD j 0 =
      gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) (cnG1.getD j (0, 0)) := by
  have hb := cnG1_bound _ (List.getElem_mem (l := cnG1) (n := j) hj)
  have hj' : j < cnGrid.length := hj
  rw [copyNookO_eq]
  simp only [cnPts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj',
    Option.map_some, Option.getD_some, cnG1, List.getElem?_eq_getElem hj', gpt, iφ, iψ]
  have hb1 : cnGrid[j].1 + 1 < 20 := by simpa [cnG1] using hb.1
  have hb2 : cnGrid[j].2 + 1 < 19 := by simpa [cnG1] using hb.2
  rw [nookφ_eq i.ge hb1, nookψ_eq i.ge hb2, cnXe_succ _ _ _ _ (cnGrid_bound _ (List.getElem_mem hj')).1,
    cnYe_succ]
  simp [ratPoint, List.getD_eq_getElem?_getD]

/-- The vertices of the copy nook are boundary points. -/
theorem nook_vtx_boundary {j : ℕ} (hj : j < 46) :
    gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) (cnG1.getD j (0, 0)) ∈
      (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  rw [← nook_vtx hk hi hik hj]
  refine mem_vertices_boundary ?_
  obtain ⟨s, t, e⟩ := nook_infix hk hi hik
  show _ ∈ (polyO n Φ).map ratPoint
  rw [← e]
  have hl : j < ((copyNookO (varA Φ k) i.b i.ge (paramH n Φ)).map ratPoint).length := by
    rw [List.length_map, copyNookO_eq, cnPts, List.length_map]; exact hj
  rw [List.getD_eq_getElem _ _ hl]
  exact List.mem_append_left _ (List.mem_append_right _ (List.getElem_mem hl))

/-- **Quadrant of a nook corner.** -/
theorem nook_sees_quad {j : ℕ} {q : ℕ × ℕ} {d : ℕ} (h : nookQuadB nookOr j q d = true) {p : Point}
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p
      (gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) (cnG1.getD j (0, 0)))) :
    p ∈ quadSet (gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) q) d := by
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  have hH := paramH_ge_q n Φ
  have hφ := nookφ_mono hH d1 d2 i.ge
  have hψ := nookψ_mono hH d1 d2 i.ge
  have hO := nook_sound hH d1 d2 i.ge
  simp only [nookQuadB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hj0, hj1, hq1, hq2⟩, hpos⟩, hd⟩ := h
  rw [cnG1_length] at hj1
  set M := (copyNookO (varA Φ k) i.b i.ge (paramH n Φ)).map ratPoint with hM
  have hML : M.length = 46 := by rw [hM, List.length_map, copyNookO_eq]; rfl
  obtain ⟨t, ht, e1, e2, e3⟩ := vtx_triple_of_infix (nook_infix hk hi hik) hj0
    (by rw [hML]; exact hj1)
  have hget : ∀ m (hm : m < M.length), M[m] = gpt (iφ Φ (paramH n Φ) k i)
      (iψ Φ (paramH n Φ) k i) (cnG1.getD m (0, 0)) := by
    intro m hm
    rw [← nook_vtx hk hi hik (by omega), List.getD_eq_getElem _ _ hm]
  rw [hget _ (by omega)] at e1 e2 e3
  have hconv := hO.2 _ _ _ hpos
  obtain ⟨l, m, hl, hm, hp⟩ := sees_vtx_cone (simpleO n Φ) (interiorLeftO n Φ) ht e1 e2 e3 hconv hs
  rw [hp]
  set u := cnG1.getD (j - 1) (0, 0)
  set v := cnG1.getD j (0, 0)
  set w := cnG1.getD (j + 1) (0, 0)
  have hmem : ∀ m, m < 46 → (cnG1.getD m (0, 0)).1 < 20 ∧ (cnG1.getD m (0, 0)).2 < 19 := by
    intro m hm'
    rw [List.getD_eq_getElem _ _ (by rw [cnG1_length]; exact hm')]
    exact cnG1_bound _ (List.getElem_mem _)
  have bu := hmem (j - 1) (by omega)
  have bv := hmem j (by omega)
  have bw := hmem (j + 1) (by omega)
  have mφ : ∀ a b : ℕ, a < 20 → b < 20 → a ≤ b →
      iφ Φ (paramH n Φ) k i a ≤ iφ Φ (paramH n Φ) k i b := fun a b ha hb hab =>
    hφ.monotoneOn (by simpa using ha) (by simpa using hb) hab
  have mψ : ∀ a b : ℕ, a < 19 → b < 19 → a ≤ b →
      iψ Φ (paramH n Φ) k i a ≤ iψ Φ (paramH n Φ) k i b := fun a b ha hb hab =>
    hψ.monotoneOn (by simpa using ha) (by simpa using hb) hab
  match d, hd with
  | 0, hd =>
    simp only [decide_eq_true_eq] at hd
    obtain ⟨h1, h2, h3⟩ := hd
    have a1 := mφ _ _ bv.1 hq1 h1
    have a2 := mφ _ _ bw.1 bv.1 h2
    have a3 := mφ _ _ bu.1 bv.1 h3
    simp only [quadSet, gpt, mem_ofPred_eq]
    have := mul_nonpos_of_nonneg_of_nonpos hl (sub_nonpos.2 a2)
    have := mul_nonpos_of_nonneg_of_nonpos hm (sub_nonpos.2 a3)
    linarith
  | 1, hd =>
    simp only [decide_eq_true_eq] at hd
    obtain ⟨h1, h2, h3⟩ := hd
    have a1 := mφ _ _ hq1 bv.1 h1
    have a2 := mφ _ _ bv.1 bw.1 h2
    have a3 := mφ _ _ bv.1 bu.1 h3
    simp only [quadSet, gpt, mem_ofPred_eq]
    have := mul_nonneg hl (sub_nonneg.2 a2)
    have := mul_nonneg hm (sub_nonneg.2 a3)
    linarith
  | 2, hd =>
    simp only [decide_eq_true_eq] at hd
    obtain ⟨h1, h2, h3⟩ := hd
    have a1 := mψ _ _ bv.2 hq2 h1
    have a2 := mψ _ _ bw.2 bv.2 h2
    have a3 := mψ _ _ bu.2 bv.2 h3
    simp only [quadSet, gpt, mem_ofPred_eq]
    have := mul_nonpos_of_nonneg_of_nonpos hl (sub_nonpos.2 a2)
    have := mul_nonpos_of_nonneg_of_nonpos hm (sub_nonpos.2 a3)
    linarith
  | d + 3, hd =>
    simp only [decide_eq_true_eq] at hd
    obtain ⟨h1, h2, h3⟩ := hd
    have a1 := mψ _ _ hq2 bv.2 h1
    have a2 := mψ _ _ bv.2 bw.2 h2
    have a3 := mψ _ _ bv.2 bu.2 h3
    simp only [quadSet, gpt, mem_ofPred_eq]
    have := mul_nonneg hl (sub_nonneg.2 a2)
    have := mul_nonneg hm (sub_nonneg.2 a3)
    linarith

/-- **A point seeing the four arm tips of a nook helper is its point `q`.** -/
theorem nook_helper_spot {q : ℕ × ℕ} {j0 j1 j2 j3 : ℕ} (h0 : nookQuadB nookOr j0 q 0 = true)
    (h1 : nookQuadB nookOr j1 q 1 = true) (h2 : nookQuadB nookOr j2 q 2 = true)
    (h3 : nookQuadB nookOr j3 q 3 = true) {p : Point}
    (hs : ∀ j ∈ [j0, j1, j2, j3], (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p
      (gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) (cnG1.getD j (0, 0)))) :
    p = gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) q :=
  eq_of_quads (nook_sees_quad hk hi hik h0 (hs _ (by simp)))
    (nook_sees_quad hk hi hik h1 (hs _ (by simp))) (nook_sees_quad hk hi hik h2 (hs _ (by simp)))
    (nook_sees_quad hk hi hik h3 (hs _ (by simp)))

/-- **The viewers of a target of a nook certificate without escaping cone** lie in a piece of
the certificate inside the nook box. -/
theorem nook_viewer {c : GCert} (hc : c.ok 20 19 nookOr = true) (hcs : c.cs.map Prod.fst = cnRR)
    (hU : c.U = [nookBox]) (hC : c.C = none) {w p : Point}
    (hw : w ∈ (realR (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) c.A).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p) :
    ∃ q ∈ c.cs, p ∈ (realR (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) q.1).set ∧
      p ∈ gcones (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) w q.2.2 ∧
      p ∈ nookBox.set (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) := by
  rcases sees_nookCert hk hi hik hc hcs hU hw hs with h | ⟨h, -⟩
  · exact h
  · rw [hC] at h; exact absurd h (by simp [goptCone])

/-- The viewers of a target of a nook certificate lie in `x_N − 3 < x < x_N + 7`. -/
theorem nook_viewer_x {c : GCert} (hc : c.ok 20 19 nookOr = true) (hcs : c.cs.map Prod.fst = cnRR)
    (hU : c.U = [nookBox]) (hC : c.C = none) {w p : Point}
    (hw : w ∈ (realR (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) c.A).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p) :
    ((nookX (varA Φ k) i.b i.ge : ℚ) : ℝ) - 3 < p.1 ∧ p.1 < ((nookX (varA Φ k) i.b i.ge : ℚ) : ℝ) + 7 := by
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  have hH := paramH_ge_q n Φ
  obtain ⟨-, -, -, -, hpU⟩ := nook_viewer hk hi hik hc hcs hU hC hw hs
  have hb := (nookBox_set (ge := i.ge)).1 hpU
  have hL := nzone_L hH d1 d2 i.ge
  have hR := nzone_R hH d1 d2 i.ge
  push_cast at hL hR ⊢
  constructor <;> linarith [hb.1, hb.2.1]

/-- **A grid point robustly unseen.** -/
theorem nook_unseen {c : GCert} (hc : c.ok 20 19 nookOr = true) (hcs : c.cs.map Prod.fst = cnRR)
    (hU : c.U = [nookBox]) {z : ℕ × ℕ} (hz : z.1 < 20 ∧ z.2 < 19)
    (hu : gptUnseenB nookOr c z = true) {w : Point}
    (hw : w ∈ (realR (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) c.A).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w
      (gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) z)) : False := by
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  have hH := paramH_ge_q n Φ
  have hφ := nookφ_mono hH d1 d2 i.ge
  have hψ := nookψ_mono hH d1 d2 i.ge
  have hO := nook_sound hH d1 d2 i.ge
  simp only [gptUnseenB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true,
    Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_true', decide_eq_false_iff_not] at hu
  obtain ⟨hC, hq⟩ := hu
  obtain ⟨q, hqm, hp, hcK, -⟩ := nook_viewer hk hi hik hc hcs hU hC hw hs
  obtain ⟨K, hK, hzK⟩ := hcK
  have hwf : q.1.wf 20 19 = true := by
    simp only [GCert.ok, Bool.and_eq_true, List.all_eq_true] at hc
    exact (hc.1.2 q hqm).1.1.1
  simp only [GRect.wf, decide_eq_true_eq] at hwf
  rcases hq q hqm with (he | hn) | hall
  · rw [he] at hK; simp at hK
  · apply hn
    obtain ⟨p1, p2, p3, p4⟩ := hp
    simp only [realR, gpt] at p1 p2 p3 p4
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hφ.le_iff_le (by simpa using (by omega : q.1.1 < 20)) (by simpa using hz.1)).1 p1
    · exact (hφ.le_iff_le (by simpa using hz.1) (by simpa using hwf.2.1)).1 p2
    · exact (hψ.le_iff_le (by simpa using (by omega : q.1.2.2.1 < 19)) (by simpa using hz.2)).1 p3
    · exact (hψ.le_iff_le (by simpa using hz.2) (by simpa using hwf.2.2.2)).1 p4
  · obtain ⟨h, hh, hn⟩ := List.any_eq_true.1 (hall K hK)
    have hzr : gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) z ∈
        (realR (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) (z.1, z.1, z.2, z.2)).set := by
      simp [Rect.set, realR, gpt]
    exact ghNeg_sound hO hn hw hzr (hzK h hh)

end Nook

end

end ArtGallery.Orthogonal.Hard
