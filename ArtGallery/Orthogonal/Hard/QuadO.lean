module

public import ArtGallery.Orthogonal.Hard.PinGroup
public import ArtGallery.Orthogonal.Hard.OrientO
public import ArtGallery.Stade.LowerCopy

/-!
# Corner quadrants of template vertices

A point seeing a convex vertex `v` (neighbours `u`, `w`) lies in the cone
`v + ℝ₊(w − v) + ℝ₊(u − v)` (`Stade.sees_vtx_cone`).  For an axis-parallel convex corner this cone
lies in a closed half-plane `x ≤ c`, `x ≥ c`, `y ≤ c` or `y ≥ c` (`quadB`, checked robustly on
the template data).  The four arm tips of a helper give the four half-planes through its point
`q`, so a point seeing all four tips is `q` (`helper_spot`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-! ### Consecutive vertices -/

/-- Three consecutive points of a contiguous part of the vertex list are consecutive vertices. -/
theorem vtx_triple_of_infix {L M : List Point} (h : M <:+: L) {k : ℕ} (hk0 : 0 < k)
    (hk : k + 1 < M.length) :
    ∃ i < (Polygon.mk L).n,
      (Polygon.mk L).vtx ((i + (Polygon.mk L).n - 1) % (Polygon.mk L).n) = M[k - 1] ∧
      (Polygon.mk L).vtx i = M[k] ∧
      (Polygon.mk L).vtx ((i + 1) % (Polygon.mk L).n) = M[k + 1] := by
  obtain ⟨a, ha, hv⟩ := chain_of_infix_gen h
  have hn : (Polygon.mk L).n = L.length := rfl
  refine ⟨a + k, by omega, ?_, hv k (by omega), ?_⟩
  · rw [hn, show a + k + L.length - 1 = (a + (k - 1)) + L.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    exact hv (k - 1) (by omega)
  · rw [hn, Nat.mod_eq_of_lt (by omega), show a + k + 1 = a + (k + 1) by omega]
    exact hv (k + 1) hk

/-! ### Template vertices in the group frame -/

/-- The frame point (frame of the group, zone offset `δ`) of a template vertex. -/
def tpt (t : ITmpl) (δ : ℚ) (p : ℤ × ℤ × ℤ) : LP :=
  (δ + (p.1 : ℚ) / t.D, ((p.2.1 : ℚ) / t.D, -((p.2.2 : ℚ) / t.D)))

theorem tpt_real (t : ITmpl) (δ ox H : ℚ) (p : ℤ × ℤ × ℤ) :
    (tpt t δ p).real (ox : ℝ) (H : ℝ) =
      ratPoint (ox + δ + (p.1 : ℚ) / t.D, (p.2.1 : ℚ) / t.D - (p.2.2 : ℚ) / t.D * H) := by
  simp only [tpt, LP.real, AH.ev, ratPoint]; push_cast; ext <;> simp <;> ring

variable {n : ℕ} {Φ : List Constraint}

/-- The instantiated template of a group zone is a contiguous part of the vertex list. -/
theorem GZ.infix {g : GZ} {ox : ℚ} (hg : g.InPoly n Φ ox) :
    (g.t.inst (paramH n Φ) (ox + g.δ)).map ratPoint <:+: (polyO n Φ).map ratPoint := by
  unfold GZ.InPoly at hg
  have hfl : ∀ F ∈ floorFeatsO n Φ, F <:+: polyO n Φ := by
    intro F hF
    refine (List.infix_of_mem_flatten hF).trans ?_
    unfold polyO
    exact ⟨[(xL n Φ, -1)], [(xR n Φ, -1), (xR n Φ, 2 * (paramH n Φ : ℚ))] ++
      (ceilFeatsO n Φ).flatten ++ [(xL n Φ, 2 * (paramH n Φ : ℚ))], by simp⟩
  have hcl : ∀ F ∈ ceilFeatsO n Φ, F <:+: polyO n Φ := by
    intro F hF
    refine (List.infix_of_mem_flatten hF).trans ?_
    unfold polyO
    exact ⟨[(xL n Φ, -1)] ++ (floorFeatsO n Φ).flatten ++
      [(xR n Φ, -1), (xR n Φ, 2 * (paramH n Φ : ℚ))], [(xL n Φ, 2 * (paramH n Φ : ℚ))], by simp⟩
  cases hc : g.ceil
  · rw [hc] at hg
    simp only [Bool.false_eq_true, ↓reduceIte] at hg
    have hmem : (fzone g.t (paramH n Φ) (ox + g.δ)).f ∈ (zfO n Φ).map FZone.f :=
      List.mem_map_of_mem hg.2
    rw [zfO_f] at hmem
    obtain ⟨F, hF, hFe⟩ := List.mem_map.1 hmem
    rw [fzone_f hg.1] at hFe
    rw [← hFe]
    exact (hfl F hF).map _
  · rw [hc] at hg
    simp only [↓reduceIte] at hg
    have hmem : (czone g.t (paramH n Φ) (ox + g.δ)).f ∈ (zcO n Φ).map FZone.f :=
      List.mem_map_of_mem hg.2
    rw [zcO_f] at hmem
    obtain ⟨F', hF', hFe⟩ := List.mem_map.1 hmem
    obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hF'
    rw [czone_f hg.1] at hFe
    have hinj : Function.Injective (List.map (fun q : Point => -q)) :=
      List.map_injective_iff.2 neg_injective
    rw [← hinj hFe]
    exact (hcl F hF).map _

/-! ### Quadrants -/

/-- The corner `v` (neighbours `u`, `w`) is convex and its cone lies in the half-plane `d` at
`q`: `0`: `x ≤ q.x`, `1`: `x ≥ q.x`, `2`: `y ≤ q.y`, otherwise `y ≥ q.y`. -/
def quadB (u v w q : LP) (d : ℕ) : Bool :=
  AH.pos (hpv u v w) && match d with
  | 0 => decide (v.1 ≤ q.1 ∧ w.1 ≤ v.1 ∧ u.1 ≤ v.1)
  | 1 => decide (q.1 ≤ v.1 ∧ v.1 ≤ w.1 ∧ v.1 ≤ u.1)
  | 2 => AH.le v.2 q.2 && AH.le w.2 v.2 && AH.le u.2 v.2
  | _ => AH.le q.2 v.2 && AH.le v.2 w.2 && AH.le v.2 u.2

/-- The half-plane `d` at `q`. -/
def quadSet (q : Point) : ℕ → Set Point
  | 0 => {p | p.1 ≤ q.1}
  | 1 => {p | q.1 ≤ p.1}
  | 2 => {p | p.2 ≤ q.2}
  | _ => {p | q.2 ≤ p.2}

/-- **Quadrant of a convex corner**: a point of the polygon seeing the corner `v` lies in the
half-plane `d`. -/
theorem sees_quad {P : Polygon} (hP : P.Simple) (hL : P.InteriorLeft) {i : ℕ} (hi : i < P.n)
    {u v w q : LP} {ox H : ℝ} (hH : 1000 ≤ H) {d : ℕ} (hq : quadB u v w q d = true)
    (hu : P.vtx ((i + P.n - 1) % P.n) = u.real ox H) (hv : P.vtx i = v.real ox H)
    (hw : P.vtx ((i + 1) % P.n) = w.real ox H) {p : Point}
    (h : P.Sees p (v.real ox H)) : p ∈ quadSet (q.real ox H) d := by
  simp only [quadB, Bool.and_eq_true] at hq
  obtain ⟨hc, hd⟩ := hq
  have hconv : 0 < det (u.real ox H) (v.real ox H) (w.real ox H) := by
    rw [hpv_ev]; exact AH.pos_sound hc hH
  obtain ⟨l, m, hl, hm, hp⟩ := sees_vtx_cone hP hL hi hu hv hw hconv h
  rw [hp]
  match d, hd with
  | 0, hd =>
    simp only [decide_eq_true_eq] at hd
    obtain ⟨h1, h2, h3⟩ := hd
    have a1 : (v.1 : ℝ) ≤ q.1 := by exact_mod_cast h1
    have a2 : (w.1 : ℝ) ≤ v.1 := by exact_mod_cast h2
    have a3 : (u.1 : ℝ) ≤ v.1 := by exact_mod_cast h3
    simp only [quadSet, LP.real, mem_ofPred_eq]
    nlinarith
  | 1, hd =>
    simp only [decide_eq_true_eq] at hd
    obtain ⟨h1, h2, h3⟩ := hd
    have a1 : (q.1 : ℝ) ≤ v.1 := by exact_mod_cast h1
    have a2 : (v.1 : ℝ) ≤ w.1 := by exact_mod_cast h2
    have a3 : (v.1 : ℝ) ≤ u.1 := by exact_mod_cast h3
    simp only [quadSet, LP.real, mem_ofPred_eq]
    nlinarith
  | 2, hd =>
    simp only [Bool.and_eq_true] at hd
    obtain ⟨⟨h1, h2⟩, h3⟩ := hd
    have a1 := AH.le_sound h1 hH
    have a2 := AH.le_sound h2 hH
    have a3 := AH.le_sound h3 hH
    simp only [quadSet, LP.real, mem_ofPred_eq]
    nlinarith
  | d + 3, hd =>
    simp only [Bool.and_eq_true] at hd
    obtain ⟨⟨h1, h2⟩, h3⟩ := hd
    have a1 := AH.le_sound h1 hH
    have a2 := AH.le_sound h2 hH
    have a3 := AH.le_sound h3 hH
    simp only [quadSet, LP.real, mem_ofPred_eq]
    nlinarith

/-- The points of the four half-planes at `q` is `q`. -/
theorem eq_of_quads {q p : Point} (h0 : p ∈ quadSet q 0) (h1 : p ∈ quadSet q 1)
    (h2 : p ∈ quadSet q 2) (h3 : p ∈ quadSet q 3) : p = q := by
  simp only [quadSet, mem_ofPred_eq] at h0 h1 h2 h3
  exact Prod.ext (le_antisymm h0 h1) (le_antisymm h2 h3)

/-! ### Template corners -/

/-- The template vertex `k` of a zone of a group is a convex corner whose cone lies in the
half-plane `d` at `q`. -/
def tquadB (g : GZ) (q : LP) (k d : ℕ) : Bool :=
  decide (0 < k) && decide (k + 1 < g.t.pts.length) &&
    quadB (tpt g.t g.δ (g.t.pts.getD (k - 1) 0)) (tpt g.t g.δ (g.t.pts.getD k 0))
      (tpt g.t g.δ (g.t.pts.getD (k + 1) 0)) q d

/-- The real template vertex `k` of a zone of a group. -/
noncomputable def GZ.vtx (g : GZ) (ox H : ℝ) (k : ℕ) : Point := (tpt g.t g.δ (g.t.pts.getD k 0)).real ox H

/-- **Quadrant of a template corner** of a zone of the polygon. -/
theorem GZ.sees_quad {g : GZ} {ox : ℚ} (hg : g.InPoly n Φ ox) {q : LP} {k d : ℕ}
    (hq : tquadB g q k d = true) {p : Point}
    (h : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (g.vtx ox (Hr n Φ) k)) :
    p ∈ quadSet (q.real ox (Hr n Φ)) d := by
  simp only [tquadB, Bool.and_eq_true, decide_eq_true_eq] at hq
  obtain ⟨⟨hk0, hk⟩, hq⟩ := hq
  set M := (g.t.inst (paramH n Φ) (ox + g.δ)).map ratPoint with hM
  have hML : M.length = g.t.pts.length := by simp [hM, ITmpl.inst]
  obtain ⟨i, hi, h1, h2, h3⟩ := vtx_triple_of_infix (GZ.infix hg) hk0 (by rw [hML]; exact hk)
  have hget : ∀ j (hj : j < M.length), M[j] = (tpt g.t g.δ (g.t.pts.getD j 0)).real ox (Hr n Φ) := by
    intro j hj
    have hj' : j < g.t.pts.length := by rw [← hML]; exact hj
    simp only [hM, ITmpl.inst, List.getElem_map, List.getD_eq_getElem _ _ hj']
    rw [Hr, tpt_real]
  rw [hget _ (by omega)] at h1
  rw [hget _ (by omega)] at h2
  rw [hget _ (by omega)] at h3
  exact ArtGallery.Orthogonal.Hard.sees_quad (simpleO n Φ) (interiorLeftO n Φ) hi (Hr_ge n Φ) hq h1 h2 h3 h

/-! ### Helpers -/

/-- The default group zone. -/
def GZ.dflt : GZ := ⟨⟨1, []⟩, false, 0⟩

/-- The frame point of the vertex `t.2.1` of zone `t.1` of a group. -/
def tipLP (gs : List GZ) (t : ℕ × ℕ × ℕ) : LP :=
  tpt (gs.getD t.1 GZ.dflt).t (gs.getD t.1 GZ.dflt).δ ((gs.getD t.1 GZ.dflt).t.pts.getD t.2.1 0)

/-- **Helper corner data** `(owner, q, tips)`: the spot of the helper `owner` is `{q}`; the four tips
(zone, vertex, direction) are convex corners whose cones lie in the four half-planes at `q`;
each tip is the counting witness of the owner or the target of one of its pins. -/
def hqB (gs : List GZ) (Ws : List WCert) (Ps : List PinT) (sps : List LR)
    (hq : ℕ × LP × List (ℕ × ℕ × ℕ)) : Bool :=
  decide (sps.getD hq.1 LR.dflt = hq.2.1.rect) &&
  [0, 1, 2, 3].all (fun d => hq.2.2.any fun t => t.2.2 == d) &&
  hq.2.2.all fun t => tquadB (gs.getD t.1 GZ.dflt) hq.2.1 t.2.1 t.2.2 &&
    (decide ((Ws.getD hq.1 WCert.dflt).a = tipLP gs t) ||
      Ps.any fun P => decide (P.owner = hq.1) && decide (P.T.A = (tipLP gs t).rect))

variable {n : ℕ} {Φ : List Constraint}

theorem tipLP_real (gs : List GZ) (t : ℕ × ℕ × ℕ) (ox H : ℝ) :
    (tipLP gs t).real ox H = (gs.getD t.1 GZ.dflt).vtx ox H t.2.1 := rfl

/-- **A point seeing the four arm tips of a helper is its point `q`.** -/
theorem helper_spot {gs : List GZ} {Ws : List WCert} {Ps : List PinT} {sps : List LR}
    {hq : ℕ × LP × List (ℕ × ℕ × ℕ)} (h : hqB gs Ws Ps sps hq = true) {ox : ℚ}
    (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) (hz : ∀ t ∈ hq.2.2, t.1 < gs.length) {p : Point}
    (hs : ∀ t ∈ hq.2.2, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p
      ((tipLP gs t).real ox (Hr n Φ))) :
    p = hq.2.1.real ox (Hr n Φ) := by
  simp only [hqB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, hdirs⟩, htips⟩ := h
  have hd : ∀ d ∈ [0, 1, 2, 3], p ∈ quadSet (hq.2.1.real ox (Hr n Φ)) d := by
    intro d hdm
    obtain ⟨t, ht, rfl⟩ := hdirs d hdm
    have hq' := (htips t ht).1
    have hzt := hz t ht
    have hg : (gs.getD t.1 GZ.dflt).InPoly n Φ ox := by
      rw [List.getD_eq_getElem _ _ hzt]; exact hgs _ (List.getElem_mem hzt)
    exact GZ.sees_quad hg hq' (hs t ht)
  exact eq_of_quads (hd 0 (by simp)) (hd 1 (by simp)) (hd 2 (by simp)) (hd 3 (by simp))

end

end ArtGallery.Orthogonal.Hard
