module

public import ArtGallery.Orthogonal.Hard.CertsVar
public import ArtGallery.Orthogonal.Hard.CertsBasin
public import ArtGallery.Orthogonal.Hard.CertsInvGe
public import ArtGallery.Orthogonal.Hard.CertsInvRevLe
public import ArtGallery.Orthogonal.Hard.CertsAddLe
public import ArtGallery.Orthogonal.Hard.CertsAddGe
public import ArtGallery.Orthogonal.Hard.StripO

/-!
# The template groups in the polygon

The counting witnesses of the template groups (variables, slots of each kind, basin), their
certificates (generated files `Certs*.lean`), the facts that the zones of every group instance
are zones of the polygon (`varZ_in`, `slotZ_in`, `basinZ_in`), that witnesses are vertices of the
polygon (`vtxB`), and that the viewers of a group instance lie in a vertical strip around its
origin (`groupExtB`, `group_viewer_x`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-! ### Slot groups by kind -/

/-- The counting witnesses of a slot of kind `k`. -/
def slotWs : TKind → List WCert
  | .invGe => gInvGeWs
  | .invRevLe => gInvRevLeWs
  | .addLe => gAddLeWs
  | .addGe => gAddGeWs

/-- The separation trees of a slot of kind `k`. -/
def slotTs : TKind → List ((ℕ × ℕ) × SepT)
  | .invGe => gInvGeTs
  | .invRevLe => gInvRevLeTs
  | .addLe => gAddLeTs
  | .addGe => gAddGeTs

theorem slot_ok (k : TKind) : groupOK (slotZ k) (slotWs k) (slotTs k) = true := by
  cases k
  · exact gInvGe_ok
  · exact gInvRevLe_ok
  · exact gAddLe_ok
  · exact gAddGe_ok

/-! ### Extents and vertices -/

/-- Every box and every slab of the group lies in `[x₀, x₁]`. -/
def groupExtB (gs : List GZ) (Ws : List WCert) (x0 x1 : ℚ) : Bool :=
  gs.all (fun g => match g.box.x0, g.box.x1 with
    | some a, some b => decide (x0 ≤ a ∧ b ≤ x1)
    | _, _ => false) &&
  Ws.all (fun W => W.C.isNone || decide (x0 ≤ W.slab.1 ∧ W.slab.2 ≤ x1))

/-- The target of every witness is a vertex of a template of the group. -/
def vtxB (gs : List GZ) (W : WCert) : Bool :=
  gs.any fun g => g.t.pts.any fun p =>
    decide (W.a = (g.δ + (p.1 : ℚ) / g.t.D, ((p.2.1 : ℚ) / g.t.D, -((p.2.2 : ℚ) / g.t.D))))

theorem var_ext : (groupExtB varZ gVarWs (-4) 4 && gVarWs.all (vtxB varZ)) = true := by
  decide +kernel

theorem basin_ext : (groupExtB basinZ gBasinWs 0 40 && gBasinWs.all (vtxB basinZ)) = true := by
  decide +kernel

theorem slot_ext (k : TKind) :
    (groupExtB (slotZ k) (slotWs k) (-460) 560 && (slotWs k).all (vtxB (slotZ k))) = true := by
  cases k <;> decide +kernel

variable {n : ℕ} {Φ : List Constraint}

/-- **The viewers of a witness of a group lie in the strip of the group.** -/
theorem group_viewer_x {gs : List GZ} {Ws : List WCert} {Ts : List ((ℕ × ℕ) × SepT)}
    (h : groupOK gs Ws Ts = true) {x0 x1 : ℚ} (he : groupExtB gs Ws x0 x1 = true) {ox : ℚ}
    (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) {W : WCert} (hW : W ∈ Ws) {p : Point}
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (W.a.real ox (Hr n Φ)) p) :
    (ox : ℝ) + x0 < p.1 ∧ p.1 < (ox : ℝ) + x1 := by
  simp only [groupExtB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none,
    decide_eq_true_eq] at he
  rcases group_viewer h hgs (strip_bound n Φ) hW hs with ⟨U, hU, hpU⟩ | ⟨hC, h1, h2⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hU
    have hb := he.1 g hg
    obtain ⟨hx0, hx1, -, -⟩ := hpU
    revert hb hx0 hx1
    cases g.box.x0 with
    | none => intro hb; simp at hb
    | some a =>
      cases g.box.x1 with
      | none => intro hb; simp at hb
      | some b =>
        intro hb hx0 hx1
        simp only [decide_eq_true_eq] at hb
        have h0 := hx0 a rfl; have h1 := hx1 b rfl
        have : (x0 : ℝ) ≤ a := by exact_mod_cast hb.1
        have : (b : ℝ) ≤ x1 := by exact_mod_cast hb.2
        constructor <;> linarith
  · rcases he.2 W hW with h' | h'
    · exact absurd h' hC
    · have : (x0 : ℝ) ≤ W.slab.1 := by exact_mod_cast h'.1
      have : (W.slab.2 : ℝ) ≤ x1 := by exact_mod_cast h'.2
      constructor <;> linarith

/-! ### Group instances in the polygon -/

theorem varZ_in {k : ℕ} (hk : k < n) : ∀ g ∈ varZ, g.InPoly n Φ (varA Φ k) := by
  intro g hg
  simp only [varZ, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · refine ⟨mem_allCeilTmpls_var ht, ?_⟩
    simp only [add_zero, zcO, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_reverse,
      List.mem_range]
    exact Or.inl (Or.inr ⟨k, hk, t, ht, rfl⟩)
  · refine ⟨mem_allFloorTmpls_var ht, ?_⟩
    simp only [add_zero, zfO, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
      List.mem_singleton]
    exact Or.inl (Or.inr ⟨k, hk, t, ht, rfl⟩)

theorem basinZ_in : ∀ g ∈ basinZ, g.InPoly n Φ (xL n Φ) := by
  intro g hg
  simp only [basinZ, List.mem_singleton] at hg
  subst hg
  refine ⟨List.mem_cons_self, ?_⟩
  simp [zfO]

theorem slotZ_in {c : ℕ} (hc : c < paramC Φ) :
    ∀ g ∈ slotZ (cKind (gadAt Φ c)), g.InPoly n Φ (slotG n Φ c) := by
  intro g hg
  simp only [slotZ, List.mem_append, List.mem_map, List.mem_flatMap] at hg
  rcases hg with ⟨t, ht, rfl⟩ | ⟨inp, hinp, t, ht, rfl⟩
  · refine ⟨mem_allFloorTmpls_slot ht, ?_⟩
    simp only [add_zero, zfO, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inr ⟨c, hc, t, ht, rfl⟩
  · refine ⟨mem_allCeilTmpls_input ht, ?_⟩
    simp only [zcO, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_reverse]
    refine Or.inl (Or.inl ⟨⟨(slotG n Φ c : ℚ) + inp.lx, inp.pos, (cVars (gadAt Φ c)).getD inp.role 0,
      inp.ge, c, inp.role⟩, ?_, t, ht, rfl⟩)
    simp only [inputsO, slotInputsO, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨c, hc, inp, hinp, rfl⟩

/-- A vertex of a polygon lies on its boundary. -/
theorem vtx_mem_boundary (P : Polygon) {j : ℕ} (hj : j < P.n) : P.vtx j ∈ P.boundary :=
  ⟨j, hj, 0, le_rfl, zero_le_one, by simp [Polygon.edge, lerp]⟩

theorem mem_vertices_boundary {P : Polygon} {v : Point} (hv : v ∈ P.vertices) : v ∈ P.boundary := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have := vtx_mem_boundary P (j := j) hj
  unfold Polygon.vtx at this
  rwa [List.getD_eq_getElem _ _ hj] at this

/-- **A witness passing `vtxB` is a boundary point of the polygon.** -/
theorem witness_boundary {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) {W : WCert}
    (hv : vtxB gs W = true) :
    W.a.real ox (Hr n Φ) ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  simp only [vtxB, List.any_eq_true, decide_eq_true_eq] at hv
  obtain ⟨g, hg, p, hp, hWa⟩ := hv
  have hin := hgs g hg
  set q : ℚ × ℚ := (ox + g.δ + (p.1 : ℚ) / g.t.D, (p.2.1 : ℚ) / g.t.D - (p.2.2 : ℚ) / g.t.D * paramH n Φ)
    with hq
  have hqi : q ∈ g.t.inst (paramH n Φ) (ox + g.δ) := List.mem_map.2 ⟨p, hp, rfl⟩
  have hreal : W.a.real ox (Hr n Φ) = ratPoint q := by
    rw [hWa]; simp only [LP.real, AH.ev, ratPoint, hq, Hr]; push_cast; ext <;> simp <;> ring
  rw [hreal]
  refine mem_vertices_boundary ?_
  show ratPoint q ∈ (polyO n Φ).map ratPoint
  unfold GZ.InPoly at hin
  cases hc : g.ceil
  · rw [hc] at hin
    simp only [Bool.false_eq_true, ↓reduceIte] at hin
    have hmem : (fzone g.t (paramH n Φ) (ox + g.δ)).f ∈ (zfO n Φ).map FZone.f := List.mem_map_of_mem hin.2
    rw [zfO_f] at hmem
    obtain ⟨F, hF, hFe⟩ := List.mem_map.1 hmem
    rw [fzone_f hin.1] at hFe
    have : ratPoint q ∈ F.map ratPoint := by rw [hFe]; exact List.mem_map_of_mem hqi
    obtain ⟨q', hq', hqq⟩ := List.mem_map.1 this
    rw [← hqq]
    refine List.mem_map_of_mem ?_
    simp only [polyO, List.mem_append, List.mem_flatten]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨F, hF, hq'⟩)))
  · rw [hc] at hin
    simp only [↓reduceIte] at hin
    have hmem : (czone g.t (paramH n Φ) (ox + g.δ)).f ∈ (zcO n Φ).map FZone.f := List.mem_map_of_mem hin.2
    rw [zcO_f] at hmem
    obtain ⟨F', hF', hFe⟩ := List.mem_map.1 hmem
    obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hF'
    rw [czone_f hin.1] at hFe
    have hinj : Function.Injective (List.map (fun q : Point => -q)) :=
      List.map_injective_iff.2 neg_injective
    have hFe' := hinj hFe
    have : ratPoint q ∈ F.map ratPoint := by rw [hFe']; exact List.mem_map_of_mem hqi
    obtain ⟨q', hq', hqq⟩ := List.mem_map.1 this
    rw [← hqq]
    refine List.mem_map_of_mem ?_
    simp only [polyO, List.mem_append, List.mem_flatten]
    exact Or.inl (Or.inr ⟨F, hF, hq'⟩)

end

end ArtGallery.Orthogonal.Hard
