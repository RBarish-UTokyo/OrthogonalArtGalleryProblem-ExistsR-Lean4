module

public import ArtGallery.Orthogonal.Hard.SpotGen

/-!
# Spots of the template witnesses

Every witness `i` of a template group gets the spot `sps[i]` (a frame rectangle), justified by
one of three decidable data checks (`SpotK`, `spotsB`, `GData.spot`):

* `seg`: a segment spot of a variable or input guard (`spotSegB`, `GData.seg_spot`);
* `helper`: the point of a helper, from the quadrants of its four arm tips (`hqB`,
  `helper_spot`);
* `box`: a box for a guard seeing its counting witness and one point pin: every piece of the
  first certificate meets every piece of the second only inside the box, up to parts outside the
  box separated by one half-plane of either cone (`boxSpotB`, `box_spot_sound`); the pin has no
  escaping cone, so a viewer of the witness through its escaping cone (outside all boxes of the
  group) sees no pin.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-! ### Parts of a rectangle outside a box -/

/-- Closed parts of `X` covering the points of `X` outside the closed box `S` (`none`: undecided). -/
def LR.outParts (X S : LR) : Option (List LR) :=
  let l : List LR := if X.x0 < S.x0 then [⟨X.x0, min X.x1 S.x0, X.y0, X.y1⟩] else []
  let r : List LR := if S.x1 < X.x1 then [⟨max X.x0 S.x1, X.x1, X.y0, X.y1⟩] else []
  let b : Option (List LR) :=
    if AH.le S.y0 X.y0 then some [] else (AH.rmin X.y1 S.y0).map fun m => [⟨X.x0, X.x1, X.y0, m⟩]
  let t : Option (List LR) :=
    if AH.le X.y1 S.y1 then some [] else (AH.rmax X.y0 S.y1).map fun m => [⟨X.x0, X.x1, m, X.y1⟩]
  match b, t with
  | some b, some t => some (l ++ r ++ b ++ t)
  | _, _ => none

theorem LR.outParts_sound {X S : LR} {ps : List LR} (h : X.outParts S = some ps) {H : ℝ}
    (hH : 1000 ≤ H) (ox : ℝ) {z : Point} (hz : z ∈ (X.real ox H).set)
    (hn : z ∉ (S.real ox H).set) : ∃ Xi ∈ ps, z ∈ (Xi.real ox H).set := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  simp only [LR.real] at hx0 hx1 hy0 hy1
  unfold LR.outParts at h
  simp only at h
  split at h
  · rename_i b t hb ht
    simp only [Option.some.injEq] at h
    subst h
    by_cases c1 : z.1 < ox + S.x0
    · have hlt : X.x0 < S.x0 := by
        by_contra hc; push Not at hc
        have : (S.x0 : ℝ) ≤ X.x0 := by exact_mod_cast hc
        linarith
      refine ⟨⟨X.x0, min X.x1 S.x0, X.y0, X.y1⟩, by simp [hlt], ?_, ?_, hy0, hy1⟩
      · exact hx0
      · simp only [LR.real]; push_cast; rw [← min_add_add_left]; exact le_min hx1 c1.le
    by_cases c2 : ox + S.x1 < z.1
    · have hlt : S.x1 < X.x1 := by
        by_contra hc; push Not at hc
        have : (X.x1 : ℝ) ≤ S.x1 := by exact_mod_cast hc
        linarith
      refine ⟨⟨max X.x0 S.x1, X.x1, X.y0, X.y1⟩, by simp [hlt], ?_, hx1, hy0, hy1⟩
      simp only [LR.real]; push_cast; rw [← max_add_add_left]; exact max_le hx0 c2.le
    push Not at c1 c2
    by_cases c3 : z.2 < S.y0.ev H
    · by_cases hs : AH.le S.y0 X.y0 = true
      · have := AH.le_sound hs hH; linarith
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hb
        obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 hb
        refine ⟨⟨X.x0, X.x1, X.y0, m⟩, by simp, hx0, hx1, hy0, ?_⟩
        exact AH.rmin_sound hm hH hy1 c3.le
    by_cases c4 : S.y1.ev H < z.2
    · by_cases hs : AH.le X.y1 S.y1 = true
      · have := AH.le_sound hs hH; linarith
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at ht
        obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 ht
        refine ⟨⟨X.x0, X.x1, m, X.y1⟩, by simp, hx0, hx1, ?_, hy1⟩
        exact AH.rmax_sound hm hH hy0 c4.le
    push Not at c3 c4
    exact absurd ⟨c1, c2, c3, c4⟩ hn
  · cases h

/-! ### Box spots -/

/-- **The box check**: every two pieces of the certificates meet inside the box `S`, up to parts
separated by one half-plane; the second certificate has no escaping cone. -/
def boxSpotB (c1 c2 : LCert) (S : LR) : Bool :=
  c2.C.isNone && c1.cs.all fun q1 => q1.2.2.isEmpty || c2.cs.all fun q2 => q2.2.2.isEmpty ||
    match q1.1.inter q2.1 with
    | none => false
    | some none => true
    | some (some X) => match X.outParts S with
      | none => false
      | some ps => ps.all fun Xi => q1.2.2.all fun K1 => q2.2.2.all fun K2 =>
          sepT c1.A K1 c2.A K2 .leaf Xi

variable {n : ℕ} {Φ : List Constraint}

/-- **Box spots**: a point seeing a target of each certificate lies in the box. -/
theorem box_spot_sound {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox)
    (hb : boxesSepB (gs.map GZ.box) = true) {T1 T2 : TCert}
    (ok1 : (T1.cert gs).ok = true) (l1 : T1.cones.length = (groupLR gs).length)
    (ok2 : (T2.cert gs).ok = true) (l2 : T2.cones.length = (groupLR gs).length) {S : LR}
    (h : boxSpotB (T1.cert gs) (T2.cert gs) S = true) {w1 w2 p : Point}
    (hw1 : w1 ∈ (T1.A.real ox (Hr n Φ)).set) (hw2 : w2 ∈ (T2.A.real ox (Hr n Φ)).set)
    (hs1 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w1 p)
    (hs2 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w2 p) : p ∈ (S.real ox (Hr n Φ)).set := by
  have hH := Hr_ge n Φ
  simp only [boxSpotB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true,
    Bool.or_eq_true, List.isEmpty_iff] at h
  obtain ⟨hC2, hcs⟩ := h
  by_contra hn
  rcases TCert.sees hgs ok2 l2 hb hw2 hs2 with ⟨q2, hq2, hp2, hc2, hU2⟩ | ⟨hC, -⟩
  · rcases TCert.sees hgs ok1 l1 hb hw1 hs1 with ⟨q1, hq1, hp1, hc1, -⟩ | ⟨-, hout⟩
    · obtain ⟨K1, hK1, hzK1⟩ := hc1
      obtain ⟨K2, hK2, hzK2⟩ := hc2
      rcases hcs q1 hq1 with he | hcs'
      · rw [he] at hK1; simp at hK1
      rcases hcs' q2 hq2 with he | hX
      · rw [he] at hK2; simp at hK2
      split at hX
      · cases hX
      · rename_i hi; exact LR.inter_empty hi hH ox hp1 hp2
      · rename_i X hi
        have hpX := LR.inter_sub hi hH ox hp1 hp2
        split at hX
        · cases hX
        · rename_i ps hps
          obtain ⟨Xi, hXi, hpXi⟩ := LR.outParts_sound hps hH ox hpX hn
          have hsep := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hX Xi hXi) K1 hK1)
            K2 hK2
          exact sepT_sound hH ox hw1 hw2 .leaf Xi hsep p hpXi hzK1 hzK2
    · have hk' : q2.2.1 < (gs.map GZ.box).length := LCert.box_lt ok2 hq2
      rw [List.getD_eq_getElem _ _ hk'] at hU2
      exact hout _ (List.getElem_mem hk') hU2
  · have : T2.C = none := hC2
    rw [this] at hC; exact absurd hC (by simp [optCone])

/-! ### The spots of a group -/

/-- The kind of spot of a witness. -/
inductive SpotK where
  | seg (xz : ℚ) (tw tn : ℕ × ℕ × ℕ) (kn a b : ℕ) (B0 B1 : AH)
  | helper (h : ℕ)
  | box (k : ℕ)

/-- The exempt pins are non-degenerate segments. -/
def exNdB (D : GData) : Bool :=
  D.Ex.all fun e => AH.lt (D.Ps.getD e.1 PinT.dflt).T.A.y0 (D.Ps.getD e.1 PinT.dflt).T.A.y1

/-- The box spot data of witness `i` with its point pin `k`. -/
def boxSpotDB (D : GData) (i k : ℕ) : Bool :=
  decide (i < D.Ws.length) && decide (k < D.Ps.length) &&
  decide ((D.Ps.getD k PinT.dflt).owner = i) && (D.Ex.find? (fun e => e.1 == k)).isNone &&
  decide ((D.Ps.getD k PinT.dflt).T.A.x0 = (D.Ps.getD k PinT.dflt).T.A.x1) &&
  AH.le (D.Ps.getD k PinT.dflt).T.A.y0 (D.Ps.getD k PinT.dflt).T.A.y1 &&
  boxSpotB ((D.Ws.getD i WCert.dflt).cert D.gs) ((D.Ps.getD k PinT.dflt).T.cert D.gs)
    (D.sps.getD i LR.dflt)

/-- The spot check of witness `i`. -/
def spotOkB (D : GData) (i : ℕ) : SpotK → Bool
  | .seg xz tw tn kn a b B0 B1 => spotSegB D i xz tw tn kn a b B0 B1 &&
      decide (D.sps.getD i LR.dflt = ⟨xz, xz, B0, B1⟩)
  | .helper h => decide (h < D.HQ.length) && decide ((D.HQ.getD h (0, (0, (0, 0)), [])).1 = i) &&
      (D.HQ.getD h (0, (0, (0, 0)), [])).2.2.all fun t => decide (t.1 < D.gs.length)
  | .box k => boxSpotDB D i k

/-- **The spot checks of a group.** -/
def spotsB (D : GData) (SK : List SpotK) : Bool :=
  decide (SK.length = D.Ws.length) && exNdB D &&
    (List.range D.Ws.length).all fun i => spotOkB D i (SK.getD i (.box 0))

theorem GData.pinSet_point {D : GData} (hex : exNdB D = true) {k : ℕ}
    (hA : (D.Ps.getD k PinT.dflt).T.A.y0 = (D.Ps.getD k PinT.dflt).T.A.y1) (ox H : ℝ) :
    D.pinSet ox H k = ((D.Ps.getD k PinT.dflt).T.A.real ox H).set := by
  unfold GData.pinSet
  split
  · rfl
  · rename_i e hfind
    exfalso
    have he := List.mem_of_find?_eq_some hfind
    have hk := List.find?_some hfind
    simp only [beq_iff_eq] at hk
    simp only [exNdB, List.all_eq_true] at hex
    have := hex e he
    rw [hk, hA] at this
    simp [AH.lt, AH.pos] at this

/-- **The spot of a template witness.** -/
theorem GData.spot {D : GData} (hD : D.Valid) {ox : ℚ} (hgs : ∀ g ∈ D.gs, g.InPoly n Φ ox)
    {SK : List SpotK} (hS : spotsB D SK = true) {i : ℕ} (hi : i < D.Ws.length) {p : Point}
    (hp : p ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (hall : ∀ w ∈ D.W ox (Hr n Φ) i, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p w) :
    p ∈ ((D.sps.getD i LR.dflt).real ox (Hr n Φ)).set := by
  have hH := Hr_ge n Φ
  simp only [spotsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hS
  obtain ⟨⟨-, hex⟩, hall'⟩ := hS
  have hk := hall' i hi
  generalize SK.getD i (.box 0) = sk at hk
  cases sk with
  | seg xz tw tn kn a b B0 B1 =>
    simp only [spotOkB, Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨hseg, hsp⟩ := hk
    obtain ⟨hx, h0, h1⟩ := GData.seg_spot hD hgs hseg hp hall
    rw [hsp]
    refine ⟨?_, ?_, h0, h1⟩ <;> simp only [LR.real] <;> rw [hx]
  | helper h =>
    simp only [spotOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hk
    obtain ⟨⟨hh, hown⟩, hz⟩ := hk
    set hq := D.HQ.getD h (0, (0, (0, 0)), []) with hhq
    have hqm : hq ∈ D.HQ := by rw [hhq, List.getD_eq_getElem _ _ hh]; exact List.getElem_mem hh
    have hqb := List.all_eq_true.1 hD.hq hq hqm
    have hqB' := hqb
    simp only [hqB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
      Bool.or_eq_true] at hqB'
    obtain ⟨⟨hsps, -⟩, htips⟩ := hqB'
    have hpq := helper_spot hqb hgs hz (p := p) fun t ht => by
      rcases (htips t ht).2 with hW | ⟨P, hP, hPo, hPA⟩
      · rw [hown] at hW
        rw [← hW]; exact hall _ (Or.inl rfl)
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hP
        have hgk : D.Ps.getD k PinT.dflt = D.Ps[k] := List.getD_eq_getElem _ _ hk
        refine hall _ (Or.inr ⟨k, hk, by rw [hgk, hPo, hown], ?_⟩)
        rw [GData.pinSet_point hex (by rw [hgk, hPA]; rfl), hgk, hPA]
        exact LP.rect_mem _ _ _
    rw [← hown, hsps, hpq]
    exact LP.rect_mem _ _ _
  | box k =>
    simp only [spotOkB, boxSpotDB, Bool.and_eq_true, decide_eq_true_eq,
      Option.isNone_iff_eq_none] at hk
    obtain ⟨⟨⟨⟨⟨⟨-, hkl⟩, hown⟩, hnone⟩, hAx⟩, hAy⟩, hbox⟩ := hk
    have hparts := groupOK_parts hD.group
    have hWm : D.Ws.getD i WCert.dflt ∈ D.Ws := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    obtain ⟨ok1, l1, -⟩ := hparts.2.1 _ hWm
    have hPm : D.Ps.getD k PinT.dflt ∈ D.Ps := by
      rw [List.getD_eq_getElem _ _ hkl]; exact List.getElem_mem hkl
    obtain ⟨ok2, l2, -, -⟩ := pinB_parts (hD.pins _ hPm)
    have hw2 : (((ox : ℝ) + (D.Ps.getD k PinT.dflt).T.A.x0,
        (D.Ps.getD k PinT.dflt).T.A.y0.ev (Hr n Φ)) : Point) ∈
        ((D.Ps.getD k PinT.dflt).T.A.real ox (Hr n Φ)).set := by
      refine ⟨le_rfl, ?_, le_rfl, AH.le_sound hAy hH⟩
      simp only [LR.real, hAx]; exact le_rfl
    refine box_spot_sound (T1 := (D.Ws.getD i WCert.dflt).toT) hgs hparts.1 ok1 l1 ok2 l2 hbox
      (LP.rect_mem _ _ _) hw2 (sees_symm (hall _ (Or.inl rfl)))
      (sees_symm (hall _ (Or.inr ⟨k, hkl, hown, ?_⟩)))
    unfold GData.pinSet
    rw [hnone]
    exact hw2

end

end ArtGallery.Orthogonal.Hard
