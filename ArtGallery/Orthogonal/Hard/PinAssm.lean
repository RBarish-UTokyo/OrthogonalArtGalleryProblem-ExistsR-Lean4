module

public import ArtGallery.Orthogonal.Hard.SpotO
public import ArtGallery.Orthogonal.Hard.GroupsO

/-!
# Pin data of a template group

`GData` collects the generated data of a template group: zones, counting witnesses, separation
trees, pin targets, pin ranks and spots, helper corner data, the exterior boxes of the exempt
pins (cutter segments next to their tips) and the boundary edges carrying the pins.  `GData.Valid`
gathers the checks.  For a valid group in the polygon:

* `GData.excl`: a viewer of another witness of the group (inside that witness's spot when it is
  pinned earlier) sees no point of the pin set of a witness;
* `GData.pin_bd`: the pin sets lie on the boundary;
* `GData.pin_x`: the viewers of the pin sets lie in the strip of the group.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-- The pin data of a template group. -/
structure GData where
  gs : List GZ
  Ws : List WCert
  Ts : List ((ℕ × ℕ) × SepT)
  Ps : List PinT
  rks : List ℕ
  sps : List LR
  HQ : List (ℕ × LP × List (ℕ × ℕ × ℕ))
  /-- Exempt pins: pin index, exterior box, `true` if the box lies left of the wall. -/
  Ex : List (ℕ × FBox × Bool)
  /-- Per pin: zone and vertex index `k` such that the pin lies on the edge `k → k + 1`. -/
  Bd : List (ℕ × ℕ)
  x0 : ℚ
  x1 : ℚ

/-- The default pin. -/
def PinT.dflt : PinT := ⟨⟨LR.dflt, 0, none, [], (0, 0)⟩, 0, [], []⟩

/-- The escaping cones of the pins lie in the extent of the group. -/
def pinExtB (Ps : List PinT) (x0 x1 : ℚ) : Bool :=
  Ps.all fun P => P.T.C.isNone || decide (x0 ≤ P.T.slab.1 ∧ P.T.slab.2 ≤ x1)

/-- The exterior data of an exempt pin. -/
def exOkB (D : GData) (k : ℕ) (E : FBox) (left : Bool) : Bool :=
  let P := D.Ps.getD k PinT.dflt
  extB D.gs E && decide (E.x0 < E.x1) &&
  decide (P.T.A.x0 = P.T.A.x1) &&
  decide (P.T.A.x0 = if left then E.x1 else E.x0) &&
  P.exempt.all fun j => decide (D.rks.getD j 0 < D.rks.getD P.owner 0) &&
    (if left then decide ((D.sps.getD j LR.dflt).x1 < P.T.A.x0)
     else decide (P.T.A.x0 < (D.sps.getD j LR.dflt).x0))

/-- Every exempt pin has its exterior data. -/
def exB (D : GData) : Bool :=
  (List.range D.Ps.length).all fun k => (D.Ps.getD k PinT.dflt).exempt.isEmpty ||
    match D.Ex.find? (fun e => e.1 == k) with
    | none => false
    | some e => exOkB D k e.2.1 e.2.2

/-- The pin `k` lies on the edge `t → t + 1` of zone `z` (a vertical edge for a segment, the
first vertex for a point). -/
def bdOkB (D : GData) (k z t : ℕ) : Bool :=
  let P := D.Ps.getD k PinT.dflt
  let g := D.gs.getD z GZ.dflt
  let u := tpt g.t g.δ (g.t.pts.getD t 0)
  let v := tpt g.t g.δ (g.t.pts.getD (t + 1) 0)
  decide (z < D.gs.length) && decide (t + 1 < g.t.pts.length) &&
  ((decide (P.T.A = u.rect)) ||
    (decide (P.T.A.x0 = u.1 ∧ P.T.A.x1 = u.1 ∧ v.1 = u.1) &&
      ((AH.le u.2 P.T.A.y0 && AH.le P.T.A.y1 v.2) || (AH.le v.2 P.T.A.y0 && AH.le P.T.A.y1 u.2))))

/-- Every pin lies on a boundary edge. -/
def bdB (D : GData) : Bool :=
  decide (D.Bd.length = D.Ps.length) &&
    (List.range D.Ps.length).all fun k => bdOkB D k (D.Bd.getD k (0, 0)).1 (D.Bd.getD k (0, 0)).2

/-- **The checks of a group.** -/
structure GData.Valid (D : GData) : Prop where
  group : groupOK D.gs D.Ws D.Ts = true
  pins : ∀ P ∈ D.Ps, pinB D.gs D.Ws D.rks D.sps P = true
  hq : D.HQ.all (hqB D.gs D.Ws D.Ps D.sps) = true
  ext : groupExtB D.gs D.Ws D.x0 D.x1 = true
  pext : pinExtB D.Ps D.x0 D.x1 = true
  ex : exB D = true
  bd : bdB D = true

/-- The pin set of the pin `k` (for an exempt pin: its points strictly inside the exterior
box's height). -/
def GData.pinSet (D : GData) (ox H : ℝ) (k : ℕ) : Set Point :=
  match D.Ex.find? (fun e => e.1 == k) with
  | none => ((D.Ps.getD k PinT.dflt).T.A.real ox H).set
  | some e => {w | w ∈ ((D.Ps.getD k PinT.dflt).T.A.real ox H).set ∧
      e.2.1.y0.ev H < w.2 ∧ w.2 < e.2.1.y1.ev H}

/-- The pin targets of witness `i`: its counting witness and the pin sets of its pins. -/
def GData.W (D : GData) (ox H : ℝ) (i : ℕ) : Set Point :=
  {(D.Ws.getD i WCert.dflt).a.real ox H} ∪
    {w | ∃ k < D.Ps.length, (D.Ps.getD k PinT.dflt).owner = i ∧ w ∈ D.pinSet ox H k}

theorem GData.pinSet_sub (D : GData) (ox H : ℝ) (k : ℕ) :
    D.pinSet ox H k ⊆ ((D.Ps.getD k PinT.dflt).T.A.real ox H).set := by
  intro w hw
  unfold GData.pinSet at hw
  split at hw
  · exact hw
  · exact hw.1

variable {n : ℕ} {Φ : List Constraint}

/-- **Exclusion inside a group.** -/
theorem GData.excl {D : GData} (hD : D.Valid) {ox : ℚ} (hgs : ∀ g ∈ D.gs, g.InPoly n Φ ox)
    {i j : ℕ} (hi : i < D.Ws.length) (hj : j < D.Ws.length) (hij : i ≠ j) {w : Point}
    (hw : w ∈ D.W ox (Hr n Φ) i) {p : Point}
    (hp : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (D.Ws[j].a.real ox (Hr n Φ)))
    (hsp : D.rks.getD j 0 < D.rks.getD i 0 → p ∈ ((D.sps.getD j LR.dflt).real ox (Hr n Φ)).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p w) : False := by
  have hY := strip_bound n Φ
  rcases hw with hw | ⟨k, hk, hown, hwk⟩
  · rw [mem_singleton_iff, List.getD_eq_getElem _ _ hi] at hw
    subst hw
    exact group_disjoint hD.group hgs hY hj hi (Ne.symm hij) hp hs
  · set P := D.Ps.getD k PinT.dflt with hPdef
    have hPm : P ∈ D.Ps := by rw [hPdef, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hPB := hD.pins P hPm
    have hwA := D.pinSet_sub _ _ k hwk
    have hjo : j ≠ P.owner := by rw [hown]; exact Ne.symm hij
    by_cases hje : j ∈ P.exempt
    · -- the exempt helper: the exterior box
      have hex := hD.ex
      simp only [exB, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.isEmpty_iff] at hex
      rcases hex k hk with he | he
      · have he' : P.exempt = [] := he
        rw [he'] at hje; simp at hje
      split at he
      · cases he
      rename_i e hfind
      have hwk' := hwk
      unfold GData.pinSet at hwk'
      rw [hfind] at hwk'
      obtain ⟨-, hy0, hy1⟩ := hwk'
      simp only [exOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at he
      obtain ⟨⟨⟨⟨hext, hlt⟩, hxx⟩, hwall⟩, hjs⟩ := he
      rw [← hPdef] at hxx hwall hjs
      obtain ⟨hr, hside⟩ := hjs j hje
      rw [hown] at hr
      have hpS := hsp hr
      obtain ⟨hx0, hx1, -, -⟩ := hwA
      obtain ⟨hpx0, hpx1, -, -⟩ := hpS
      simp only [LR.real] at hx0 hx1 hpx0 hpx1
      have hx1' : w.1 ≤ (ox : ℝ) + ((P.T.A.x1 : ℚ) : ℝ) := hx1
      have hx0' : (ox : ℝ) + ((P.T.A.x0 : ℚ) : ℝ) ≤ w.1 := hx0
      have hwx : w.1 = (ox : ℝ) + P.T.A.x0 := by
        rw [← hxx] at hx1'; linarith
      cases hl : e.2.2
      · rw [hl] at hwall hside
        simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hwall hside
        have : (P.T.A.x0 : ℝ) < (D.sps.getD j LR.dflt).x0 := by exact_mod_cast hside
        exact not_sees_of_ext_left hgs hext hlt (by rw [hwx, hwall]) hy0 hy1
          (by rw [← hwall]; linarith) hs
      · rw [hl] at hwall hside
        simp only [↓reduceIte, decide_eq_true_eq] at hwall hside
        have : ((D.sps.getD j LR.dflt).x1 : ℝ) < P.T.A.x0 := by exact_mod_cast hside
        exact not_sees_of_ext_right hgs hext hlt (by rw [hwx, hwall]) hy0 hy1
          (by rw [← hwall]; linarith) hs
    · by_cases hr : D.rks.getD j 0 < D.rks.getD i 0
      · rw [← hown] at hr
        exact pinB_early hPB (groupOK_parts hD.group).1 hgs hj hjo hje hr hwA (hsp (by rw [hown] at hr; exact hr))
          (sees_symm hs)
      · rw [← hown] at hr
        exact pinB_late hPB hD.group hgs hY hj hjo hje hr hwA (sees_symm hs) (sees_symm hp)

/-- A point of a vertical segment between two points lies on it. -/
theorem mem_segment_vert' {x ya yb y : ℝ} (h : (ya ≤ y ∧ y ≤ yb) ∨ (yb ≤ y ∧ y ≤ ya)) :
    ((x, y) : Point) ∈ ArtGallery.segment (x, ya) (x, yb) := by
  rcases eq_or_ne ya yb with he | he
  · subst he
    refine ⟨0, le_rfl, zero_le_one, ?_⟩
    rcases h with h | h <;> (ext <;> simp <;> linarith [h.1, h.2])
  · refine ⟨(y - ya) / (yb - ya), ?_, ?_, ?_⟩
    · rcases h with h | h
      · exact div_nonneg (by linarith) (by rcases lt_or_gt_of_ne he with h' | h' <;> [linarith; (exfalso; linarith)])
      · exact div_nonneg_of_nonpos (by linarith) (by rcases lt_or_gt_of_ne he with h' | h' <;> [(exfalso; linarith); linarith])
    · rcases h with h | h
      · rw [div_le_one (by rcases lt_or_gt_of_ne he with h' | h' <;> [linarith; (exfalso; linarith)])]; linarith
      · rw [div_le_one_of_neg (by rcases lt_or_gt_of_ne he with h' | h' <;> [(exfalso; linarith); linarith])]; linarith
    · have : yb - ya ≠ 0 := sub_ne_zero.2 (Ne.symm he)
      ext <;> simp <;> field_simp <;> ring

/-- **The pin sets lie on the boundary.** -/
theorem GData.pin_bd {D : GData} (hD : D.Valid) {ox : ℚ} (hgs : ∀ g ∈ D.gs, g.InPoly n Φ ox)
    {k : ℕ} (hk : k < D.Ps.length) {w : Point} (hw : w ∈ D.pinSet ox (Hr n Φ) k) :
    w ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  have hH := Hr_ge n Φ
  have hb := hD.bd
  simp only [bdB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hb
  have hbk := hb.2 k hk
  set z := (D.Bd.getD k (0, 0)).1
  set t := (D.Bd.getD k (0, 0)).2
  simp only [bdOkB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hbk
  obtain ⟨⟨hz, ht⟩, hcase⟩ := hbk
  set g := D.gs.getD z GZ.dflt with hg
  have hgin : g.InPoly n Φ ox := by
    rw [hg, List.getD_eq_getElem _ _ hz]; exact hgs _ (List.getElem_mem hz)
  set M := (g.t.inst (paramH n Φ) (ox + g.δ)).map ratPoint with hM
  have hML : M.length = g.t.pts.length := by simp [hM, ITmpl.inst]
  have hget : ∀ j (hj : j < M.length), M[j] = (tpt g.t g.δ (g.t.pts.getD j 0)).real ox (Hr n Φ) := by
    intro j hj
    have hj' : j < g.t.pts.length := by rw [← hML]; exact hj
    simp only [hM, ITmpl.inst, List.getElem_map, List.getD_eq_getElem _ _ hj']
    rw [Hr, tpt_real]
  have hseg := seg_subset_boundary (GZ.infix hgin) (j := t) (by rw [hML]; exact ht)
  rw [hget t (by omega), hget (t + 1) (by rw [hML]; exact ht)] at hseg
  apply hseg
  have hwA := D.pinSet_sub _ _ k hw
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hwA
  simp only [LR.real] at hx0 hx1 hy0 hy1
  rcases hcase with he | ⟨⟨e0, e1, e2⟩, hy⟩
  · rw [he] at hx0 hx1 hy0 hy1
    simp only [LP.rect] at hx0 hx1 hy0 hy1
    have : w = (tpt g.t g.δ (g.t.pts.getD t 0)).real ox (Hr n Φ) := by
      simp only [LP.real]; ext <;> simp only <;> linarith
    rw [this]; exact ⟨0, le_rfl, zero_le_one, by ext <;> simp⟩
  · set u := tpt g.t g.δ (g.t.pts.getD t 0)
    set v := tpt g.t g.δ (g.t.pts.getD (t + 1) 0)
    have hwx : w.1 = (ox : ℝ) + (u.1 : ℝ) := by rw [e0] at hx0; rw [e1] at hx1; linarith
    have hw' : w = ((ox : ℝ) + (u.1 : ℝ), w.2) := Prod.ext hwx rfl
    have hu : u.real ox (Hr n Φ) = ((ox : ℝ) + (u.1 : ℝ), u.2.ev (Hr n Φ)) := rfl
    have hv : v.real ox (Hr n Φ) = ((ox : ℝ) + (u.1 : ℝ), v.2.ev (Hr n Φ)) := by
      simp only [LP.real, e2]
    rw [hu, hv, hw']
    apply mem_segment_vert'
    rcases hy with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · left; exact ⟨(AH.le_sound a1 hH).trans hy0, hy1.trans (AH.le_sound a2 hH)⟩
    · right; exact ⟨(AH.le_sound a1 hH).trans hy0, hy1.trans (AH.le_sound a2 hH)⟩

/-- **The viewers of the pin sets lie in the strip of the group.** -/
theorem GData.pin_x {D : GData} (hD : D.Valid) {ox : ℚ} (hgs : ∀ g ∈ D.gs, g.InPoly n Φ ox)
    {k : ℕ} (hk : k < D.Ps.length) {w p : Point} (hw : w ∈ D.pinSet ox (Hr n Φ) k)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p) :
    (ox : ℝ) + D.x0 < p.1 ∧ p.1 < (ox : ℝ) + D.x1 := by
  have hH := Hr_ge n Φ
  set P := D.Ps.getD k PinT.dflt with hPdef
  have hPm : P ∈ D.Ps := by rw [hPdef, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  obtain ⟨ok, l, sl, -⟩ := pinB_parts (hD.pins P hPm)
  have hb := (groupOK_parts hD.group).1
  have he := hD.ext
  simp only [groupExtB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Option.isNone_iff_eq_none, decide_eq_true_eq] at he
  rcases TCert.sees hgs ok l hb (D.pinSet_sub _ _ k hw) hs with ⟨q, hq, -, -, hpU⟩ | ⟨hC, -⟩
  · have hk' : q.2.1 < (D.gs.map GZ.box).length := LCert.box_lt ok hq
    have hpU' : p ∈ ((D.gs.map GZ.box).getD q.2.1 LBox.default).set ox (Hr n Φ) := hpU
    rw [List.getD_eq_getElem _ _ hk', List.getElem_map] at hpU'
    have hk'' : q.2.1 < D.gs.length := by simpa using hk'
    have hgm : D.gs[q.2.1] ∈ D.gs := List.getElem_mem hk''
    have hbx := he.1 _ hgm
    obtain ⟨hx0, hx1, -, -⟩ := hpU'
    revert hbx hx0 hx1
    cases (D.gs[q.2.1]).box.x0 with
    | none => intro hbx; simp at hbx
    | some a =>
      cases (D.gs[q.2.1]).box.x1 with
      | none => intro hbx; simp at hbx
      | some b =>
        intro hbx hx0 hx1
        simp only [decide_eq_true_eq] at hbx
        have h0 := hx0 a rfl; have h1 := hx1 b rfl
        have : (D.x0 : ℝ) ≤ a := by exact_mod_cast hbx.1
        have : (b : ℝ) ≤ D.x1 := by exact_mod_cast hbx.2
        constructor <;> linarith
  · have hY := strip_bound n Φ p (mem_filled_of_sees hs)
    have hpe := hD.pext
    simp only [pinExtB, List.all_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none,
      decide_eq_true_eq] at hpe
    cases hTC : P.T.C with
    | none => rw [hTC] at hC; exact absurd hC (by simp [optCone])
    | some K =>
      rw [hTC] at hC
      rcases hpe P hPm with h | h
      · rw [hTC] at h; cases h
      simp only [TCert.slabB, hTC, Bool.and_eq_true] at sl
      have a1 := rightOfBA_sound sl.1 hH ox (D.pinSet_sub _ _ k hw) hC hY.1 hY.2
      have a2 := leftOfBA_sound sl.2 hH ox (D.pinSet_sub _ _ k hw) hC hY.1 hY.2
      have : (D.x0 : ℝ) ≤ P.T.slab.1 := by exact_mod_cast h.1
      have : (P.T.slab.2 : ℝ) ≤ D.x1 := by exact_mod_cast h.2
      constructor <;> linarith

end

end ArtGallery.Orthogonal.Hard
