module

public import ArtGallery.Orthogonal.Hard.CertZone

/-!
# Counting certificates of a template group

A *template group* is a list of template zones in one frame (`GZ`).  Its counting witnesses come
with certificates (`WCert`): the target point, the box containing it, the escape cone `C` (for
witnesses whose viewers leave the zones: the W1 tips, the aux corridor) with the `x`-interval
(`slab`) containing the escaping viewers, and the cones of the group rectangles.

`groupOK` checks: the boxes are separated, every certificate is valid, every escaping cone lies in
its slab within the strip `−5H ≤ y ≤ 3H` (which contains the region), the pieces of any two
certificates are disjoint, and so are the escaping parts of any two certificates.

`group_sound`: every viewer of a witness lies in the boxes of the group or in its slab, and no point
of the region sees two witnesses of the group.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-! ### Cones in a vertical strip -/

/-- The coefficient of `z.1` in `det(u, v, z)` with the target at `a`. -/
def hpCoefX (a : LP) (h : HP) : AH :=
  (-((h.2.getD a).2.1 - (h.1.getD a).2.1), -((h.2.getD a).2.2 - (h.1.getD a).2.2))

/-- The degenerate rectangle of a point. -/
def LP.rect (a : LP) : LR := ⟨a.1, a.1, a.2, a.2⟩

theorem LP.mem_rect (ox H : ℝ) (a : LP) : a.real ox H ∈ (a.rect.real ox H).set := by
  simp only [LP.rect, LR.real, LP.real, Rect.set, mem_ofPred_eq]; exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- The cone (target `a`) lies strictly left of `x = xr` in the strip `ylo ≤ y ≤ yhi`. -/
def leftOfB (a : LP) (K : List HP) (xr : ℚ) (ylo yhi : AH) : Bool :=
  K.any fun h => AH.nn (-(hpCoefX a h).1, -(hpCoefX a h).2) && hpNeg a.rect h [(xr, ylo), (xr, yhi)]

/-- The cone (target `a`) lies strictly right of `x = xl` in the strip `ylo ≤ y ≤ yhi`. -/
def rightOfB (a : LP) (K : List HP) (xl : ℚ) (ylo yhi : AH) : Bool :=
  K.any fun h => (hpCoefX a h).nn && hpNeg a.rect h [(xl, ylo), (xl, yhi)]

theorem det_shift_x (u v z : Point) (x : ℝ) :
    det u v z = det u v (x, z.2) + (-(v.2 - u.2)) * (z.1 - x) := by
  simp only [det]; ring

theorem hpCoefX_ev (ox H : ℝ) (a : LP) (h : HP) :
    -((h.2.pt ox H (a.real ox H)).2 - (h.1.pt ox H (a.real ox H)).2) = (hpCoefX a h).ev H := by
  rw [HE.pt_real, HE.pt_real]
  simp only [hpCoefX, LP.real, AH.ev]; push_cast; ring

/-- The two corners of a vertical side, as a degenerate rectangle. -/
theorem side_mem {ox H : ℝ} {x : ℚ} {ylo yhi : AH} {y : ℝ} (h1 : ylo.ev H ≤ y) (h2 : y ≤ yhi.ev H) :
    ((ox + x, y) : Point) ∈ (LR.real ox H ⟨x, x, ylo, yhi⟩).set :=
  ⟨le_rfl, le_rfl, h1, h2⟩

theorem hpNeg_side {A : LR} {h : HP} {x : ℚ} {ylo yhi : AH}
    (hh : hpNeg A h [(x, ylo), (x, yhi)] = true) : hpNeg A h (LR.corners ⟨x, x, ylo, yhi⟩) = true := by
  simp only [hpNeg, List.all_eq_true, LR.corners, List.mem_cons, List.not_mem_nil, or_false] at hh ⊢
  intro a ha c hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact hh a ha _ (Or.inl rfl)
  · exact hh a ha _ (Or.inl rfl)
  · exact hh a ha _ (Or.inr rfl)
  · exact hh a ha _ (Or.inr rfl)

theorem leftOfB_sound {a : LP} {K : List HP} {xr : ℚ} {ylo yhi : AH}
    (h : leftOfB a K xr ylo yhi = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ) {z : Point}
    (hz : z ∈ cone ox H (a.real ox H) K) (h1 : ylo.ev H ≤ z.2) (h2 : z.2 ≤ yhi.ev H) :
    z.1 < ox + xr := by
  simp only [leftOfB, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨hp, hpK, hc, hn⟩ := h
  by_contra hx
  push Not at hx
  have hzh : 0 ≤ det (hp.1.pt ox H (a.real ox H)) (hp.2.pt ox H (a.real ox H)) z := hz hp hpK
  have hneg := hpNeg_sound (hpNeg_side hn) hH ox (LP.mem_rect ox H a) (side_mem (ox := ox) h1 h2)
  have hneg' : det (hp.1.pt ox H (a.real ox H)) (hp.2.pt ox H (a.real ox H)) (ox + xr, z.2) < 0 := by
    by_contra hc'; push Not at hc'; exact hneg hc'
  have hcoef := AH.nn_sound hc hH
  have he := hpCoefX_ev ox H a hp
  rw [det_shift_x _ _ z (ox + xr)] at hzh
  simp only [AH.ev] at hcoef he
  push_cast at hcoef
  have : (hpCoefX a hp).ev H ≤ 0 := by simp only [AH.ev]; linarith
  rw [he] at hzh
  nlinarith

theorem rightOfB_sound {a : LP} {K : List HP} {xl : ℚ} {ylo yhi : AH}
    (h : rightOfB a K xl ylo yhi = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ) {z : Point}
    (hz : z ∈ cone ox H (a.real ox H) K) (h1 : ylo.ev H ≤ z.2) (h2 : z.2 ≤ yhi.ev H) :
    ox + xl < z.1 := by
  simp only [rightOfB, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨hp, hpK, hc, hn⟩ := h
  by_contra hx
  push Not at hx
  have hzh : 0 ≤ det (hp.1.pt ox H (a.real ox H)) (hp.2.pt ox H (a.real ox H)) z := hz hp hpK
  have hneg := hpNeg_sound (hpNeg_side hn) hH ox (LP.mem_rect ox H a) (side_mem (ox := ox) h1 h2)
  have hneg' : det (hp.1.pt ox H (a.real ox H)) (hp.2.pt ox H (a.real ox H)) (ox + xl, z.2) < 0 := by
    by_contra hc'; push Not at hc'; exact hneg hc'
  have hcoef := AH.nn_sound hc hH
  have he := hpCoefX_ev ox H a hp
  rw [det_shift_x _ _ z (ox + xl)] at hzh
  rw [he] at hzh
  nlinarith

/-! ### Witness certificates of a group -/

/-- The strip `−5H ≤ y ≤ 3H` containing the region. -/
def yMin : AH := (0, -5)

/-- Top of the strip. -/
def yMax : AH := (0, 3)

/-- A counting witness of a group with its certificate data. -/
structure WCert where
  a : LP
  Ab : ℕ
  C : Option (List HP)
  cones : List (List (List HP))
  slab : ℚ × ℚ

/-- The certificate of a witness over the rectangles of a group. -/
def WCert.cert (gs : List GZ) (W : WCert) : LCert :=
  ⟨W.a.rect, W.Ab, (groupLR gs).zipWith (fun rk Ks => (rk.1, rk.2, Ks)) W.cones, W.C,
    gs.map GZ.box⟩

/-- The escaping cone lies in the slab (within the strip). -/
def WCert.slabB (W : WCert) : Bool :=
  match W.C with
  | none => true
  | some K => rightOfB W.a K W.slab.1 yMin yMax && leftOfB W.a K W.slab.2 yMin yMax

/-- A separation tree: split a rectangle at an abscissa or an ordinate; at the leaves a half-plane
of one of the two cones is strictly negative. -/
inductive SepT where
  | leaf
  | splitX (c : ℚ) (l r : SepT)
  | splitY (c : AH) (l r : SepT)

/-- Disjointness of two cones on a rectangle along a separation tree. -/
def sepT (A1 : LR) (K1 : List HP) (A2 : LR) (K2 : List HP) : SepT → LR → Bool
  | .leaf, X => K1.any (fun h => hpNegr A1 h X) || K2.any (fun h => hpNegr A2 h X)
  | .splitX c l r, X => sepT A1 K1 A2 K2 l ⟨X.x0, c, X.y0, X.y1⟩ && sepT A1 K1 A2 K2 r ⟨c, X.x1, X.y0, X.y1⟩
  | .splitY c l r, X => sepT A1 K1 A2 K2 l ⟨X.x0, X.x1, X.y0, c⟩ && sepT A1 K1 A2 K2 r ⟨X.x0, X.x1, c, X.y1⟩

theorem sepT_sound {A1 A2 : LR} {K1 K2 : List HP} {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {w1 w2 : Point} (hw1 : w1 ∈ (A1.real ox H).set) (hw2 : w2 ∈ (A2.real ox H).set) :
    ∀ (T : SepT) (X : LR), sepT A1 K1 A2 K2 T X = true → ∀ z ∈ (X.real ox H).set,
      z ∈ cone ox H w1 K1 → z ∉ cone ox H w2 K2
  | .leaf, X, h, z, hz, h1, h2 => by
    simp only [sepT, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨h, hh, hn⟩ | ⟨h, hh, hn⟩
    · exact hpNegr_sound hn hH ox hw1 hz (h1 h hh)
    · exact hpNegr_sound hn hH ox hw2 hz (h2 h hh)
  | .splitX c l r, X, h, z, hz, h1, h2 => by
    simp only [sepT, Bool.and_eq_true] at h
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
    simp only [LR.real] at hx0 hx1 hy0 hy1
    rcases le_total z.1 (ox + (c : ℝ)) with hc | hc
    · exact sepT_sound hH ox hw1 hw2 l _ h.1 z ⟨hx0, hc, hy0, hy1⟩ h1 h2
    · exact sepT_sound hH ox hw1 hw2 r _ h.2 z ⟨hc, hx1, hy0, hy1⟩ h1 h2
  | .splitY c l r, X, h, z, hz, h1, h2 => by
    simp only [sepT, Bool.and_eq_true] at h
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
    simp only [LR.real] at hx0 hx1 hy0 hy1
    rcases le_total z.2 (c.ev H) with hc | hc
    · exact sepT_sound hH ox hw1 hw2 l _ h.1 z ⟨hx0, hx1, hy0, hc⟩ h1 h2
    · exact sepT_sound hH ox hw1 hw2 r _ h.2 z ⟨hx0, hx1, hc, hy1⟩ h1 h2

/-- The escaping parts of two witnesses are disjoint (within the strip), along a tree. -/
def escSepB (T : SepT) (W1 W2 : WCert) : Bool :=
  match W1.C, W2.C with
  | some K1, some K2 =>
    decide (min W1.slab.2 W2.slab.2 ≤ max W1.slab.1 W2.slab.1) ||
      sepT W1.a.rect K1 W2.a.rect K2 T
        ⟨max W1.slab.1 W2.slab.1, min W1.slab.2 W2.slab.2, yMin, yMax⟩
  | _, _ => true

/-- The separation tree of a pair of witnesses (default: a leaf). -/
def treeOf (Ts : List ((ℕ × ℕ) × SepT)) (i j : ℕ) : SepT :=
  ((Ts.find? fun t => t.1 == (i, j)).map Prod.snd).getD .leaf

/-- **The group check.** -/
def groupOK (gs : List GZ) (Ws : List WCert) (Ts : List ((ℕ × ℕ) × SepT)) : Bool :=
  boxesSepB (gs.map GZ.box) &&
  Ws.all (fun W => (W.cert gs).ok && decide (W.cones.length = (groupLR gs).length) && W.slabB) &&
  (List.range Ws.length).all fun i => (List.range Ws.length).all fun j =>
    decide (j ≤ i) ||
      (disjB ((Ws.getD i ⟨(0, 0, 0), 0, none, [], (0, 0)⟩).cert gs)
          ((Ws.getD j ⟨(0, 0, 0), 0, none, [], (0, 0)⟩).cert gs) &&
        escSepB (treeOf Ts i j) (Ws.getD i ⟨(0, 0, 0), 0, none, [], (0, 0)⟩)
          (Ws.getD j ⟨(0, 0, 0), 0, none, [], (0, 0)⟩))

/-! ### The template groups of the construction -/

/-- The zones of the group of a variable (frame `a_k`): its ceiling zones (W1, ceiling cutter) and
its floor zones (W2, floor cutter). -/
def varZ : List GZ := oVarCeil.map (fun t => ⟨t, true, 0⟩) ++ oVarFloor.map (fun t => ⟨t, false, 0⟩)

/-- The zone of the basin of `H_L` (frame `x_L`). -/
def basinZ : List GZ := [⟨oBasin, false, 0⟩]

/-- The zones of the group of a slot of kind `k` (frame `g_c`): its floor zones and the ceiling
zones of its inputs. -/
def slotZ (k : TKind) : List GZ :=
  (oSlotFloor k).map (fun t => ⟨t, false, 0⟩) ++
    (oTmplInputs k).flatMap (fun inp => (oInputCeil inp.pos).map (fun t => ⟨t, true, inp.lx⟩))

/-! ### Soundness -/

variable {n : ℕ} {Φ : List Constraint}

/-- The rest of the region for a group: closed, outside every box, and with the group rectangles
covering the region. -/
theorem group_rest {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) :
    ∃ Rest : List (Set Point), (∀ r ∈ Rest, IsClosed r) ∧
      (∀ r ∈ Rest, ∀ z ∈ r, ∀ U ∈ gs.map GZ.box, z ∉ U.set ox (Hr n Φ)) ∧
      ∀ z ∈ RU (regionRectsO n Φ),
        (∃ rk ∈ groupLR gs, z ∈ (rk.1.real ox (Hr n Φ)).set) ∨ ∃ r ∈ Rest, z ∈ r := by
  classical
  set Rest := (regionRectsO n Φ).filter (fun r => decide (∀ g ∈ gs, r ∉ g.rects.map
    (LR.real ox (Hr n Φ)))) with hRest
  refine ⟨Rest.map Rect.set, fun r hr => ?_, fun r hr z hz U hU' hzU => ?_, fun z hz => ?_⟩
  · obtain ⟨r', -, rfl⟩ := List.mem_map.1 hr; exact isClosed_rect_set r'
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hU'
    simp only [hRest, List.mem_filter, decide_eq_true_eq] at hr'
    have hb := GZ.box_set (hgs g hg) hzU
    have hin := hgs g hg
    have hnot := hr'.2 g hg
    rw [GZ.rects_real] at hnot
    unfold GZ.InPoly at hin
    cases hcg : g.ceil
    · rw [hcg] at hin hnot hb
      simp only [Bool.false_eq_true, ↓reduceIte] at hin hnot hb
      rcases region_rect_floor hin.2 r' hr'.1 with h | h
      · exact hnot h
      · exact h z hz hb
    · rw [hcg] at hin hnot hb
      simp only [↓reduceIte] at hin hnot hb
      rcases region_rect_ceil hin.2 r' hr'.1 with h | h
      · exact hnot h
      · exact h z hz hb
  · obtain ⟨r, hr, hz⟩ := hz
    by_cases hloc : ∃ g ∈ gs, r ∈ g.rects.map (LR.real ox (Hr n Φ))
    · left
      obtain ⟨g, hg, hrg⟩ := hloc
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hrg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      refine ⟨(l, k), ?_, hz⟩
      simp only [groupLR, List.mem_flatMap, List.mem_range, List.mem_map]
      refine ⟨k, hk, l, ?_, rfl⟩
      rw [List.getD_eq_getElem _ _ hk]; exact hl
    · right
      push Not at hloc
      refine ⟨r.set, List.mem_map.2 ⟨r, ?_, rfl⟩, hz⟩
      simp only [hRest, List.mem_filter, decide_eq_true_eq]
      exact ⟨hr, hloc⟩

theorem WCert.cert_cs {gs : List GZ} {W : WCert} (hl : W.cones.length = (groupLR gs).length) :
    (W.cert gs).cs.map (fun q => (q.1, q.2.1)) = groupLR gs := by
  simp only [WCert.cert]
  rw [List.map_zipWith]
  refine List.ext_getElem (by simp [hl]) (fun i h1 h2 => ?_)
  simp only [List.getElem_zipWith]

/-- **A witness certificate of a group bounds the viewers** (box form). -/
theorem WCert.sees {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) {W : WCert}
    (hok : (W.cert gs).ok = true) (hl : W.cones.length = (groupLR gs).length)
    (hsep : boxesSepB (gs.map GZ.box) = true) {p : Point}
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (W.a.real ox (Hr n Φ)) p) :
    (∃ q ∈ (W.cert gs).cs, p ∈ (q.1.real ox (Hr n Φ)).set ∧
      p ∈ conesSet ox (Hr n Φ) (W.a.real ox (Hr n Φ)) q.2.2 ∧
      p ∈ ((gs.map GZ.box).getD q.2.1 LBox.default).set ox (Hr n Φ)) ∨
      (p ∈ optCone ox (Hr n Φ) (W.a.real ox (Hr n Φ)) W.C ∧
        ∀ U ∈ gs.map GZ.box, p ∉ U.set ox (Hr n Φ)) := by
  obtain ⟨Rest, hRc, hRU, hcov⟩ := group_rest hgs
  have hcs := WCert.cert_cs hl
  exact LCert.sound_box hok hsep (Hr_ge n Φ) ox (LP.mem_rect ox _ W.a) hRc hRU (fun s h0 h1 => by
    have hm : lerp (W.a.real ox (Hr n Φ)) p s ∈ RU (regionRectsO n Φ) := by
      rw [← filledO]; exact hs (lerp_mem_segment' _ p h0 h1)
    rcases hcov _ hm with ⟨rk, hrk, hz⟩ | h
    · left
      rw [← hcs] at hrk
      obtain ⟨q, hq, hql⟩ := List.mem_map.1 hrk
      exact ⟨q, hq, by rw [← hql] at hz; exact hz⟩
    · exact Or.inr h)

/-- The default witness certificate. -/
def WCert.dflt : WCert := ⟨(0, 0, 0), 0, none, [], (0, 0)⟩

/-- The part of the group check besides the certificates. -/
def groupRestB (gs : List GZ) (Ws : List WCert) (Ts : List ((ℕ × ℕ) × SepT)) : Bool :=
  boxesSepB (gs.map GZ.box) &&
  Ws.all (fun W => decide (W.cones.length = (groupLR gs).length) && W.slabB) &&
  (List.range Ws.length).all fun i => (List.range Ws.length).all fun j =>
    decide (j ≤ i) ||
      (disjB ((Ws.getD i ⟨(0, 0, 0), 0, none, [], (0, 0)⟩).cert gs)
          ((Ws.getD j ⟨(0, 0, 0), 0, none, [], (0, 0)⟩).cert gs) &&
        escSepB (treeOf Ts i j) (Ws.getD i ⟨(0, 0, 0), 0, none, [], (0, 0)⟩)
          (Ws.getD j ⟨(0, 0, 0), 0, none, [], (0, 0)⟩))

/-- The group check from its parts (certificates checked one by one). -/
theorem groupOK_of {gs : List GZ} {Ws : List WCert} {Ts : List ((ℕ × ℕ) × SepT)}
    (hc : ∀ W ∈ Ws, (W.cert gs).ok = true) (hr : groupRestB gs Ws Ts = true) :
    groupOK gs Ws Ts = true := by
  simp only [groupRestB, Bool.and_eq_true, List.all_eq_true] at hr
  simp only [groupOK, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨hr.1.1, fun W hW => ⟨⟨hc W hW, (hr.1.2 W hW).1⟩, (hr.1.2 W hW).2⟩⟩, hr.2⟩

theorem groupOK_parts {gs : List GZ} {Ws : List WCert} {Ts : List ((ℕ × ℕ) × SepT)}
    (h : groupOK gs Ws Ts = true) :
    boxesSepB (gs.map GZ.box) = true ∧
    (∀ W ∈ Ws, (W.cert gs).ok = true ∧ W.cones.length = (groupLR gs).length ∧ W.slabB = true) ∧
    ∀ i j (hi : i < Ws.length) (hj : j < Ws.length), i < j →
      disjB (Ws[i].cert gs) (Ws[j].cert gs) = true ∧ escSepB (treeOf Ts i j) Ws[i] Ws[j] = true := by
  simp only [groupOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨hb, hW⟩, hp⟩ := h
  refine ⟨hb, fun W hW' => ⟨(hW W hW').1.1, (hW W hW').1.2, (hW W hW').2⟩, fun i j hi hj hij => ?_⟩
  rcases hp i hi j hj with h | h
  · omega
  · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
    exact h

theorem mem_filled_of_sees {P : Polygon} {w p : Point} (h : P.Sees w p) : p ∈ P.filled :=
  h ⟨1, zero_le_one, le_rfl, by ext <;> simp⟩

theorem sees_symm {P : Polygon} {w p : Point} (h : P.Sees p w) : P.Sees w p := by
  intro z hz
  apply h
  rw [Geometry.segment_comm]; exact hz

/-- The strip contains the region. -/
def StripBound (n : ℕ) (Φ : List Constraint) : Prop :=
  ∀ p ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled, yMin.ev (Hr n Φ) ≤ p.2 ∧ p.2 ≤ yMax.ev (Hr n Φ)

/-- **The viewers of a witness lie in the boxes of its group or in its slab.** -/
theorem group_viewer {gs : List GZ} {Ws : List WCert} {Ts : List ((ℕ × ℕ) × SepT)}
    (h : groupOK gs Ws Ts = true) {ox : ℚ}
    (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) (hY : StripBound n Φ) {W : WCert} (hW : W ∈ Ws) {p : Point}
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (W.a.real ox (Hr n Φ)) p) :
    (∃ U ∈ gs.map GZ.box, p ∈ U.set ox (Hr n Φ)) ∨
      (W.C ≠ none ∧ ox + W.slab.1 < p.1 ∧ p.1 < ox + W.slab.2) := by
  obtain ⟨hb, hWs, -⟩ := groupOK_parts h
  obtain ⟨hok, hl, hslab⟩ := hWs W hW
  rcases WCert.sees hgs hok hl hb hs with ⟨q, hq, -, -, hpU⟩ | ⟨hC, -⟩
  · left
    refine ⟨_, ?_, hpU⟩
    have hk : q.2.1 < (gs.map GZ.box).length := by
      have := hok
      simp only [LCert.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
      exact this.1.2 q hq |>.1.2
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  · right
    have hY' := hY p (mem_filled_of_sees hs)
    cases hWC : W.C with
    | none => rw [hWC] at hC; exact absurd hC (by simp [optCone])
    | some K =>
      rw [hWC] at hC
      simp only [WCert.slabB, hWC, Bool.and_eq_true] at hslab
      refine ⟨by simp, rightOfB_sound hslab.1 (Hr_ge n Φ) ox hC hY'.1 hY'.2,
        leftOfB_sound hslab.2 (Hr_ge n Φ) ox hC hY'.1 hY'.2⟩

/-- Disjointness for an ordered pair of witnesses. -/
theorem group_disjoint_lt {gs : List GZ} {Ws : List WCert} {Ts : List ((ℕ × ℕ) × SepT)}
    (h : groupOK gs Ws Ts = true) {ox : ℚ}
    (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) (hY : StripBound n Φ) {i j : ℕ} (hi : i < Ws.length)
    (hj : j < Ws.length) (hij : i < j) {p : Point}
    (h1 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (Ws[i].a.real ox (Hr n Φ)) p)
    (h2 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (Ws[j].a.real ox (Hr n Φ)) p) : False := by
  obtain ⟨hb, hWs, hpair⟩ := groupOK_parts h
  obtain ⟨hd, he⟩ := hpair i j hi hj hij
  obtain ⟨ok1, l1, -⟩ := hWs _ (List.getElem_mem hi)
  obtain ⟨ok2, l2, -⟩ := hWs _ (List.getElem_mem hj)
  have hH := Hr_ge n Φ
  rcases WCert.sees hgs ok1 l1 hb h1 with ⟨q1, hq1, hp1, hc1, hU1⟩ | ⟨hC1, hout1⟩ <;>
    rcases WCert.sees hgs ok2 l2 hb h2 with ⟨q2, hq2, hp2, hc2, hU2⟩ | ⟨hC2, hout2⟩
  · exact disjB_sound hd hH ox (LP.mem_rect ox _ _) (LP.mem_rect ox _ _) hq1 hp1 hc1 hq2 hp2 hc2
  · have hk : q1.2.1 < (gs.map GZ.box).length := by
      have := ok1
      simp only [LCert.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
      exact this.1.2 q1 hq1 |>.1.2
    rw [List.getD_eq_getElem _ _ hk] at hU1
    exact hout2 _ (List.getElem_mem hk) hU1
  · have hk : q2.2.1 < (gs.map GZ.box).length := by
      have := ok2
      simp only [LCert.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
      exact this.1.2 q2 hq2 |>.1.2
    rw [List.getD_eq_getElem _ _ hk] at hU2
    exact hout1 _ (List.getElem_mem hk) hU2
  · -- two escaping cones
    have hY' := hY p (mem_filled_of_sees h1)
    obtain ⟨-, -, hs1⟩ := hWs _ (List.getElem_mem hi)
    obtain ⟨-, -, hs2⟩ := hWs _ (List.getElem_mem hj)
    cases hC1' : Ws[i].C with
    | none => rw [hC1'] at hC1; exact absurd hC1 (by simp [optCone])
    | some K1 =>
      cases hC2' : Ws[j].C with
      | none => rw [hC2'] at hC2; exact absurd hC2 (by simp [optCone])
      | some K2 =>
        rw [hC1'] at hC1; rw [hC2'] at hC2
        simp only [WCert.slabB, hC1', hC2', Bool.and_eq_true] at hs1 hs2
        have a1 := rightOfB_sound hs1.1 hH ox hC1 hY'.1 hY'.2
        have a2 := leftOfB_sound hs1.2 hH ox hC1 hY'.1 hY'.2
        have b1 := rightOfB_sound hs2.1 hH ox hC2 hY'.1 hY'.2
        have b2 := leftOfB_sound hs2.2 hH ox hC2 hY'.1 hY'.2
        simp only [escSepB, hC1', hC2', Bool.or_eq_true, decide_eq_true_eq] at he
        rcases he with he | he
        · have : ((min Ws[i].slab.2 Ws[j].slab.2 : ℚ) : ℝ) ≤ ((max Ws[i].slab.1 Ws[j].slab.1 : ℚ) : ℝ) := by
            exact_mod_cast he
          rw [Rat.cast_min, Rat.cast_max] at this
          rcases le_total (Ws[i].slab.2 : ℝ) Ws[j].slab.2 with c1 | c1 <;>
            rcases le_total (Ws[i].slab.1 : ℝ) Ws[j].slab.1 with c2 | c2
          · rw [min_eq_left c1, max_eq_right c2] at this; linarith
          · rw [min_eq_left c1, max_eq_left c2] at this; linarith
          · rw [min_eq_right c1, max_eq_right c2] at this; linarith
          · rw [min_eq_right c1, max_eq_left c2] at this; linarith
        · refine sepT_sound hH ox (LP.mem_rect ox _ _) (LP.mem_rect ox _ _) _ _ he p ⟨?_, ?_, hY'.1, hY'.2⟩ hC1 hC2
          · show ox + ((max Ws[i].slab.1 Ws[j].slab.1 : ℚ) : ℝ) ≤ p.1
            rw [Rat.cast_max]
            have := max_le (show (Ws[i].slab.1 : ℝ) ≤ p.1 - ox by linarith)
              (show (Ws[j].slab.1 : ℝ) ≤ p.1 - ox by linarith)
            linarith
          · show p.1 ≤ ox + ((min Ws[i].slab.2 Ws[j].slab.2 : ℚ) : ℝ)
            rw [Rat.cast_min]
            have := le_min (show p.1 - ox ≤ (Ws[i].slab.2 : ℝ) by linarith)
              (show p.1 - ox ≤ (Ws[j].slab.2 : ℝ) by linarith)
            linarith

/-- **No point of the region sees two witnesses of a group.** -/
theorem group_disjoint {gs : List GZ} {Ws : List WCert} {Ts : List ((ℕ × ℕ) × SepT)}
    (h : groupOK gs Ws Ts = true) {ox : ℚ}
    (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) (hY : StripBound n Φ) {i j : ℕ} (hi : i < Ws.length)
    (hj : j < Ws.length) (hij : i ≠ j) {p : Point}
    (h1 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (Ws[i].a.real ox (Hr n Φ)))
    (h2 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (Ws[j].a.real ox (Hr n Φ))) : False := by
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact group_disjoint_lt h hgs hY hi hj hlt (sees_symm h1) (sees_symm h2)
  · exact group_disjoint_lt h hgs hY hj hi hlt (sees_symm h2) (sees_symm h1)

end

end ArtGallery.Orthogonal.Hard
