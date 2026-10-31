module

public import ArtGallery.Orthogonal.Hard.CertGroup

/-!
# Pin targets of a template group

A *pin target* is a boundary point or a vertical boundary segment that the guard of a counting
witness (its *owner*) must see.  Its certificate (`TCert`, target rectangle `A`) bounds its
viewers like the counting certificates (`WCert`) do.  The pin check of a group verifies that no
viewer of a pin target is a viewer of another counting witness of the group, except

* the *exempt* witnesses (the helper of the cutter of a cutter segment: it is pinned first and
  handled by the exterior side of the cutter wall), and
* the helpers when the owner is a main guard: then only the helper point `q` must see no point of
  the target (`pointUnseenB`), since helpers are pinned before main guards.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-! ### Cones of a target rectangle in a vertical strip -/

/-- The cone (targets in `A`) lies strictly left of `x = xr` in the strip `ylo ≤ y ≤ yhi`. -/
def leftOfBA (A : LR) (K : List HP) (xr : ℚ) (ylo yhi : AH) : Bool :=
  K.any fun h => A.corners.all (fun a => AH.nn (-(hpCoefX a h).1, -(hpCoefX a h).2)) &&
    hpNeg A h [(xr, ylo), (xr, yhi)]

/-- The cone (targets in `A`) lies strictly right of `x = xl` in the strip `ylo ≤ y ≤ yhi`. -/
def rightOfBA (A : LR) (K : List HP) (xl : ℚ) (ylo yhi : AH) : Bool :=
  K.any fun h => A.corners.all (fun a => (hpCoefX a h).nn) && hpNeg A h [(xl, ylo), (xl, yhi)]

/-- The coefficient of `z.1` in `det(E₁(w), E₂(w), z)` is affine in the target `w`. -/
theorem coefX_affine (ox H : ℝ) (h : HP) : ∃ α β γ : ℝ, ∀ x y : ℝ,
    -((h.2.pt ox H (x, y)).2 - (h.1.pt ox H (x, y)).2) = α * x + β * y + γ := by
  rcases h with ⟨e1, e2⟩
  cases e1 with
  | none =>
    cases e2 with
    | none => exact ⟨0, 0, 0, fun x y => by simp only [HE.pt]; ring⟩
    | some p => exact ⟨0, 1, -(p.real ox H).2, fun x y => by simp only [HE.pt]; ring⟩
  | some p =>
    cases e2 with
    | none => exact ⟨0, -1, (p.real ox H).2, fun x y => by simp only [HE.pt]; ring⟩
    | some q => exact ⟨0, 0, -((q.real ox H).2 - (p.real ox H).2), fun x y => by simp only [HE.pt]; ring⟩

/-- A sign of the `x`-coefficient at the corner targets holds for every target of `A`. -/
theorem coefX_bound {A : LR} {h : HP} {H : ℝ} (ox : ℝ) {s : ℝ}
    (hc : ∀ a ∈ A.corners, 0 ≤ s * (hpCoefX a h).ev H) {w : Point} (hw : w ∈ (A.real ox H).set) :
    0 ≤ s * -((h.2.pt ox H w).2 - (h.1.pt ox H w).2) := by
  obtain ⟨α, β, γ, hf⟩ := coefX_affine ox H h
  obtain ⟨c00, c10, c01, c11⟩ := corners_mem (P := fun a => 0 ≤ s * (hpCoefX a h).ev H) hc
  rw [← hpCoefX_ev, hf] at c00 c10 c01 c11
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  simp only [LR.real, LP.real] at hx0 hx1 hy0 hy1 c00 c10 c01 c11
  have := affine_rect (c := 0) (fun x y => s * (α * x + β * y + γ)) (A := s * α) (B := s * β)
    (G := s * γ) (fun x y => by ring) c00 c10 c01 c11 hx0 hx1 hy0 hy1
  have e : w = (w.1, w.2) := rfl
  rw [e, hf]; simpa using this

theorem leftOfBA_sound {A : LR} {K : List HP} {xr : ℚ} {ylo yhi : AH}
    (h : leftOfBA A K xr ylo yhi = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ) {w : Point}
    (hw : w ∈ (A.real ox H).set) {z : Point}
    (hz : z ∈ cone ox H w K) (h1 : ylo.ev H ≤ z.2) (h2 : z.2 ≤ yhi.ev H) :
    z.1 < ox + xr := by
  simp only [leftOfBA, List.any_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hp, hpK, hc, hn⟩ := h
  by_contra hx
  push Not at hx
  have hzh : 0 ≤ det (hp.1.pt ox H w) (hp.2.pt ox H w) z := hz hp hpK
  have hneg := hpNeg_sound (hpNeg_side hn) hH ox hw (side_mem (ox := ox) h1 h2)
  have hneg' : det (hp.1.pt ox H w) (hp.2.pt ox H w) (ox + xr, z.2) < 0 := by
    by_contra hc'; push Not at hc'; exact hneg hc'
  have hcoef := coefX_bound (s := -1) ox (fun a ha => by
    have := AH.nn_sound (hc a ha) hH
    simp only [AH.ev] at this ⊢; push_cast at this; linarith) hw
  rw [det_shift_x _ _ z (ox + xr)] at hzh
  nlinarith

theorem rightOfBA_sound {A : LR} {K : List HP} {xl : ℚ} {ylo yhi : AH}
    (h : rightOfBA A K xl ylo yhi = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ) {w : Point}
    (hw : w ∈ (A.real ox H).set) {z : Point}
    (hz : z ∈ cone ox H w K) (h1 : ylo.ev H ≤ z.2) (h2 : z.2 ≤ yhi.ev H) :
    ox + xl < z.1 := by
  simp only [rightOfBA, List.any_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hp, hpK, hc, hn⟩ := h
  by_contra hx
  push Not at hx
  have hzh : 0 ≤ det (hp.1.pt ox H w) (hp.2.pt ox H w) z := hz hp hpK
  have hneg := hpNeg_sound (hpNeg_side hn) hH ox hw (side_mem (ox := ox) h1 h2)
  have hneg' : det (hp.1.pt ox H w) (hp.2.pt ox H w) (ox + xl, z.2) < 0 := by
    by_contra hc'; push Not at hc'; exact hneg hc'
  have hcoef := coefX_bound (s := 1) ox (fun a ha => by
    have := AH.nn_sound (hc a ha) hH
    simp only [AH.ev] at this ⊢; linarith) hw
  rw [det_shift_x _ _ z (ox + xl)] at hzh
  nlinarith

/-! ### Target certificates -/

/-- A target of a group (a point or a vertical segment) with its certificate data. -/
structure TCert where
  A : LR
  Ab : ℕ
  C : Option (List HP)
  cones : List (List (List HP))
  slab : ℚ × ℚ

/-- The certificate of a target over the rectangles of a group. -/
def TCert.cert (gs : List GZ) (T : TCert) : LCert :=
  ⟨T.A, T.Ab, (groupLR gs).zipWith (fun rk Ks => (rk.1, rk.2, Ks)) T.cones, T.C, gs.map GZ.box⟩

/-- The escaping cone lies in the slab (within the strip). -/
def TCert.slabB (T : TCert) : Bool :=
  match T.C with
  | none => true
  | some K => rightOfBA T.A K T.slab.1 yMin yMax && leftOfBA T.A K T.slab.2 yMin yMax

/-! ### Integer-coded target certificates (fast to elaborate) -/

/-- A rational coded as numerator and denominator. -/
abbrev QC := ℤ × ℕ

/-- The rational of a code. -/
def QC.q (c : QC) : ℚ := mkRat c.1 c.2

/-- A target certificate coded by integers, with tables of endpoints `E` (an endpoint
`(x, a, b)` stands for `(x, a + b H)`) and of half-planes `H` (a pair of endpoint indices, `0`
standing for the point at infinity and `i + 1` for `E[i]`); cones list half-plane indices. -/
structure TCertI where
  E : List (QC × QC × QC)
  H : List (ℕ × ℕ)
  A : QC × QC × QC × QC × QC × QC
  Ab : ℕ
  C : Option (List ℕ)
  cones : List (List (List ℕ))
  slab : QC × QC

/-- An endpoint of the table. -/
def TCertI.he (c : TCertI) : ℕ → HE
  | 0 => none
  | i + 1 => let e := c.E.getD i ((0, 1), (0, 1), (0, 1)); some (e.1.q, (e.2.1.q, e.2.2.q))

/-- A half-plane of the table. -/
def TCertI.hp (c : TCertI) (i : ℕ) : HP := let h := c.H.getD i (0, 0); (c.he h.1, c.he h.2)

/-- The target certificate of an integer code. -/
def TCertI.toT (c : TCertI) : TCert :=
  ⟨⟨c.A.1.q, c.A.2.1.q, (c.A.2.2.1.q, c.A.2.2.2.1.q), (c.A.2.2.2.2.1.q, c.A.2.2.2.2.2.q)⟩,
    c.Ab, c.C.map (·.map c.hp), c.cones.map (·.map (·.map c.hp)),
    (c.slab.1.q, c.slab.2.q)⟩

/-- A counting witness as a target. -/
def WCert.toT (W : WCert) : TCert := ⟨W.a.rect, W.Ab, W.C, W.cones, W.slab⟩

theorem WCert.toT_cert (gs : List GZ) (W : WCert) : W.toT.cert gs = W.cert gs := rfl

theorem LP.rect_corners (a : LP) : a.rect.corners = [a, a, a, a] := rfl

theorem WCert.toT_slabB {W : WCert} (h : W.slabB = true) : W.toT.slabB = true := by
  unfold WCert.slabB at h
  unfold TCert.slabB
  simp only [WCert.toT]
  cases hC : W.C with
  | none => rfl
  | some K =>
    rw [hC] at h
    simp only [rightOfB, leftOfB, rightOfBA, leftOfBA, Bool.and_eq_true, List.any_eq_true,
      LP.rect_corners, List.all_cons, List.all_nil, Bool.and_true, Bool.and_self] at h ⊢
    exact h

/-- The escaping parts of two targets are disjoint (within the strip), along a tree. -/
def tescSepB (T : SepT) (W1 W2 : TCert) : Bool :=
  match W1.C, W2.C with
  | some K1, some K2 =>
    decide (min W1.slab.2 W2.slab.2 ≤ max W1.slab.1 W2.slab.1) ||
      sepT W1.A K1 W2.A K2 T ⟨max W1.slab.1 W2.slab.1, min W1.slab.2 W2.slab.2, yMin, yMax⟩
  | _, _ => true

/-- The point `z` (a frame point) is robustly outside the closed rectangle `r`. -/
def LR.outB (r : LR) (z : LP) : Bool :=
  decide (z.1 < r.x0) || decide (r.x1 < z.1) || AH.lt z.2 r.y0 || AH.lt r.y1 z.2

/-- The point `z` is robustly no viewer of the targets of the certificate. -/
def pointUnseenB (c : LCert) (z : LP) : Bool :=
  c.cs.all (fun q => q.1.outB z || q.2.2.all fun K => K.any fun h => hpNeg c.A h [z]) &&
  (c.U.any (fun U => U.memB z) || match c.C with
    | none => true
    | some K => K.any fun h => hpNeg c.A h [z])

variable {n : ℕ} {Φ : List Constraint}

/-- **A target certificate of a group bounds the viewers** (box form). -/
theorem TCert.sees {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) {T : TCert}
    (hok : (T.cert gs).ok = true) (hl : T.cones.length = (groupLR gs).length)
    (hsep : boxesSepB (gs.map GZ.box) = true) {w p : Point} (hw : w ∈ (T.A.real ox (Hr n Φ)).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p) :
    (∃ q ∈ (T.cert gs).cs, p ∈ (q.1.real ox (Hr n Φ)).set ∧
      p ∈ conesSet ox (Hr n Φ) w q.2.2 ∧
      p ∈ ((gs.map GZ.box).getD q.2.1 LBox.default).set ox (Hr n Φ)) ∨
      (p ∈ optCone ox (Hr n Φ) w T.C ∧ ∀ U ∈ gs.map GZ.box, p ∉ U.set ox (Hr n Φ)) := by
  obtain ⟨Rest, hRc, hRU, hcov⟩ := group_rest hgs
  have hcs : (T.cert gs).cs.map (fun q => (q.1, q.2.1)) = groupLR gs := by
    simp only [TCert.cert]
    rw [List.map_zipWith]
    refine List.ext_getElem (by simp [hl]) (fun i h1 h2 => ?_)
    simp only [List.getElem_zipWith]
  exact LCert.sound_box hok hsep (Hr_ge n Φ) ox hw hRc hRU (fun s h0 h1 => by
    have hm : lerp w p s ∈ RU (regionRectsO n Φ) := by
      rw [← filledO]; exact hs (lerp_mem_segment' _ p h0 h1)
    rcases hcov _ hm with ⟨rk, hrk, hz⟩ | h
    · left
      rw [← hcs] at hrk
      obtain ⟨q, hq, hql⟩ := List.mem_map.1 hrk
      exact ⟨q, hq, by rw [← hql] at hz; exact hz⟩
    · exact Or.inr h)

/-- The box index of a local rectangle of a valid certificate is in range. -/
theorem LCert.box_lt {c : LCert} (hok : c.ok = true) {q : LR × ℕ × List (List HP)} (hq : q ∈ c.cs) :
    q.2.1 < c.U.length := by
  simp only [LCert.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  exact (hok.1.2 q hq).1.2

/-- **No point sees targets of two certificates of a group** whose pieces and escaping parts are
separated. -/
theorem tcert_disjoint {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox)
    (hY : StripBound n Φ) (hb : boxesSepB (gs.map GZ.box) = true) {T1 T2 : TCert}
    (ok1 : (T1.cert gs).ok = true) (l1 : T1.cones.length = (groupLR gs).length) (s1 : T1.slabB = true)
    (ok2 : (T2.cert gs).ok = true) (l2 : T2.cones.length = (groupLR gs).length) (s2 : T2.slabB = true)
    (hd : disjB (T1.cert gs) (T2.cert gs) = true) {tr : SepT} (he : tescSepB tr T1 T2 = true)
    {w1 w2 p : Point} (hw1 : w1 ∈ (T1.A.real ox (Hr n Φ)).set) (hw2 : w2 ∈ (T2.A.real ox (Hr n Φ)).set)
    (h1 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w1 p)
    (h2 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w2 p) : False := by
  have hH := Hr_ge n Φ
  rcases TCert.sees hgs ok1 l1 hb hw1 h1 with ⟨q1, hq1, hp1, hc1, hU1⟩ | ⟨hC1, hout1⟩ <;>
    rcases TCert.sees hgs ok2 l2 hb hw2 h2 with ⟨q2, hq2, hp2, hc2, hU2⟩ | ⟨hC2, hout2⟩
  · exact disjB_sound hd hH ox hw1 hw2 hq1 hp1 hc1 hq2 hp2 hc2
  · have hk := LCert.box_lt ok1 hq1
    simp only [TCert.cert] at hk hU1
    rw [List.getD_eq_getElem _ _ hk] at hU1
    exact hout2 _ (List.getElem_mem hk) hU1
  · have hk := LCert.box_lt ok2 hq2
    simp only [TCert.cert] at hk hU2
    rw [List.getD_eq_getElem _ _ hk] at hU2
    exact hout1 _ (List.getElem_mem hk) hU2
  · have hY' := hY p (mem_filled_of_sees h1)
    cases hC1' : T1.C with
    | none => rw [hC1'] at hC1; exact absurd hC1 (by simp [optCone])
    | some K1 =>
      cases hC2' : T2.C with
      | none => rw [hC2'] at hC2; exact absurd hC2 (by simp [optCone])
      | some K2 =>
        rw [hC1'] at hC1; rw [hC2'] at hC2
        simp only [TCert.slabB, hC1', hC2', Bool.and_eq_true] at s1 s2
        have a1 := rightOfBA_sound s1.1 hH ox hw1 hC1 hY'.1 hY'.2
        have a2 := leftOfBA_sound s1.2 hH ox hw1 hC1 hY'.1 hY'.2
        have b1 := rightOfBA_sound s2.1 hH ox hw2 hC2 hY'.1 hY'.2
        have b2 := leftOfBA_sound s2.2 hH ox hw2 hC2 hY'.1 hY'.2
        simp only [tescSepB, hC1', hC2', Bool.or_eq_true, decide_eq_true_eq] at he
        rcases he with he | he
        · have : ((min T1.slab.2 T2.slab.2 : ℚ) : ℝ) ≤ ((max T1.slab.1 T2.slab.1 : ℚ) : ℝ) := by
            exact_mod_cast he
          rw [Rat.cast_min, Rat.cast_max] at this
          rcases le_total (T1.slab.2 : ℝ) T2.slab.2 with c1 | c1 <;>
            rcases le_total (T1.slab.1 : ℝ) T2.slab.1 with c2 | c2
          · rw [min_eq_left c1, max_eq_right c2] at this; linarith
          · rw [min_eq_left c1, max_eq_left c2] at this; linarith
          · rw [min_eq_right c1, max_eq_right c2] at this; linarith
          · rw [min_eq_right c1, max_eq_left c2] at this; linarith
        · refine sepT_sound hH ox hw1 hw2 _ _ he p ⟨?_, ?_, hY'.1, hY'.2⟩ hC1 hC2
          · show ox + ((max T1.slab.1 T2.slab.1 : ℚ) : ℝ) ≤ p.1
            rw [Rat.cast_max]
            have := max_le (show (T1.slab.1 : ℝ) ≤ p.1 - ox by linarith)
              (show (T2.slab.1 : ℝ) ≤ p.1 - ox by linarith)
            linarith
          · show p.1 ≤ ox + ((min T1.slab.2 T2.slab.2 : ℚ) : ℝ)
            rw [Rat.cast_min]
            have := le_min (show p.1 - ox ≤ (T1.slab.2 : ℝ) by linarith)
              (show p.1 - ox ≤ (T2.slab.2 : ℝ) by linarith)
            linarith

/-- **A point robustly unseen**: the frame point `z` does not see any target of the certificate. -/
theorem pointUnseen_sound {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox)
    (hb : boxesSepB (gs.map GZ.box) = true) {T : TCert}
    (ok : (T.cert gs).ok = true) (l : T.cones.length = (groupLR gs).length) {z : LP}
    (hz : pointUnseenB (T.cert gs) z = true) {w : Point} (hw : w ∈ (T.A.real ox (Hr n Φ)).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w (z.real ox (Hr n Φ))) : False := by
  have hH := Hr_ge n Φ
  simp only [pointUnseenB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.any_eq_true] at hz
  obtain ⟨hz1, hz2⟩ := hz
  rcases TCert.sees hgs ok l hb hw hs with ⟨q, hq, hp, hc, -⟩ | ⟨hC, hout⟩
  · rcases hz1 q hq with ho | hK
    · -- the point is outside the rectangle
      obtain ⟨hx0, hx1, hy0, hy1⟩ := hp
      simp only [LR.real, LP.real] at hx0 hx1 hy0 hy1
      simp only [LR.outB, Bool.or_eq_true, decide_eq_true_eq] at ho
      rcases ho with ((h | h) | h) | h
      · have : (z.1 : ℝ) < q.1.x0 := by exact_mod_cast h
        linarith
      · have : (q.1.x1 : ℝ) < z.1 := by exact_mod_cast h
        linarith
      · have := AH.lt_sound h hH; linarith
      · have := AH.lt_sound h hH; linarith
    · obtain ⟨K, hKm, hzK⟩ := hc
      obtain ⟨h, hh, hn⟩ := hK K hKm
      have hzr : z.real ox (Hr n Φ) ∈ (z.rect.real ox (Hr n Φ)).set := LP.mem_rect ox _ z
      have hn' : hpNeg T.A h z.rect.corners = true := by
        simp only [hpNeg, List.all_eq_true] at hn ⊢
        intro a ha c hc
        simp only [LP.rect, LR.corners, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> exact hn a ha _ (by simp)
      exact hpNeg_sound hn' hH ox hw hzr (hzK h hh)
  · rcases hz2 with ⟨U, hU, hm⟩ | hC'
    · exact hout U hU (LBox.memB_sound hm hH ox)
    · simp only [TCert.cert] at hC'
      cases hTC : T.C with
      | none => rw [hTC] at hC; exact absurd hC (by simp [optCone])
      | some K =>
        rw [hTC] at hC hC'
        simp only [List.any_eq_true] at hC'
        obtain ⟨h, hh, hn⟩ := hC'
        have hzr : z.real ox (Hr n Φ) ∈ (z.rect.real ox (Hr n Φ)).set := LP.mem_rect ox _ z
        have hn' : hpNeg T.A h z.rect.corners = true := by
          simp only [hpNeg, List.all_eq_true] at hn ⊢
          intro a ha c hc
          simp only [LP.rect, LR.corners, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl <;> exact hn a ha _ (by simp)
        exact hpNeg_sound hn' hH ox hw hzr (hC h hh)

/-! ### Spots -/

/-- No point of the rectangle `S` (robustly) is a viewer of the targets of the certificate. -/
def rectUnseenB (c : LCert) (S : LR) : Bool :=
  c.cs.all (fun q => q.2.2.isEmpty || match q.1.inter S with
    | none => false
    | some none => true
    | some (some X) => q.2.2.all fun K => K.any fun h => hpNegr c.A h X) &&
  (c.U.any (fun U => S.corners.all U.memB) || match c.C with
    | none => true
    | some K => K.any fun h => hpNegr c.A h S)

/-- **A rectangle robustly unseen**: no point of `S` sees a target of the certificate. -/
theorem rectUnseen_sound {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox)
    (hb : boxesSepB (gs.map GZ.box) = true) {T : TCert}
    (ok : (T.cert gs).ok = true) (l : T.cones.length = (groupLR gs).length) {S : LR}
    (hS : rectUnseenB (T.cert gs) S = true) {w z : Point} (hw : w ∈ (T.A.real ox (Hr n Φ)).set)
    (hz : z ∈ (S.real ox (Hr n Φ)).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w z) : False := by
  have hH := Hr_ge n Φ
  simp only [rectUnseenB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.any_eq_true,
    List.isEmpty_iff] at hS
  obtain ⟨hz1, hz2⟩ := hS
  rcases TCert.sees hgs ok l hb hw hs with ⟨q, hq, hp, hc, -⟩ | ⟨hC, hout⟩
  · obtain ⟨K, hKm, hzK⟩ := hc
    rcases hz1 q hq with he | hK
    · rw [he] at hKm; simp at hKm
    · split at hK
      · cases hK
      · rename_i hi; exact LR.inter_empty hi hH ox hp hz
      · rename_i X hi
        simp only [List.all_eq_true, List.any_eq_true] at hK
        obtain ⟨h, hh, hn⟩ := hK K hKm
        exact hpNegr_sound hn hH ox hw (LR.inter_sub hi hH ox hp hz) (hzK h hh)
  · rcases hz2 with ⟨U, hU, hm⟩ | hC'
    · exact hout U hU (LBox.corners_sound (List.all_eq_true.2 hm) hH ox hz)
    · simp only [TCert.cert] at hC'
      cases hTC : T.C with
      | none => rw [hTC] at hC; exact absurd hC (by simp [optCone])
      | some K =>
        rw [hTC] at hC hC'
        simp only [List.any_eq_true] at hC'
        obtain ⟨h, hh, hn⟩ := hC'
        exact hpNegr_sound hn hH ox hw hz (hC h hh)

/-! ### The pin check of a group -/

/-- A pin target of a group: its certificate, the index of its owner (the counting witness whose
guard sees it), the exempt witnesses, and the separation trees of its escaping cone against the
escaping witnesses. -/
structure PinT where
  T : TCert
  owner : ℕ
  exempt : List ℕ
  trees : List (ℕ × SepT)

/-- The separation tree against witness `j` (default: a leaf). -/
def treeOfJ (ts : List (ℕ × SepT)) (j : ℕ) : SepT :=
  ((ts.find? fun t => t.1 == j).map Prod.snd).getD .leaf

/-- The default rectangle. -/
def LR.dflt : LR := ⟨0, 0, (0, 0), (0, 0)⟩

/-- **The pin check** of a pin target in a group with counting witnesses `Ws`, their ranks `rks`
(the order in which guards are pinned) and spots `sps`: the certificate is valid and, for every
other non-exempt witness `j`, either `j` is pinned earlier and no point of its spot sees the target,
or the viewers are disjoint. -/
def pinB (gs : List GZ) (Ws : List WCert) (rks : List ℕ) (sps : List LR) (P : PinT) : Bool :=
  (P.T.cert gs).ok && decide (P.T.cones.length = (groupLR gs).length) && P.T.slabB &&
  (List.range Ws.length).all fun j =>
    decide (j = P.owner) || decide (j ∈ P.exempt) ||
      if rks.getD j 0 < rks.getD P.owner 0 then rectUnseenB (P.T.cert gs) (sps.getD j LR.dflt)
      else disjB (P.T.cert gs) ((Ws.getD j WCert.dflt).cert gs) &&
          tescSepB (treeOfJ P.trees j) P.T (Ws.getD j WCert.dflt).toT

theorem pinB_parts {gs : List GZ} {Ws : List WCert} {rks : List ℕ} {sps : List LR} {P : PinT}
    (h : pinB gs Ws rks sps P = true) :
    (P.T.cert gs).ok = true ∧ P.T.cones.length = (groupLR gs).length ∧ P.T.slabB = true ∧
    ∀ j < Ws.length, j ≠ P.owner → j ∉ P.exempt →
      (if rks.getD j 0 < rks.getD P.owner 0 then rectUnseenB (P.T.cert gs) (sps.getD j LR.dflt)
      else disjB (P.T.cert gs) ((Ws.getD j WCert.dflt).cert gs) &&
          tescSepB (treeOfJ P.trees j) P.T (Ws.getD j WCert.dflt).toT) = true := by
  simp only [pinB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun j hj hjo hje => ?_⟩
  rcases h4 j hj with (h | h) | h
  · exact absurd h hjo
  · exact absurd h hje
  · exact h

/-- **Late exclusion**: a viewer of a pin target is no viewer of another non-exempt witness of
equal or later rank. -/
theorem pinB_late {gs : List GZ} {Ws : List WCert} {Ts : List ((ℕ × ℕ) × SepT)}
    {rks : List ℕ} {sps : List LR} {P : PinT} (hP : pinB gs Ws rks sps P = true)
    (hG : groupOK gs Ws Ts = true)
    {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) (hY : StripBound n Φ) {j : ℕ} (hj : j < Ws.length)
    (hjo : j ≠ P.owner) (hje : j ∉ P.exempt) (hr : ¬ rks.getD j 0 < rks.getD P.owner 0)
    {w p : Point} (hw : w ∈ (P.T.A.real ox (Hr n Φ)).set)
    (h1 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p)
    (h2 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (Ws[j].a.real ox (Hr n Φ)) p) : False := by
  obtain ⟨ok, l, sl, hpair⟩ := pinB_parts hP
  obtain ⟨hb, hWs, -⟩ := groupOK_parts hG
  obtain ⟨ok2, l2, sl2⟩ := hWs _ (List.getElem_mem hj)
  have hx := hpair j hj hjo hje
  simp only [hr, ↓reduceIte] at hx
  rw [List.getD_eq_getElem _ _ hj] at hx
  simp only [Bool.and_eq_true] at hx
  exact tcert_disjoint hgs hY hb ok l sl (T2 := Ws[j].toT) ok2 l2 (WCert.toT_slabB sl2) hx.1 hx.2 hw
    (LP.mem_rect ox _ _) h1 h2

/-- **Early exclusion**: no point of the spot of an earlier witness sees a point of a pin target. -/
theorem pinB_early {gs : List GZ} {Ws : List WCert} {rks : List ℕ} {sps : List LR} {P : PinT}
    (hP : pinB gs Ws rks sps P = true) (hb : boxesSepB (gs.map GZ.box) = true) {ox : ℚ}
    (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) {j : ℕ} (hj : j < Ws.length) (hjo : j ≠ P.owner)
    (hje : j ∉ P.exempt) (hr : rks.getD j 0 < rks.getD P.owner 0)
    {w z : Point} (hw : w ∈ (P.T.A.real ox (Hr n Φ)).set)
    (hz : z ∈ ((sps.getD j LR.dflt).real ox (Hr n Φ)).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w z) : False := by
  obtain ⟨ok, l, -, hpair⟩ := pinB_parts hP
  have hx := hpair j hj hjo hje
  simp only [hr, ↓reduceIte] at hx
  exact rectUnseen_sound hgs hb ok l hx hw hz hs

end

end ArtGallery.Orthogonal.Hard
