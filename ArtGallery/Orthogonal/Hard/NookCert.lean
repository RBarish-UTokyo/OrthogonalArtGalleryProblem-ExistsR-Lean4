module

public import ArtGallery.Orthogonal.Hard.GCert
public import ArtGallery.Orthogonal.Hard.MPoly
public import ArtGallery.Orthogonal.Hard.CertGroup

/-!
# Grid certificates in a copy nook

The grid of the copy-nook zone (`cnXe`, `cnYe`) relative to the frame origin `(x_N, 2H)` is a
list of polynomials in the parameters `(G, d, e)` of the nook (`u = G + d`), which range over the
box `G ∈ [1, 2]`, `d ∈ (0, 1/100]`, `e ∈ (0, 1/500]` (`nookPar_dom`).  The sign oracle `nookOr`
decides `det` of three grid points by the subdivided polynomial sign test (`MP.nnS`, `MP.posS`);
it is sound for every nook (`nookOr_sound`).  A grid certificate over the rectangles of the copy-nook
zone (`cnRR`, real grid indices) and the box of the zone applies to the polygon
(`sees_nookCert`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-! ### The polynomial grid -/

/-- The parameter `G`. -/
def nG : MP := MP.var 0
/-- The parameter `d = u − G`. -/
def nD : MP := MP.var 1
/-- The parameter `e`. -/
def nE : MP := MP.var 2
/-- `u = G + d`. -/
def nU : MP := MP.add nG nD
/-- `G e`. -/
def nGE : MP := MP.mul nG nE

/-- The abscissae `cnXe` relative to `x_N`. -/
def nXs : List MP :=
  [MP.sub (MP.neg nU) (MP.c (7 / 8)), MP.sub (MP.neg nU) (MP.c (3 / 4)),
    MP.sub (MP.neg nU) (MP.c (1 / 4)), MP.sub (MP.neg nU) (MP.c (1 / 32)), MP.neg nU,
    MP.add (MP.neg nU) (MP.c (1 / 32)), MP.add (MP.neg nU) (MP.c (1 / 4)), MP.c (-1 / 2),
    MP.add (MP.smul (-27 / 64) nGE) (MP.smul (-9 / 32) nE), MP.smul (-27 / 64) nGE,
    MP.add (MP.smul (-9 / 32) nGE) (MP.smul (-9 / 512) nE), MP.smul (-9 / 32) nGE,
    MP.add (MP.smul (-9 / 32) nGE) (MP.smul (9 / 512) nE), MP.smul (-9 / 64) nGE,
    MP.smul (-9 / 128) nGE, MP.c 0, nG, nU, MP.add (MP.smul 3 nU) (MP.c (1 / 4)),
    MP.add (MP.smul 3 nU) (MP.c (3 / 8))]

/-- `1 − 5e/4`. -/
def nYB : MP := MP.add (MP.c 1) (MP.smul (-5 / 4) nE)
/-- `(1 − 5e/4) (9e/32)`. -/
def nS32 : MP := MP.mul nYB (MP.smul (9 / 32) nE)
/-- `(1 − 5e/4) (9e/64)`. -/
def nS64 : MP := MP.mul nYB (MP.smul (9 / 64) nE)
/-- The base `1 − 5e/4 + (1 − 5e/4)(9e/32)`. -/
def nYS : MP := MP.add nYB nS32

/-- The ordinates `cnYe` relative to `2H`. -/
def nYs : List MP :=
  [MP.c (-1 / 4), MP.c (-1 / 8), MP.c (-1 / 16), MP.c 0, MP.add nE (MP.c (1 / 2)),
    MP.add nYS (MP.smul (-9 / 64) nGE), MP.add nYB nS64, MP.add nYS (MP.smul (-9 / 512) nE), nYS,
    MP.add nYS (MP.smul (9 / 512) nE), MP.add nYS (MP.smul (9 / 64) nGE),
    MP.add (MP.add nYS (MP.smul (9 / 64) nGE)) (MP.smul (9 / 64) nE), MP.add (MP.c 1) nE,
    MP.add (MP.add (MP.c 2) (MP.smul 2 nE)) (MP.c (-1 / 4)),
    MP.add (MP.add (MP.c 2) (MP.smul 2 nE)) (MP.c (-1 / 32)), MP.add (MP.c 2) (MP.smul 2 nE),
    MP.add (MP.add (MP.c 2) (MP.smul 2 nE)) (MP.c (1 / 32)),
    MP.add (MP.add (MP.c 2) (MP.smul 2 nE)) (MP.c (1 / 4)),
    MP.add (MP.add (MP.c 3) (MP.smul 3 nE)) (MP.c (1 / 2))]

/-- `det` of three grid points as a polynomial (translation invariant). -/
def nookDet (u v z : ℕ × ℕ) : MP :=
  MP.sub (MP.mul (MP.sub (nXs.getD v.1 []) (nXs.getD u.1 [])) (MP.sub (nYs.getD z.2 []) (nYs.getD u.2 [])))
    (MP.mul (MP.sub (nXs.getD z.1 []) (nXs.getD u.1 [])) (MP.sub (nYs.getD v.2 []) (nYs.getD u.2 [])))

/-- The parameter box. -/
def nookDom : List VDom := [⟨1, some 2, false⟩, ⟨0, some (1 / 100), true⟩, ⟨0, some (1 / 500), true⟩]

/-- The sign oracle of the copy nooks. -/
def nookOr : GOr :=
  ⟨fun u v z => MP.nnS nookDom (MP.norm (nookDet u v z)) 6,
    fun u v z => MP.posS nookDom (MP.norm (nookDet u v z)) 6⟩

/-- The grid abscissa (frame origin `x_N`, parameters `xs`). -/
noncomputable def nφ (xN : ℝ) (xs : List ℝ) (i : ℕ) : ℝ := xN + MP.ev xs (nXs.getD i [])

/-- The grid ordinate (frame origin `2H`, parameters `xs`). -/
noncomputable def nψ (H : ℝ) (xs : List ℝ) (j : ℕ) : ℝ := 2 * H + MP.ev xs (nYs.getD j [])

theorem nookOr_sound {xs : List ℝ} (hx : InDom nookDom xs) (xN H : ℝ) :
    nookOr.Sound (nφ xN xs) (nψ H xs) := by
  have key : ∀ u v z : ℕ × ℕ, det (gpt (nφ xN xs) (nψ H xs) u) (gpt (nφ xN xs) (nψ H xs) v)
      (gpt (nφ xN xs) (nψ H xs) z) = MP.ev xs (nookDet u v z) := by
    intro u v z
    simp only [gpt, det, nφ, nψ, nookDet, MP.ev_sub, MP.ev_mul]; ring
  refine ⟨fun u v z h => ?_, fun u v z h => ?_⟩
  · rw [key, ← MP.ev_norm]; exact MP.nnS_sound h hx
  · rw [key, ← MP.ev_norm]; exact MP.posS_sound h hx

/-! ### The rectangles and the box of the zone in real grid indices -/

/-- The rectangles of the copy-nook zone in real grid indices (`cnXe`, `cnYe`). -/
def cnRR : List GRect :=
  cnZone.rects.map fun r => (19 - r.2.1, 19 - r.1, 18 - r.2.2.2, 18 - r.2.2.1)

/-- The open box of the copy-nook zone. -/
def nookBox : GBox := ⟨some 0, some 19, some 0, none⟩

/-! ### The parameters of a nook -/

/-- The gap `u − G` of the mouth is small. -/
theorem nook_gap {a b H : ℚ} (hH : 1000 ≤ H) (h1 : H + 30 ≤ b - a) (h2 : b - a ≤ 2 * H - 600)
    (ge : Bool) : nookU a b ge H - nookG a b ge H ≤ 1 / 100 := by
  have hd1 : 0 < 2 * H - 1 := by linarith
  have hd2 : 0 < 2 * H - 2 := by linarith
  have hn1 : 2 * H - 1 ≠ 0 := hd1.ne'
  have hn2 : 2 * H - 2 ≠ 0 := hd2.ne'
  have hn3 : H - 1 ≠ 0 := by intro h; linarith
  cases ge
  · have hu : nookU a b false H = 2 * (b - a + 16) / (2 * H - 1) := by
      simp only [nookU, nookRm, nookPs, nookX, copyE, Bool.false_eq_true, ↓reduceIte]; field_simp; ring
    have hg : nookG a b false H = (2 * (b - a) + 16) / (2 * H - 2) := by
      simp only [nookG, nookLm, nookPt, nookX, copyE, Bool.false_eq_true, ↓reduceIte]; field_simp; ring
    rw [hu, hg, div_sub_div _ _ hn1 hn2, div_le_iff₀ (by positivity)]
    nlinarith
  · have hu : nookU a b true H = (2 * (b - a) - 12) / (2 * H - 2) := by
      simp only [nookU, nookRm, nookPt, nookX, copyE, ↓reduceIte]; field_simp; ring
    have hg : nookG a b true H = 2 * (b - a - 12) / (2 * H - 1) := by
      simp only [nookG, nookLm, nookPs, nookX, copyE, ↓reduceIte]; field_simp; ring
    rw [hu, hg, div_sub_div _ _ hn2 hn1, div_le_iff₀ (by positivity)]
    nlinarith

/-- The parameter point `[G, u − G, e]` of a copy nook. -/
noncomputable def nookPar (a b : ℚ) (ge : Bool) (H : ℚ) : List ℝ :=
  [((nookG a b ge H : ℚ) : ℝ), ((nookU a b ge H - nookG a b ge H : ℚ) : ℝ),
    ((3 / (2 * H - 3) : ℚ) : ℝ)]

/-- The grid abscissae of a copy nook. -/
noncomputable def nookφ (a b : ℚ) (ge : Bool) (H : ℚ) : ℕ → ℝ :=
  nφ ((nookX a b ge : ℚ) : ℝ) (nookPar a b ge H)

/-- The grid ordinates of a copy nook. -/
noncomputable def nookψ (a b : ℚ) (ge : Bool) (H : ℚ) : ℕ → ℝ :=
  nψ ((H : ℚ) : ℝ) (nookPar a b ge H)

section Nook

variable {a b H : ℚ} (hH : 1000 ≤ H) (h1 : H + 30 ≤ b - a) (h2 : b - a ≤ 2 * H - 600) (ge : Bool)
include hH h1 h2

theorem nookPar_dom : InDom nookDom (nookPar a b ge H) := by
  obtain ⟨hG, hGu, hu⟩ := nook_offsets hH h1 h2 ge
  have hgap := nook_gap hH h1 h2 ge
  have hd3 : 0 < 2 * H - 3 := by linarith
  have he : 0 < 3 / (2 * H - 3) := by positivity
  have he' : 3 / (2 * H - 3) ≤ 1 / 500 := by rw [div_le_iff₀ hd3]; linarith
  refine ⟨rfl, fun i hi => ?_⟩
  have hi' : i < 3 := hi
  interval_cases i
  · simp only [nookDom, nookPar, List.getD_cons_zero]
    refine ⟨by exact_mod_cast hG.le, fun h hh => ?_, fun h => by simp at h⟩
    simp only [Option.some.injEq] at hh; subst hh; exact_mod_cast hu.le.trans' hGu.le
  · simp only [nookDom, nookPar, List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨by push_cast; exact_mod_cast (by linarith : (0 : ℚ) ≤ nookU a b ge H - nookG a b ge H),
      fun h hh => ?_, fun _ => by exact_mod_cast (by linarith : (0 : ℚ) < nookU a b ge H - nookG a b ge H)⟩
    simp only [Option.some.injEq] at hh; subst hh; exact_mod_cast hgap
  · simp only [nookDom, nookPar, List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨by exact_mod_cast he.le, fun h hh => ?_, fun _ => by exact_mod_cast he⟩
    simp only [Option.some.injEq] at hh; subst hh; exact_mod_cast he'

omit hH h1 h2 in
theorem nookφ_eq {i : ℕ} (hi : i < 20) :
    nookφ a b ge H i = (((cnXe (nookX a b ge) (nookU a b ge H) (nookG a b ge H)
      (3 / (2 * H - 3))).getD i 0 : ℚ) : ℝ) := by
  simp only [nookφ, nφ, nookPar]
  interval_cases i <;>
    simp [nXs, cnXe, cnXs, nU, nG, nD, nE, nGE] <;> ring

omit hH h1 h2 in
theorem nookψ_eq {j : ℕ} (hj : j < 19) :
    nookψ a b ge H j = (((cnYe (nookG a b ge H) (3 / (2 * H - 3)) H).getD j 0 : ℚ) : ℝ) := by
  simp only [nookψ, nψ, nookPar]
  interval_cases j <;>
    simp [nYs, cnYe, cnYs, nYS, nYB, nS32, nS64, nG, nE, nGE] <;> ring

theorem nookφ_mono : StrictMonoOn (nookφ a b ge H) (Iio 20) := by
  obtain ⟨hG, hGu, hu⟩ := nook_offsets hH h1 h2 ge
  have hd3 : 0 < 2 * H - 3 := by linarith
  have he : 0 < 3 / (2 * H - 3) := by positivity
  have he' : 3 / (2 * H - 3) < 1 / 100 := by rw [div_lt_iff₀ hd3]; linarith
  have hm := strictMonoOn_getD_rat (cnXe_chain (xN := nookX a b ge) hG hGu hu he he')
  intro i hi j hj hij
  rw [nookφ_eq ge (by simpa using hi), nookφ_eq ge (by simpa using hj)]
  have hl : (cnXe (nookX a b ge) (nookU a b ge H) (nookG a b ge H) (3 / (2 * H - 3))).length = 20 :=
    rfl
  exact hm (by rw [Set.mem_Iio, hl]; simpa using hi) (by rw [Set.mem_Iio, hl]; simpa using hj) hij

theorem nookψ_mono : StrictMonoOn (nookψ a b ge H) (Iio 19) := by
  obtain ⟨hG, hGu, hu⟩ := nook_offsets hH h1 h2 ge
  have hd3 : 0 < 2 * H - 3 := by linarith
  have he : 0 < 3 / (2 * H - 3) := by positivity
  have he' : 3 / (2 * H - 3) < 1 / 100 := by rw [div_lt_iff₀ hd3]; linarith
  have hm := strictMonoOn_getD_rat (cnYe_chain (H := H) hG (hGu.trans hu) he he')
  intro i hi j hj hij
  rw [nookψ_eq ge (by simpa using hi), nookψ_eq ge (by simpa using hj)]
  have hl : (cnYe (nookG a b ge H) (3 / (2 * H - 3)) H).length = 19 := rfl
  exact hm (by rw [Set.mem_Iio, hl]; simpa using hi) (by rw [Set.mem_Iio, hl]; simpa using hj) hij

theorem nook_sound : nookOr.Sound (nookφ a b ge H) (nookψ a b ge H) :=
  nookOr_sound (nookPar_dom hH h1 h2 ge) _ _

omit hH h1 h2 in
/-- The realised rectangles of the zone of the nook (mirrored back) are the grid rectangles. -/
theorem nzone_rs :
    (nzone a b ge H).rs.map Rect.neg = cnRR.map (realR (nookφ a b ge H) (nookψ a b ge H)) := by
  simp only [nzone, cnFZone, gFZone, cnRR, List.map_map]
  refine List.map_congr_left (fun r _ => ?_)
  simp only [Function.comp_apply, realR, Rect.neg, cnφ, cnψ, neg_neg]
  rw [nookφ_eq ge (by omega), nookφ_eq ge (by omega), nookψ_eq ge (by omega), nookψ_eq ge (by omega)]

omit hH h1 h2 in
theorem nookBox_set {z : Point} :
    z ∈ nookBox.set (nookφ a b ge H) (nookψ a b ge H) ↔
      (-(nzone a b ge H).R < z.1 ∧ z.1 < -(nzone a b ge H).L ∧ 2 * (H : ℝ) - 1 / 4 < z.2) := by
  have e0 : nookφ a b ge H 0 = -(nzone a b ge H).R := by
    rw [nookφ_eq ge (by norm_num), nzone, cn_R, neg_neg]; simp [cnXe]
  have e19 : nookφ a b ge H 19 = -(nzone a b ge H).L := by
    rw [nookφ_eq ge (by norm_num), nzone, cn_L, neg_neg]; simp [cnXe, cnXs]
  have f0 : nookψ a b ge H 0 = 2 * (H : ℝ) - 1 / 4 := by
    rw [nookψ_eq ge (by norm_num)]; simp [cnYe]
  simp only [GBox.set, nookBox, Option.some.injEq, forall_eq', mem_ofPred_eq, reduceCtorEq,
    IsEmpty.forall_iff, forall_const, and_true, e0, e19, f0]

end Nook

/-! ### Certificates in a copy nook apply to the polygon -/

variable {n : ℕ} {Φ : List Constraint}

theorem nzone_mem {k : ℕ} (hk : k < n) {i : InputSeg} (hi : i ∈ inputsO n Φ) (hik : i.var = k) :
    nzone (varA Φ k) i.b i.ge (paramH n Φ) ∈ zcO n Φ := by
  unfold zcO
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_reverse,
    List.mem_range, beq_iff_eq]
  exact Or.inr ⟨k, hk, i, ⟨hi, hik⟩, rfl⟩

/-- The grid abscissae of the nook of input `i` (variable `k`). -/
noncomputable abbrev iφ (Φ : List Constraint) (H : ℚ) (k : ℕ) (i : InputSeg) : ℕ → ℝ :=
  nookφ (varA Φ k) i.b i.ge H

/-- The grid ordinates of the nook of input `i` (variable `k`). -/
noncomputable abbrev iψ (Φ : List Constraint) (H : ℚ) (k : ℕ) (i : InputSeg) : ℕ → ℝ :=
  nookψ (varA Φ k) i.b i.ge H

/-- **A grid certificate in a copy nook applies to the polygon.** -/
theorem sees_nookCert {k : ℕ} (hk : k < n) {i : InputSeg} (hi : i ∈ inputsO n Φ) (hik : i.var = k)
    {c : GCert} (hc : c.ok 20 19 nookOr = true) (hcs : c.cs.map Prod.fst = cnRR)
    (hU : c.U = [nookBox]) {w p : Point}
    (hw : w ∈ (realR (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) c.A).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p) :
    (∃ q ∈ c.cs, p ∈ (realR (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) q.1).set ∧
      p ∈ gcones (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) w q.2.2 ∧
      p ∈ nookBox.set (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i)) ∨
      (p ∈ goptCone (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) w c.C ∧
        p ∉ nookBox.set (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i)) := by
  classical
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  have hH := paramH_ge_q n Φ
  have hZ := nzone_mem hk hi hik
  set Z := nzone (varA Φ k) i.b i.ge (paramH n Φ) with hZdef
  have hφ := nookφ_mono hH d1 d2 i.ge
  have hψ := nookψ_mono hH d1 d2 i.ge
  have hO := nook_sound hH d1 d2 i.ge
  have hrect := region_rect_ceil hZ
  let Rest : List Rect := (regionRectsO n Φ).filter (fun r => r ∉ Z.rs.map Rect.neg)
  have key := GCert.sound hφ hψ hO hc hw (Rest := Rest.map Rect.set)
    (fun r hr => by obtain ⟨r', -, rfl⟩ := List.mem_map.1 hr; exact isClosed_rect_set r')
    (fun r hr z hz U hU' hzU => by
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      rw [hU, List.mem_singleton] at hU'
      subst hU'
      simp only [Rest, List.mem_filter, decide_eq_true_eq] at hr'
      rcases hrect r' hr'.1 with h | h
      · exact hr'.2 h
      · have := (nookBox_set (ge := i.ge)).1 hzU
        simp only [Hr] at h
        exact h z hz (by push_cast at this ⊢; exact this))
    (p := p) (fun s h0 h1 => by
      have hm : lerp w p s ∈ RU (regionRectsO n Φ) := by
        rw [← filledO]; exact hs (lerp_mem_segment' w p h0 h1)
      obtain ⟨r, hr, hz⟩ := hm
      by_cases hrZ : r ∈ Z.rs.map Rect.neg
      · left
        rw [nzone_rs, ← hcs, List.map_map] at hrZ
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hrZ
        exact ⟨q, hq, hz⟩
      · right
        exact ⟨r.set, List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by simpa using hrZ⟩, rfl⟩, hz⟩)
  rcases key with ⟨q, hq, h1, h2, h3⟩ | ⟨h1, h2⟩
  · left
    refine ⟨q, hq, h1, h2, ?_⟩
    have hk' : q.2.1 < c.U.length := by
      have := hc
      simp only [GCert.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
      exact (this.1.2 q hq).1.2
    rw [hU] at hk'
    have : q.2.1 = 0 := by simp at hk'; omega
    rw [this, hU] at h3
    exact h3
  · exact Or.inr ⟨h1, h2 _ (by rw [hU]; exact List.mem_singleton_self _)⟩

end

end ArtGallery.Orthogonal.Hard
