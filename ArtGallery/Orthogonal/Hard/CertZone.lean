module

public import ArtGallery.Orthogonal.Hard.Cert
public import ArtGallery.Orthogonal.Hard.RegionO

/-!
# Certificates in the zone of a template

The rectangles of the region of `polyO` that do not belong to a given zone lie outside the zone's
open box (`region_split_floor`, `region_split_ceil`).  The realised rectangles of a template zone
are the frame rectangles `tzLR` (ordinates affine in `H`).  Hence a certificate whose local
rectangles are those of a template zone and whose box is the zone's box applies to the polygon
(`sees_floorCert`, `sees_ceilCert`): every point seeing a target lies in one of the certified
cones.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-! ### Splitting a half comb at one of its zones -/

section Split

variable {y₀ T : ℝ}

theorem hc_split {e : ℝ} : ∀ {zs : List FZone} {s : ℝ}, (∀ Z ∈ zs, Z.Good y₀ T) → ZOrd s zs e →
    ∀ Z ∈ zs, ∃ A B : List Rect, hcRects y₀ T s zs e = A ++ Z.rs ++ B ∧
      (∀ r ∈ A, ∀ p ∈ r.set, p.1 ≤ Z.L) ∧ (∀ r ∈ B, ∀ p ∈ r.set, Z.R ≤ p.1)
  | [], _, _, _, Z, hZ => by simp at hZ
  | Z' :: zs, s, hG, h, Z, hZ => by
    have hG' : ∀ Z ∈ zs, Z.Good y₀ T := fun Z hZ => hG Z (List.mem_cons_of_mem _ hZ)
    have hZ'G := hG Z' List.mem_cons_self
    have hZ'LR : Z'.L < Z'.R := by linarith [hZ'G.Lf, hZ'G.fl, hZ'G.lR]
    rcases List.mem_cons.1 hZ with rfl | hZ'
    · refine ⟨[(s, Z.L, y₀, T)], hcRects y₀ T Z.R zs e, by simp [hcRects], ?_, ?_⟩
      · intro r hr p hp
        simp only [List.mem_singleton] at hr
        subst hr
        exact hp.2.1
      · intro r hr p hp
        exact (hc_box hG' h.2 r hr p hp).1
    · obtain ⟨A, B, hAB, hA, hB⟩ := hc_split hG' h.2 Z hZ'
      have hZL : Z'.R < Z.L := ((ZOrd.bounds hG' h.2).2 Z hZ').1
      refine ⟨(s, Z'.L, y₀, T) :: (Z'.rs ++ A), B, ?_, ?_, hB⟩
      · simp only [hcRects, hAB, List.cons_append, List.append_assoc]
      · intro r hr p hp
        simp only [List.mem_cons, List.mem_append] at hr
        rcases hr with rfl | hr | hr
        · have := hp.2.1
          simp only at this
          linarith
        · have := (hZ'G.box r hr p hp).2.1
          linarith
        · exact hA r hr p hp

end Split

variable {n : ℕ} {Φ : List Constraint}

/-- The parameter `H` as a real number. -/
noncomputable abbrev Hr (n : ℕ) (Φ : List Constraint) : ℝ := ((paramH n Φ : ℚ) : ℝ)

theorem Hr_ge (n : ℕ) (Φ : List Constraint) : 1000 ≤ Hr n Φ := by
  exact_mod_cast paramH_ge_q n Φ

theorem zord_zfO : ZOrd (xL n Φ : ℝ) (zfO n Φ) (xR n Φ : ℝ) :=
  zord_of (by exact_mod_cast xL_lt_xR n Φ) zfO_bounds zfO_pw

theorem zord_zcO : ZOrd (-(xR n Φ : ℝ)) (zcO n Φ) (-(xL n Φ : ℝ)) :=
  zord_of (by have := xL_lt_xR n Φ; have : (xL n Φ : ℝ) < xR n Φ := by exact_mod_cast this
              linarith) zcO_bounds zcO_pw

/-- **The rectangles outside a floor zone** avoid its open box. -/
theorem region_split_floor {Z : FZone} (hZ : Z ∈ zfO n Φ) : ∃ Rest : List Rect,
    (∀ p ∈ RU (regionRectsO n Φ), p ∈ RU Z.rs ∨ p ∈ RU Rest) ∧
    ∀ r ∈ Rest, ∀ p ∈ r.set, ¬ (Z.L < p.1 ∧ p.1 < Z.R ∧ p.2 < -1 / 4) := by
  have hH := Hr_ge n Φ
  obtain ⟨A, B, hAB, hA, hB⟩ := hc_split zfO_good zord_zfO Z hZ
  set Cl := (hcRects (-(2 * Hr n Φ)) (-(2 * Hr n Φ - 1 / 4)) (-(xR n Φ : ℝ)) (zcO n Φ)
    (-(xL n Φ : ℝ))).map Rect.neg with hCl
  refine ⟨((xL n Φ : ℝ), (xR n Φ : ℝ), -1 / 4, 2 * Hr n Φ - 1 / 4) :: (A ++ B ++ Cl), ?_, ?_⟩
  · rintro p ⟨r, hr, hp⟩
    simp only [regionRectsO, combRects, List.mem_cons, List.mem_append] at hr
    rw [hAB] at hr
    simp only [List.mem_append] at hr
    rcases hr with rfl | ((hr | hr) | hr) | hr
    · exact Or.inr ⟨_, by simp [Hr], hp⟩
    · exact Or.inr ⟨r, by simp [hr], hp⟩
    · exact Or.inl ⟨r, hr, hp⟩
    · exact Or.inr ⟨r, by simp [hr], hp⟩
    · exact Or.inr ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), hp⟩
  · intro r hr p hp ⟨h1, h2, h3⟩
    simp only [List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | (hr | hr) | hr
    · have := hp.2.2.1; simp only at this; linarith
    · linarith [hA r hr p hp]
    · linarith [hB r hr p hp]
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      have := (hc_box zcO_good zord_zcO r' hr' (-p) (Rect.mem_neg.1 hp)).2.2
      simp only [Prod.snd_neg] at this
      linarith

/-- **The rectangles outside a ceiling zone** (given mirrored) avoid its open box. -/
theorem region_split_ceil {Z : FZone} (hZ : Z ∈ zcO n Φ) : ∃ Rest : List Rect,
    (∀ p ∈ RU (regionRectsO n Φ), p ∈ RU (Z.rs.map Rect.neg) ∨ p ∈ RU Rest) ∧
    ∀ r ∈ Rest, ∀ p ∈ r.set, ¬ (-Z.R < p.1 ∧ p.1 < -Z.L ∧ 2 * Hr n Φ - 1 / 4 < p.2) := by
  have hH := Hr_ge n Φ
  obtain ⟨A, B, hAB, hA, hB⟩ := hc_split zcO_good zord_zcO Z hZ
  set Fl := hcRects (-1) (-1 / 4) (xL n Φ : ℝ) (zfO n Φ) (xR n Φ : ℝ) with hFl
  refine ⟨((xL n Φ : ℝ), (xR n Φ : ℝ), -1 / 4, 2 * Hr n Φ - 1 / 4) :: (Fl ++ (A ++ B).map Rect.neg),
    ?_, ?_⟩
  · rintro p ⟨r, hr, hp⟩
    simp only [regionRectsO, combRects, List.mem_cons, List.mem_append] at hr
    rw [hAB] at hr
    simp only [List.map_append, List.mem_append] at hr
    rcases hr with rfl | hr | ((hr | hr) | hr)
    · exact Or.inr ⟨_, by simp [Hr], hp⟩
    · exact Or.inr ⟨r, by simp [hFl, hr], hp⟩
    · exact Or.inr ⟨r, by simp only [List.mem_cons, List.mem_append, List.map_append]; tauto, hp⟩
    · exact Or.inl ⟨r, hr, hp⟩
    · exact Or.inr ⟨r, by simp only [List.mem_cons, List.mem_append, List.map_append]; tauto, hp⟩
  · intro r hr p hp ⟨h1, h2, h3⟩
    simp only [List.mem_cons, List.mem_append, List.map_append] at hr
    rcases hr with rfl | hr | (hr | hr)
    · have := hp.2.2.2; simp only at this; linarith
    · have := (hc_box zfO_good zord_zfO r hr p hp).2.2
      linarith
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      have := hA r' hr' (-p) (Rect.mem_neg.1 hp)
      simp only [Prod.fst_neg] at this
      linarith
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      have := hB r' hr' (-p) (Rect.mem_neg.1 hp)
      simp only [Prod.fst_neg] at this
      linarith

/-! ### Template zones as frame rectangles -/

/-- The rectangles of a template zone in the frame of the template origin; a mirrored (ceiling)
zone is mapped back to the plane. -/
def tzLR (t : ITmpl) (zt : TZone) (mirror : Bool) : List LR :=
  zt.zone.rects.map fun r =>
    let x : ℕ → ℚ := fun i => (zt.xs.getD i 0 : ℚ) / t.D
    let y : ℕ → AH := fun j => (((zt.ys.getD j (0, 0)).1 : ℚ) / t.D,
      -(((zt.ys.getD j (0, 0)).2 : ℚ) / t.D))
    if mirror then ⟨-x r.2.1, -x r.1, (-(y r.2.2.2).1, -(y r.2.2.2).2),
      (-(y r.2.2.1).1, -(y r.2.2.1).2)⟩
    else ⟨x r.1, x r.2.1, y r.2.2.1, y r.2.2.2⟩

theorem fzone_rs (t : ITmpl) (H ox : ℚ) :
    (fzone t H ox).rs = (tzLR t (fz t) false).map (LR.real (ox : ℝ) (H : ℝ)) := by
  simp only [fzone, tzFZone, gFZone, tzLR, List.map_map]
  refine List.map_congr_left (fun r _ => ?_)
  simp only [Function.comp_apply, realR, tzX, tzY, LR.real, AH.ev, Bool.false_eq_true, ↓reduceIte]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only; push_cast; ring
  · simp only; push_cast; ring
  · simp only; push_cast; ring
  · simp only; push_cast; ring

theorem czone_rs (t : ITmpl) (H b : ℚ) :
    (czone t H b).rs.map Rect.neg = (tzLR t (cz t) true).map (LR.real (b : ℝ) (H : ℝ)) := by
  simp only [czone, tzFZone, gFZone, tzLR, List.map_map]
  refine List.map_congr_left (fun r _ => ?_)
  simp only [Function.comp_apply, realR, tzX, tzY, LR.real, AH.ev, Rect.neg, ↓reduceIte]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only; push_cast; ring
  · simp only; push_cast; ring
  · simp only; push_cast; ring
  · simp only; push_cast; ring

/-- The open box of a floor template zone (frame of the template origin). -/
def floorBoxL (t : ITmpl) : LBox := ⟨some (t.xmin - 1 / 8), some (t.xmax + 1 / 8), none, some (-1 / 4, 0)⟩

/-- The open box of a ceiling template zone (frame of the template origin). -/
def ceilBoxL (t : ITmpl) : LBox := ⟨some (t.xmin - 1 / 8), some (t.xmax + 1 / 8), some (-1 / 4, 2), none⟩

/-! ### Certificates in a template zone -/

theorem lerp_mem_segment' (w p : Point) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    lerp w p t ∈ ArtGallery.segment w p := ⟨t, h0, h1, rfl⟩

/-- **A certificate in a floor template zone applies to the polygon.** -/
theorem sees_floorCert {t : ITmpl} (ht : t ∈ allFloorTmpls) {c : LCert} (hc : c.ok = true)
    (hcs : c.cs.map Prod.fst = tzLR t (fz t) false) (hU : c.U = [floorBoxL t]) {ox : ℚ}
    (hZ : fzone t (paramH n Φ) ox ∈ zfO n Φ) {w p : Point}
    (hw : w ∈ (c.A.real ox (Hr n Φ)).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p) :
    (∃ q ∈ c.cs, p ∈ (q.1.real ox (Hr n Φ)).set ∧ p ∈ conesSet ox (Hr n Φ) w q.2.2) ∨
      (p ∈ optCone ox (Hr n Φ) w c.C ∧ ∀ U ∈ c.U, p ∉ U.set ox (Hr n Φ)) := by
  obtain ⟨Rest, hcov, hout⟩ := region_split_floor hZ
  refine LCert.sound hc (Hr_ge n Φ) ox hw (Rest := Rest.map Rect.set)
    (fun r hr => by obtain ⟨r', -, rfl⟩ := List.mem_map.1 hr; exact isClosed_rect_set r')
    (fun r hr z hz U hU' hzU => ?_) (fun s h0 h1 => ?_)
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    rw [hU, List.mem_singleton] at hU'
    subst hU'
    obtain ⟨hx0, hx1, -, hy1⟩ := hzU
    refine hout r' hr' z hz ⟨?_, ?_, ?_⟩
    · rw [fzone_L ht]; have := hx0 _ rfl; push_cast at this ⊢; linarith
    · rw [fzone_R ht]; have := hx1 _ rfl; push_cast at this ⊢; linarith
    · have := hy1 _ rfl; simp only [AH.ev, Hr] at this ⊢; push_cast at this ⊢; linarith
  · have hm : lerp w p s ∈ RU (regionRectsO n Φ) := by
      rw [← filledO]; exact hs (lerp_mem_segment' w p h0 h1)
    rcases hcov _ hm with ⟨r, hr, hz⟩ | ⟨r, hr, hz⟩
    · left
      rw [fzone_rs, ← hcs, List.map_map] at hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact ⟨q, hq, hz⟩
    · exact Or.inr ⟨r.set, List.mem_map.2 ⟨r, hr, rfl⟩, hz⟩

/-- **A certificate in a ceiling template zone applies to the polygon.** -/
theorem sees_ceilCert {t : ITmpl} (ht : t ∈ allCeilTmpls) {c : LCert} (hc : c.ok = true)
    (hcs : c.cs.map Prod.fst = tzLR t (cz t) true) (hU : c.U = [ceilBoxL t]) {b : ℚ}
    (hZ : czone t (paramH n Φ) b ∈ zcO n Φ) {w p : Point}
    (hw : w ∈ (c.A.real b (Hr n Φ)).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p) :
    (∃ q ∈ c.cs, p ∈ (q.1.real b (Hr n Φ)).set ∧ p ∈ conesSet b (Hr n Φ) w q.2.2) ∨
      (p ∈ optCone b (Hr n Φ) w c.C ∧ ∀ U ∈ c.U, p ∉ U.set b (Hr n Φ)) := by
  obtain ⟨Rest, hcov, hout⟩ := region_split_ceil hZ
  refine LCert.sound hc (Hr_ge n Φ) b hw (Rest := Rest.map Rect.set)
    (fun r hr => by obtain ⟨r', -, rfl⟩ := List.mem_map.1 hr; exact isClosed_rect_set r')
    (fun r hr z hz U hU' hzU => ?_) (fun s h0 h1 => ?_)
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    rw [hU, List.mem_singleton] at hU'
    subst hU'
    obtain ⟨hx0, hx1, hy0, -⟩ := hzU
    refine hout r' hr' z hz ⟨?_, ?_, ?_⟩
    · rw [czone_R ht]; have := hx0 _ rfl; push_cast at this ⊢; linarith
    · rw [czone_L ht]; have := hx1 _ rfl; push_cast at this ⊢; linarith
    · have := hy0 _ rfl; simp only [AH.ev, Hr] at this ⊢; push_cast at this ⊢; linarith
  · have hm : lerp w p s ∈ RU (regionRectsO n Φ) := by
      rw [← filledO]; exact hs (lerp_mem_segment' w p h0 h1)
    rcases hcov _ hm with ⟨r, hr, hz⟩ | ⟨r, hr, hz⟩
    · left
      rw [czone_rs, ← hcs, List.map_map] at hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact ⟨q, hq, hz⟩
    · exact Or.inr ⟨r.set, List.mem_map.2 ⟨r, hr, rfl⟩, hz⟩

/-! ### Certificates in a group of template zones -/

/-- Rectangle-wise form of `region_split_floor`. -/
theorem region_rect_floor {Z : FZone} (hZ : Z ∈ zfO n Φ) :
    ∀ r ∈ regionRectsO n Φ, r ∈ Z.rs ∨ ∀ p ∈ r.set, ¬ (Z.L < p.1 ∧ p.1 < Z.R ∧ p.2 < -1 / 4) := by
  have hH := Hr_ge n Φ
  obtain ⟨A, B, hAB, hA, hB⟩ := hc_split zfO_good zord_zfO Z hZ
  intro r hr
  by_cases hrZ : r ∈ Z.rs
  · exact Or.inl hrZ
  right
  intro p hp ⟨h1, h2, h3⟩
  simp only [regionRectsO, combRects, List.mem_cons, List.mem_append] at hr
  rw [hAB] at hr
  simp only [List.mem_append] at hr
  rcases hr with rfl | ((hr | hr) | hr) | hr
  · have := hp.2.2.1; simp only at this; linarith
  · linarith [hA r hr p hp]
  · exact hrZ hr
  · linarith [hB r hr p hp]
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    have := (hc_box zcO_good zord_zcO r' hr' (-p) (Rect.mem_neg.1 hp)).2.2
    simp only [Prod.snd_neg] at this
    linarith

/-- Rectangle-wise form of `region_split_ceil`. -/
theorem region_rect_ceil {Z : FZone} (hZ : Z ∈ zcO n Φ) :
    ∀ r ∈ regionRectsO n Φ, r ∈ Z.rs.map Rect.neg ∨
      ∀ p ∈ r.set, ¬ (-Z.R < p.1 ∧ p.1 < -Z.L ∧ 2 * Hr n Φ - 1 / 4 < p.2) := by
  have hH := Hr_ge n Φ
  obtain ⟨A, B, hAB, hA, hB⟩ := hc_split zcO_good zord_zcO Z hZ
  intro r hr
  by_cases hrZ : r ∈ Z.rs.map Rect.neg
  · exact Or.inl hrZ
  right
  intro p hp ⟨h1, h2, h3⟩
  simp only [regionRectsO, combRects, List.mem_cons, List.mem_append] at hr
  rw [hAB] at hr
  simp only [List.map_append, List.mem_append] at hr
  rcases hr with rfl | hr | ((hr | hr) | hr)
  · have := hp.2.2.2; simp only at this; linarith
  · have := (hc_box zfO_good zord_zfO r hr p hp).2.2
    linarith
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    have := hA r' hr' (-p) (Rect.mem_neg.1 hp)
    simp only [Prod.fst_neg] at this
    linarith
  · exact hrZ hr
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    have := hB r' hr' (-p) (Rect.mem_neg.1 hp)
    simp only [Prod.fst_neg] at this
    linarith

/-- Translation of a frame rectangle by `δ`. -/
def LR.shift (δ : ℚ) (r : LR) : LR := ⟨r.x0 + δ, r.x1 + δ, r.y0, r.y1⟩

theorem LR.real_shift (ox H : ℝ) (δ : ℚ) (r : LR) :
    (r.shift δ).real ox H = r.real (ox + δ) H := by
  simp only [LR.shift, LR.real]; push_cast; ring_nf

/-- Translation of an open box by `δ`. -/
def LBox.shift (δ : ℚ) (U : LBox) : LBox := ⟨U.x0.map (· + δ), U.x1.map (· + δ), U.y0, U.y1⟩

/-- A zone of a template group: a floor (`ceil = false`) or ceiling template at offset `δ` from
the origin of the group. -/
structure GZ where
  t : ITmpl
  ceil : Bool
  δ : ℚ

/-- The rectangles of a group zone in the frame of the group. -/
def GZ.rects (g : GZ) : List LR :=
  (tzLR g.t (if g.ceil then cz g.t else fz g.t) g.ceil).map (LR.shift g.δ)

/-- The open box of a group zone in the frame of the group. -/
def GZ.box (g : GZ) : LBox := (if g.ceil then ceilBoxL g.t else floorBoxL g.t).shift g.δ

/-- The rectangles of a group, with the index of their zone. -/
def groupLR (gs : List GZ) : List (LR × ℕ) :=
  (List.range gs.length).flatMap fun k => ((gs.getD k ⟨⟨1, []⟩, false, 0⟩).rects).map (·, k)

/-- The zone of a group zone is a zone of the polygon. -/
def GZ.InPoly (n : ℕ) (Φ : List Constraint) (ox : ℚ) (g : GZ) : Prop :=
  if g.ceil then g.t ∈ allCeilTmpls ∧ czone g.t (paramH n Φ) (ox + g.δ) ∈ zcO n Φ
  else g.t ∈ allFloorTmpls ∧ fzone g.t (paramH n Φ) (ox + g.δ) ∈ zfO n Φ

/-- The real rectangles of a group zone. -/
theorem GZ.rects_real (g : GZ) (ox : ℚ) :
    (g.rects.map (LR.real ox (Hr n Φ))) =
      if g.ceil then (czone g.t (paramH n Φ) (ox + g.δ)).rs.map Rect.neg
      else (fzone g.t (paramH n Φ) (ox + g.δ)).rs := by
  unfold GZ.rects
  cases hc : g.ceil
  · simp only [Bool.false_eq_true, ↓reduceIte, List.map_map]
    rw [fzone_rs]
    refine List.map_congr_left (fun r _ => ?_)
    simp only [Function.comp_apply, LR.real_shift]; push_cast; rfl
  · simp only [↓reduceIte, List.map_map]
    rw [czone_rs]
    refine List.map_congr_left (fun r _ => ?_)
    simp only [Function.comp_apply, LR.real_shift]; push_cast; rfl

/-- Points outside the real box of a group zone avoid it, from the zone's region lemma. -/
theorem GZ.box_set {g : GZ} {ox : ℚ} (hg : g.InPoly n Φ ox) {p : Point}
    (hp : p ∈ g.box.set ox (Hr n Φ)) :
    if g.ceil then -(czone g.t (paramH n Φ) (ox + g.δ)).R < p.1 ∧
        p.1 < -(czone g.t (paramH n Φ) (ox + g.δ)).L ∧ 2 * Hr n Φ - 1 / 4 < p.2
    else (fzone g.t (paramH n Φ) (ox + g.δ)).L < p.1 ∧
        p.1 < (fzone g.t (paramH n Φ) (ox + g.δ)).R ∧ p.2 < -1 / 4 := by
  unfold GZ.InPoly at hg
  unfold GZ.box at hp
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hp
  cases hc : g.ceil
  · rw [hc] at hg hx0 hx1 hy0 hy1
    simp only [Bool.false_eq_true, ↓reduceIte] at hg hx0 hx1 hy0 hy1 ⊢
    simp only [LBox.shift, floorBoxL, Option.map_some] at hx0 hx1 hy0 hy1
    refine ⟨?_, ?_, ?_⟩
    · rw [fzone_L hg.1]; have := hx0 _ rfl; push_cast at this ⊢; linarith
    · rw [fzone_R hg.1]; have := hx1 _ rfl; push_cast at this ⊢; linarith
    · have := hy1 _ rfl; simp only [AH.ev, Hr] at this ⊢; push_cast at this ⊢; linarith
  · rw [hc] at hg hx0 hx1 hy0 hy1
    simp only [↓reduceIte] at hg hx0 hx1 hy0 hy1 ⊢
    simp only [LBox.shift, ceilBoxL, Option.map_some] at hx0 hx1 hy0 hy1
    refine ⟨?_, ?_, ?_⟩
    · rw [czone_R hg.1]; have := hx0 _ rfl; push_cast at this ⊢; linarith
    · rw [czone_L hg.1]; have := hx1 _ rfl; push_cast at this ⊢; linarith
    · have := hy0 _ rfl; simp only [AH.ev, Hr] at this ⊢; push_cast at this ⊢; linarith

/-- **A certificate over a group of template zones applies to the polygon.** -/
theorem sees_groupCert {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox) {c : LCert}
    (hc : c.ok = true) (hcs : c.cs.map (fun q => (q.1, q.2.1)) = groupLR gs)
    (hU : c.U = gs.map GZ.box) {w p : Point} (hw : w ∈ (c.A.real ox (Hr n Φ)).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w p) :
    (∃ q ∈ c.cs, p ∈ (q.1.real ox (Hr n Φ)).set ∧ p ∈ conesSet ox (Hr n Φ) w q.2.2) ∨
      (p ∈ optCone ox (Hr n Φ) w c.C ∧ ∀ U ∈ c.U, p ∉ U.set ox (Hr n Φ)) := by
  classical
  -- the rest: rectangles of the region in no zone of the group
  set Rest := (regionRectsO n Φ).filter (fun r => decide (∀ g ∈ gs, r ∉ g.rects.map
    (LR.real ox (Hr n Φ)))) with hRest
  refine LCert.sound hc (Hr_ge n Φ) ox hw (Rest := Rest.map Rect.set)
    (fun r hr => by obtain ⟨r', -, rfl⟩ := List.mem_map.1 hr; exact isClosed_rect_set r')
    (fun r hr z hz U hU' hzU => ?_) (fun s h0 h1 => ?_)
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    rw [hU] at hU'
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
  · have hm : lerp w p s ∈ RU (regionRectsO n Φ) := by
      rw [← filledO]; exact hs (lerp_mem_segment' w p h0 h1)
    obtain ⟨r, hr, hz⟩ := hm
    by_cases hloc : ∃ g ∈ gs, r ∈ g.rects.map (LR.real ox (Hr n Φ))
    · left
      obtain ⟨g, hg, hrg⟩ := hloc
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hrg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      have hmem : (l, k) ∈ groupLR gs := by
        simp only [groupLR, List.mem_flatMap, List.mem_range, List.mem_map]
        refine ⟨k, hk, l, ?_, rfl⟩
        rw [List.getD_eq_getElem _ _ hk]; exact hl
      rw [← hcs] at hmem
      obtain ⟨q, hq, hql⟩ := List.mem_map.1 hmem
      simp only [Prod.mk.injEq] at hql
      exact ⟨q, hq, by rw [hql.1]; exact hz⟩
    · right
      push Not at hloc
      refine ⟨r.set, List.mem_map.2 ⟨r, ?_, rfl⟩, hz⟩
      simp only [hRest, List.mem_filter, decide_eq_true_eq]
      exact ⟨hr, hloc⟩

end

end ArtGallery.Orthogonal.Hard
