module

public import ArtGallery.Orthogonal.Hard.PinAssm

/-!
# Spots from cutter segments (generic)

A guard on a vertical line `x = ox + x_z` seeing every point of a cutter segment `σ` near its tip
`K` (the open segment `{c} × (y₀, y₁)`, the tip being an end) is bounded by the limit of the
escape cones of the points of `σ` as they tend to `K`:

* `nonneg_of_affine`, `cone_tip`: the escape cone of the tip contains every point lying in the
  escape cones of all points of `σ` near the tip (the half-planes are affine in the target);
* `tipHiB`, `tipLoB`: a half-plane of the escape cone of the tip bounds the ordinates of the
  points of the line `x = ox + x_z` (an exact computation in `ℚ × ℚ`, robust in `H ≥ 1000`);
* `seg_hi`, `seg_lo`: the spot bounds.  Points outside the strip `[-1/4, 2H - 1/4]` are excluded
  by a robustly unseen rectangle (`rectUnseenB`); inside the strip a viewer is in no box of the
  group (`boxesOutB`), hence in the escape cone.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-! ### Limits of affine inequalities -/

/-- An affine function nonnegative on `(0, ε)` is nonnegative at `0`. -/
theorem nonneg_of_affine {a c ε : ℝ} (hε : 0 < ε) (h : ∀ t, 0 < t → t < ε → 0 ≤ a + c * t) :
    0 ≤ a := by
  by_contra ha
  push Not at ha
  set t := min (ε / 2) (-a / (2 * (|c| + 1))) with ht
  have hc1 : 0 < |c| + 1 := by positivity
  have ht0 : 0 < t := lt_min (by linarith) (div_pos (by linarith) (by positivity))
  have h1 := h t ht0 (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have h2 : t ≤ -a / (2 * (|c| + 1)) := min_le_right _ _
  rw [le_div_iff₀ (by positivity)] at h2
  have h3 : c * t ≤ |c| * t := mul_le_mul_of_nonneg_right (le_abs_self c) ht0.le
  nlinarith [abs_nonneg c]

/-- **The escape cone of the tip.** A point in the cones of all targets `(X, y₀ + s t)`,
`0 < t < ε`, is in the cone of `(X, y₀)`. -/
theorem cone_tip {ox H X y0 ε s : ℝ} (hε : 0 < ε) {K : List HP} {p : Point}
    (h : ∀ t, 0 < t → t < ε → p ∈ cone ox H (X, y0 + s * t) K) : p ∈ cone ox H (X, y0) K := by
  intro hp hhp
  rcases hp with ⟨_ | u, _ | v⟩
  · simp only [HP.set, HE.pt, mem_ofPred_eq, det]; nlinarith
  · refine nonneg_of_affine hε (c := s * ((p.1 - X) - ((v.real ox H).1 - X))) fun t h1 h2 => ?_
    have := h t h1 h2 _ hhp
    simp only [HP.set, HE.pt, mem_ofPred_eq, det] at this ⊢
    linear_combination this
  · refine nonneg_of_affine hε (c := -(p.1 - (u.real ox H).1) * s) fun t h1 h2 => ?_
    have := h t h1 h2 _ hhp
    simp only [HP.set, HE.pt, mem_ofPred_eq, det] at this ⊢
    linear_combination this
  · have := h (ε / 2) (by linarith) (by linarith) _ hhp
    simpa only [HP.set, HE.pt, mem_ofPred_eq] using this

/-! ### Bounds from a half-plane of the tip cone -/

/-- The bound `β / α` of the half-plane `h` (endpoints `e₁ e₂`, `none` = the tip) on the line
`x = x_z`: the half-plane is `α y ≥ β` with `α = e₂.x − e₁.x`. -/
def tipBound (h : HP) (tip : LP) (xz : ℚ) : ℚ × AH :=
  let e1 := h.1.getD tip
  let e2 := h.2.getD tip
  let α := e2.1 - e1.1
  let l := xz - e1.1
  (α, ((α * e1.2.1 + l * (e2.2.1 - e1.2.1)) / α, (α * e1.2.2 + l * (e2.2.2 - e1.2.2)) / α))

/-- The half-plane bounds the line from above by `B`. -/
def tipHiB (h : HP) (tip : LP) (xz : ℚ) (B : AH) : Bool :=
  decide ((tipBound h tip xz).1 < 0) && AH.le (tipBound h tip xz).2 B

/-- The half-plane bounds the line from below by `B`. -/
def tipLoB (h : HP) (tip : LP) (xz : ℚ) (B : AH) : Bool :=
  decide (0 < (tipBound h tip xz).1) && AH.le B (tipBound h tip xz).2

theorem HE.pt_tip (ox H : ℝ) (tip : LP) (e : HE) : e.pt ox H (tip.real ox H) = (e.getD tip).real ox H := by
  cases e <;> rfl

/-- The half-plane at the tip as `α y ≥ α b`. -/
theorem tipBound_spec (h : HP) (tip : LP) (xz : ℚ) {ox H : ℝ} {z : Point} (hz : z.1 = ox + xz)
    (hd : 0 ≤ det (h.1.pt ox H (tip.real ox H)) (h.2.pt ox H (tip.real ox H)) z)
    (hα : (tipBound h tip xz).1 ≠ 0) :
    ((tipBound h tip xz).1 : ℝ) * (tipBound h tip xz).2.ev H ≤ ((tipBound h tip xz).1 : ℝ) * z.2 := by
  rw [HE.pt_tip, HE.pt_tip] at hd
  simp only [tipBound] at hα ⊢
  set e1 := h.1.getD tip
  set e2 := h.2.getD tip
  have hα' : ((e2.1 - e1.1 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hα
  simp only [det, LP.real, AH.ev, hz] at hd
  simp only [AH.ev]
  push_cast at hα' ⊢
  rw [mul_add, mul_div_cancel₀ _ hα', ← mul_assoc, mul_div_cancel₀ _ hα']
  linarith

theorem tipHiB_sound {h : HP} {tip : LP} {xz : ℚ} {B : AH} (hb : tipHiB h tip xz B = true)
    {ox H : ℝ} (hH : 1000 ≤ H) {z : Point} (hz : z.1 = ox + xz)
    (hd : 0 ≤ det (h.1.pt ox H (tip.real ox H)) (h.2.pt ox H (tip.real ox H)) z) : z.2 ≤ B.ev H := by
  simp only [tipHiB, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hs := tipBound_spec h tip xz hz hd hb.1.ne
  have hα : ((tipBound h tip xz).1 : ℝ) < 0 := by exact_mod_cast hb.1
  have := AH.le_sound hb.2 hH
  nlinarith

theorem tipLoB_sound {h : HP} {tip : LP} {xz : ℚ} {B : AH} (hb : tipLoB h tip xz B = true)
    {ox H : ℝ} (hH : 1000 ≤ H) {z : Point} (hz : z.1 = ox + xz)
    (hd : 0 ≤ det (h.1.pt ox H (tip.real ox H)) (h.2.pt ox H (tip.real ox H)) z) : B.ev H ≤ z.2 := by
  simp only [tipLoB, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hs := tipBound_spec h tip xz hz hd hb.1.ne'
  have hα : (0 : ℝ) < (tipBound h tip xz).1 := by exact_mod_cast hb.1
  have := AH.le_sound hb.2 hH
  nlinarith

/-! ### Unseen rectangles for a part of the target -/

/-- `A'` lies in `A` (robustly). -/
def LR.subB (A' A : LR) : Bool :=
  decide (A.x0 ≤ A'.x0 ∧ A'.x1 ≤ A.x1) && AH.le A.y0 A'.y0 && AH.le A'.y1 A.y1

theorem LR.subB_sound {A' A : LR} (h : A'.subB A = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {w : Point} (hw : w ∈ (A'.real ox H).set) : w ∈ (A.real ox H).set := by
  simp only [LR.subB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨w1, w2, w3, w4⟩ := hw
  simp only [LR.real] at w1 w2 w3 w4 ⊢
  have : (A.x0 : ℝ) ≤ A'.x0 := by exact_mod_cast h1
  have : (A'.x1 : ℝ) ≤ A.x1 := by exact_mod_cast h2
  have := AH.le_sound h3 hH
  have := AH.le_sound h4 hH
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- No point of `S` sees a point of the part `A'` of the target (robustly). -/
def rectUnseenSubB (c : LCert) (A' S : LR) : Bool :=
  A'.subB c.A &&
  c.cs.all (fun q => q.2.2.isEmpty || match q.1.inter S with
    | none => false
    | some none => true
    | some (some X) => q.2.2.all fun K => K.any fun h => hpNegr A' h X) &&
  (c.U.any (fun U => S.corners.all U.memB) || match c.C with
    | none => true
    | some K => K.any fun h => hpNegr A' h S)

variable {n : ℕ} {Φ : List Constraint} in
/-- **A rectangle robustly unseen from a part of the target.** -/
theorem rectUnseenSub_sound {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox)
    (hb : boxesSepB (gs.map GZ.box) = true) {T : TCert}
    (ok : (T.cert gs).ok = true) (l : T.cones.length = (groupLR gs).length) {A' S : LR}
    (hS : rectUnseenSubB (T.cert gs) A' S = true) {w z : Point} (hw : w ∈ (A'.real ox (Hr n Φ)).set)
    (hz : z ∈ (S.real ox (Hr n Φ)).set)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees w z) : False := by
  have hH := Hr_ge n Φ
  simp only [rectUnseenSubB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.any_eq_true,
    List.isEmpty_iff] at hS
  obtain ⟨⟨hsub, hz1⟩, hz2⟩ := hS
  have hwA : w ∈ (T.A.real ox (Hr n Φ)).set := LR.subB_sound hsub hH _ hw
  rcases TCert.sees hgs ok l hb hwA hs with ⟨q, hq, hp, hc, -⟩ | ⟨hC, hout⟩
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

/-- The part of a target segment within `1/8` of its lower end. -/
def LR.loPart (A : LR) : LR := ⟨A.x0, A.x1, A.y0, (A.y0.1 + 1 / 8, A.y0.2)⟩

/-- The part of a target segment within `1/8` of its upper end. -/
def LR.hiPart (A : LR) : LR := ⟨A.x0, A.x1, (A.y1.1 - 1 / 8, A.y1.2), A.y1⟩

/-! ### Boxes of a group outside the strip -/

/-- Every box of the group lies below `y = −1/4` or above `y = 2H − 1/4`. -/
def boxesOutB (gs : List GZ) : Bool :=
  gs.all fun g => (g.box.y1.any fun e => AH.le e (-1 / 4, 0)) ||
    (g.box.y0.any fun e => AH.le (-1 / 4, 2) e)

theorem box_y_of_out {gs : List GZ} (h : boxesOutB gs = true) {ox H : ℝ} (hH : 1000 ≤ H)
    {U : LBox} (hU : U ∈ gs.map GZ.box) {p : Point} (hp : p ∈ U.set ox H) :
    p.2 < -1 / 4 ∨ 2 * H - 1 / 4 < p.2 := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hU
  simp only [boxesOutB, List.all_eq_true, Bool.or_eq_true, Option.any_eq_true] at h
  obtain ⟨-, -, hy0, hy1⟩ := hp
  rcases h g hg with ⟨e, he, hle⟩ | ⟨e, he, hle⟩
  · left
    have := AH.le_sound hle hH
    have := hy1 e he
    simp only [AH.ev] at *; push_cast at *; linarith
  · right
    have := AH.le_sound hle hH
    have := hy0 e he
    simp only [AH.ev] at *; push_cast at *; linarith

variable {n : ℕ} {Φ : List Constraint}

/-! ### The spot bounds -/

/-- **Upper spot bound** from a cutter segment whose tip is its upper end. -/
theorem seg_hi {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox)
    (hb : boxesSepB (gs.map GZ.box) = true) (hout : boxesOutB gs = true) {T : TCert}
    (ok : (T.cert gs).ok = true) (l : T.cones.length = (groupLR gs).length) {xz : ℚ} {B : AH}
    (hA : T.A.x0 = T.A.x1) (hne : AH.le (T.A.y0.1 + 1 / 8, T.A.y0.2) T.A.y1 = true)
    (hU : rectUnseenSubB (T.cert gs) T.A.hiPart ⟨xz, xz, (-1 / 4, 2), (0, 3)⟩ = true)
    {K : List HP} (hC : T.C = some K)
    (htip : K.any (fun h => tipHiB h (T.A.x0, T.A.y1) xz B) = true) (hB : AH.le (-1 / 4, 0) B = true)
    {p : Point} (hp : p ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (hx : p.1 = (ox : ℝ) + xz)
    (hs : ∀ y : ℝ, T.A.y0.ev (Hr n Φ) < y → y < T.A.y1.ev (Hr n Φ) →
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p ((ox : ℝ) + T.A.x0, y)) :
    p.2 ≤ B.ev (Hr n Φ) := by
  obtain ⟨h, hh, htip⟩ := List.any_eq_true.1 htip
  have hH := Hr_ge n Φ
  have hHc : Hr n Φ = (paramH n Φ : ℝ) := Rat.cast_natCast _
  have hY := strip_bound n Φ p hp
  simp only [yMin, yMax, AH.ev] at hY
  push_cast at hY
  have hlt : T.A.y0.ev (Hr n Φ) + 1 / 8 ≤ T.A.y1.ev (Hr n Φ) := by
    have := AH.le_sound hne hH; simp only [AH.ev] at this ⊢; push_cast at this ⊢; linarith
  have hB' : (-1 / 4 : ℝ) ≤ B.ev (Hr n Φ) := by
    have := AH.le_sound hB hH; simp only [AH.ev] at this ⊢; push_cast at this ⊢; linarith
  have hAx : ∀ y, T.A.y0.ev (Hr n Φ) ≤ y → y ≤ T.A.y1.ev (Hr n Φ) →
      (((ox : ℝ) + T.A.x0, y) : Point) ∈ (T.A.real ox (Hr n Φ)).set := by
    intro y h0 h1
    refine ⟨le_rfl, ?_, h0, h1⟩
    simp only [LR.real, hA]; exact le_rfl
  by_contra hgt
  push Not at hgt
  by_cases hhi : 2 * Hr n Φ - 1 / 4 ≤ p.2
  · have hm : (((ox : ℝ) + T.A.x0, T.A.y1.ev (Hr n Φ) - 1 / 16) : Point) ∈
        (T.A.hiPart.real ox (Hr n Φ)).set := by
      refine ⟨le_rfl, ?_, ?_, ?_⟩
      · simp only [LR.real, LR.hiPart, hA]; exact le_rfl
      · simp only [LR.real, LR.hiPart, AH.ev]; push_cast; linarith
      · simp only [LR.real, LR.hiPart]; linarith
    refine rectUnseenSub_sound hgs hb ok l hU hm (z := p) ?_
      (sees_symm (hs _ (by linarith) (by linarith)))
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [LR.real, AH.ev] <;> push_cast <;> linarith
  · push Not at hhi
    have hcone : p ∈ cone ox (Hr n Φ) ((ox : ℝ) + T.A.x0, T.A.y1.ev (Hr n Φ)) K := by
      refine cone_tip (s := -1) (ε := T.A.y1.ev (Hr n Φ) - T.A.y0.ev (Hr n Φ)) (by linarith)
        fun t h1 h2 => ?_
      have hw := hAx (T.A.y1.ev (Hr n Φ) + -1 * t) (by linarith) (by linarith)
      rcases TCert.sees hgs ok l hb hw (sees_symm (hs _ (by linarith) (by linarith))) with
        ⟨q, hq, -, -, hpU⟩ | ⟨hpC, -⟩
      · have hk' : q.2.1 < (gs.map GZ.box).length := LCert.box_lt ok hq
        rw [List.getD_eq_getElem _ _ hk'] at hpU
        rcases box_y_of_out hout hH (List.getElem_mem hk') hpU with h | h <;> linarith
      · rw [hC] at hpC; exact hpC
    have hd := hcone h hh
    have := tipHiB_sound htip hH hx (ox := ox) (H := Hr n Φ) (by
      rw [show LP.real ox (Hr n Φ) (T.A.x0, T.A.y1) =
        ((ox : ℝ) + T.A.x0, T.A.y1.ev (Hr n Φ)) from rfl]
      exact hd)
    linarith

/-- **Lower spot bound** from a cutter segment whose tip is its lower end. -/
theorem seg_lo {gs : List GZ} {ox : ℚ} (hgs : ∀ g ∈ gs, g.InPoly n Φ ox)
    (hb : boxesSepB (gs.map GZ.box) = true) (hout : boxesOutB gs = true) {T : TCert}
    (ok : (T.cert gs).ok = true) (l : T.cones.length = (groupLR gs).length) {xz : ℚ} {B : AH}
    (hA : T.A.x0 = T.A.x1) (hne : AH.le (T.A.y0.1 + 1 / 8, T.A.y0.2) T.A.y1 = true)
    (hU : rectUnseenSubB (T.cert gs) T.A.loPart ⟨xz, xz, (0, -5), (-1 / 4, 0)⟩ = true)
    {K : List HP} (hC : T.C = some K)
    (htip : K.any (fun h => tipLoB h (T.A.x0, T.A.y0) xz B) = true) (hB : AH.le B (-1 / 4, 2) = true)
    {p : Point} (hp : p ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (hx : p.1 = (ox : ℝ) + xz)
    (hs : ∀ y : ℝ, T.A.y0.ev (Hr n Φ) < y → y < T.A.y1.ev (Hr n Φ) →
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p ((ox : ℝ) + T.A.x0, y)) :
    B.ev (Hr n Φ) ≤ p.2 := by
  obtain ⟨h, hh, htip⟩ := List.any_eq_true.1 htip
  have hH := Hr_ge n Φ
  have hHc : Hr n Φ = (paramH n Φ : ℝ) := Rat.cast_natCast _
  have hY := strip_bound n Φ p hp
  simp only [yMin, yMax, AH.ev] at hY
  push_cast at hY
  have hlt : T.A.y0.ev (Hr n Φ) + 1 / 8 ≤ T.A.y1.ev (Hr n Φ) := by
    have := AH.le_sound hne hH; simp only [AH.ev] at this ⊢; push_cast at this ⊢; linarith
  have hB' : B.ev (Hr n Φ) ≤ 2 * Hr n Φ - 1 / 4 := by
    have := AH.le_sound hB hH; simp only [AH.ev] at this ⊢; push_cast at this ⊢; linarith
  have hAx : ∀ y, T.A.y0.ev (Hr n Φ) ≤ y → y ≤ T.A.y1.ev (Hr n Φ) →
      (((ox : ℝ) + T.A.x0, y) : Point) ∈ (T.A.real ox (Hr n Φ)).set := by
    intro y h0 h1
    refine ⟨le_rfl, ?_, h0, h1⟩
    simp only [LR.real, hA]; exact le_rfl
  by_contra hgt
  push Not at hgt
  by_cases hlo : p.2 ≤ -1 / 4
  · have hm : (((ox : ℝ) + T.A.x0, T.A.y0.ev (Hr n Φ) + 1 / 16) : Point) ∈
        (T.A.loPart.real ox (Hr n Φ)).set := by
      refine ⟨le_rfl, ?_, ?_, ?_⟩
      · simp only [LR.real, LR.loPart, hA]; exact le_rfl
      · simp only [LR.real, LR.loPart]; linarith
      · simp only [LR.real, LR.loPart, AH.ev]; push_cast; linarith
    refine rectUnseenSub_sound hgs hb ok l hU hm (z := p) ?_
      (sees_symm (hs _ (by linarith) (by linarith)))
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [LR.real, AH.ev] <;> push_cast <;> linarith
  · push Not at hlo
    have hcone : p ∈ cone ox (Hr n Φ) ((ox : ℝ) + T.A.x0, T.A.y0.ev (Hr n Φ)) K := by
      refine cone_tip (s := 1) (ε := T.A.y1.ev (Hr n Φ) - T.A.y0.ev (Hr n Φ)) (by linarith)
        fun t h1 h2 => ?_
      have hw := hAx (T.A.y0.ev (Hr n Φ) + 1 * t) (by linarith) (by linarith)
      rcases TCert.sees hgs ok l hb hw (sees_symm (hs _ (by linarith) (by linarith))) with
        ⟨q, hq, -, -, hpU⟩ | ⟨hpC, -⟩
      · have hk' : q.2.1 < (gs.map GZ.box).length := LCert.box_lt ok hq
        rw [List.getD_eq_getElem _ _ hk'] at hpU
        rcases box_y_of_out hout hH (List.getElem_mem hk') hpU with h | h <;> linarith
      · rw [hC] at hpC; exact hpC
    have hd := hcone h hh
    have := tipLoB_sound htip hH hx (ox := ox) (H := Hr n Φ) (by
      rw [show LP.real ox (Hr n Φ) (T.A.x0, T.A.y0) =
        ((ox : ℝ) + T.A.x0, T.A.y0.ev (Hr n Φ)) from rfl]
      exact hd)
    linarith

/-! ### Segment spots of a group -/

/-- The exterior box of an exempt pin spans the height of its target. -/
def exHeightB (D : GData) (k : ℕ) : Bool :=
  match D.Ex.find? (fun e => e.1 == k) with
  | none => true
  | some e => decide (e.2.1.y0 = (D.Ps.getD k PinT.dflt).T.A.y0 ∧
      e.2.1.y1 = (D.Ps.getD k PinT.dflt).T.A.y1)

/-- The pin `k` (a vertical segment with its tip at the lower end) bounds the guards of the line
`x = x_z` from below by `B`. -/
def segLoB (D : GData) (k : ℕ) (xz : ℚ) (B : AH) : Bool :=
  let T := (D.Ps.getD k PinT.dflt).T
  decide (T.A.x0 = T.A.x1) && AH.le (T.A.y0.1 + 1 / 8, T.A.y0.2) T.A.y1 &&
    rectUnseenSubB (T.cert D.gs) T.A.loPart ⟨xz, xz, (0, -5), (-1 / 4, 0)⟩ && AH.le B (-1 / 4, 2) &&
    (match T.C with
      | none => false
      | some K => K.any fun h => tipLoB h (T.A.x0, T.A.y0) xz B) && exHeightB D k

/-- The pin `k` (a vertical segment with its tip at the upper end) bounds the guards of the line
`x = x_z` from above by `B`. -/
def segHiB (D : GData) (k : ℕ) (xz : ℚ) (B : AH) : Bool :=
  let T := (D.Ps.getD k PinT.dflt).T
  decide (T.A.x0 = T.A.x1) && AH.le (T.A.y0.1 + 1 / 8, T.A.y0.2) T.A.y1 &&
    rectUnseenSubB (T.cert D.gs) T.A.hiPart ⟨xz, xz, (-1 / 4, 2), (0, 3)⟩ && AH.le (-1 / 4, 0) B &&
    (match T.C with
      | none => false
      | some K => K.any fun h => tipHiB h (T.A.x0, T.A.y1) xz B) && exHeightB D k

/-- **The segment spot data of witness `i`**: its counting witness and the point pin `kn` are
convex corners whose quadrants meet in the line `x = x_z`; the pins `a` and `b` bound the
ordinates by `B₀` and `B₁`. -/
def spotSegB (D : GData) (i : ℕ) (xz : ℚ) (tw tn : ℕ × ℕ × ℕ) (kn a b : ℕ) (B0 B1 : AH) : Bool :=
  decide (i < D.Ws.length) && decide (kn < D.Ps.length) && decide (a < D.Ps.length) &&
  decide (b < D.Ps.length) && decide ((D.Ps.getD kn PinT.dflt).owner = i) &&
  decide ((D.Ps.getD a PinT.dflt).owner = i) && decide ((D.Ps.getD b PinT.dflt).owner = i) &&
  decide (tw.1 < D.gs.length) && decide (tn.1 < D.gs.length) &&
  decide ((D.Ws.getD i WCert.dflt).a = tipLP D.gs tw) &&
  decide ((D.Ps.getD kn PinT.dflt).T.A = (tipLP D.gs tn).rect) &&
  (D.Ex.find? (fun e => e.1 == kn)).isNone &&
  tquadB (D.gs.getD tw.1 GZ.dflt) (xz, (0, 0)) tw.2.1 tw.2.2 &&
  tquadB (D.gs.getD tn.1 GZ.dflt) (xz, (0, 0)) tn.2.1 tn.2.2 &&
  decide ((tw.2.2 = 0 ∧ tn.2.2 = 1) ∨ (tw.2.2 = 1 ∧ tn.2.2 = 0)) &&
  boxesOutB D.gs && segLoB D a xz B0 && segHiB D b xz B1

theorem LP.rect_mem (ox H : ℝ) (a : LP) : a.real ox H ∈ (a.rect.real ox H).set :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- The points of the open target of a pin with `exHeightB` are in its pin set. -/
theorem GData.pinSet_of_open {D : GData} {k : ℕ} (he : exHeightB D k = true)
    (hA : (D.Ps.getD k PinT.dflt).T.A.x0 = (D.Ps.getD k PinT.dflt).T.A.x1) {ox H y : ℝ}
    (h0 : (D.Ps.getD k PinT.dflt).T.A.y0.ev H < y) (h1 : y < (D.Ps.getD k PinT.dflt).T.A.y1.ev H) :
    (ox + (D.Ps.getD k PinT.dflt).T.A.x0, y) ∈ D.pinSet ox H k := by
  have hm : ((ox + (D.Ps.getD k PinT.dflt).T.A.x0, y) : Point) ∈
      ((D.Ps.getD k PinT.dflt).T.A.real ox H).set := by
    refine ⟨le_rfl, ?_, h0.le, h1.le⟩
    simp only [LR.real, hA]; exact le_rfl
  unfold GData.pinSet
  unfold exHeightB at he
  split
  · exact hm
  · rename_i e hfind
    rw [hfind] at he
    simp only [decide_eq_true_eq] at he
    refine ⟨hm, ?_, ?_⟩
    · rw [he.1]; exact h0
    · rw [he.2]; exact h1

/-- **Segment spots.** A point seeing every pin target of witness `i` lies on the segment
`{ox + x_z} × [B₀, B₁]`. -/
theorem GData.seg_spot {D : GData} (hD : D.Valid) {ox : ℚ} (hgs : ∀ g ∈ D.gs, g.InPoly n Φ ox)
    {i : ℕ} {xz : ℚ} {tw tn : ℕ × ℕ × ℕ} {kn a b : ℕ} {B0 B1 : AH}
    (hchk : spotSegB D i xz tw tn kn a b B0 B1 = true) {p : Point}
    (hp : p ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (hall : ∀ w ∈ D.W ox (Hr n Φ) i, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p w) :
    p.1 = (ox : ℝ) + xz ∧ B0.ev (Hr n Φ) ≤ p.2 ∧ p.2 ≤ B1.ev (Hr n Φ) := by
  simp only [spotSegB, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hi, hkn⟩, ha⟩, hb⟩, hokn⟩, hoa⟩, hob⟩, htw⟩, htn⟩, hWa⟩, hPk⟩, hnone⟩,
    hqw⟩, hqn⟩, hdir⟩, hout⟩, hlo⟩, hhi⟩ := hchk
  have hH := Hr_ge n Φ
  have hparts := (groupOK_parts hD.group).1
  have hmem : ∀ k (hk : k < D.Ps.length), D.Ps.getD k PinT.dflt ∈ D.Ps := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  have hgm : ∀ z (hz : z < D.gs.length), D.gs.getD z GZ.dflt ∈ D.gs := fun z hz => by
    rw [List.getD_eq_getElem _ _ hz]; exact List.getElem_mem hz
  -- the two corners
  have hsw : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p
      ((D.gs.getD tw.1 GZ.dflt).vtx ox (Hr n Φ) tw.2.1) := by
    have : (D.gs.getD tw.1 GZ.dflt).vtx ox (Hr n Φ) tw.2.1 =
        (D.Ws.getD i WCert.dflt).a.real ox (Hr n Φ) := by
      rw [hWa]; rfl
    rw [this]; exact hall _ (Or.inl rfl)
  have hsn : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p
      ((D.gs.getD tn.1 GZ.dflt).vtx ox (Hr n Φ) tn.2.1) := by
    refine hall _ (Or.inr ⟨kn, hkn, hokn, ?_⟩)
    unfold GData.pinSet
    rw [hnone, hPk]
    exact LP.rect_mem _ _ _
  have q1 := GZ.sees_quad (hgs _ (hgm _ htw)) hqw hsw
  have q2 := GZ.sees_quad (hgs _ (hgm _ htn)) hqn hsn
  have hx : p.1 = (ox : ℝ) + xz := by
    rcases hdir with ⟨d1, d2⟩ | ⟨d1, d2⟩
    · rw [d1] at q1; rw [d2] at q2
      simp only [quadSet, LP.real, mem_ofPred_eq] at q1 q2
      exact le_antisymm q1 q2
    · rw [d1] at q1; rw [d2] at q2
      simp only [quadSet, LP.real, mem_ofPred_eq] at q1 q2
      exact le_antisymm q2 q1
  refine ⟨hx, ?_, ?_⟩
  · simp only [segLoB, Bool.and_eq_true, decide_eq_true_eq] at hlo
    obtain ⟨⟨⟨⟨⟨hA, hne⟩, hU⟩, hB⟩, hK⟩, hex⟩ := hlo
    obtain ⟨ok, l, -, -⟩ := pinB_parts (hD.pins _ (hmem a ha))
    split at hK
    · cases hK
    rename_i K hC
    exact seg_lo hgs hparts hout ok l hA hne hU hC hK hB hp hx fun y h0 h1 =>
      hall _ (Or.inr ⟨a, ha, hoa, GData.pinSet_of_open hex hA h0 h1⟩)
  · simp only [segHiB, Bool.and_eq_true, decide_eq_true_eq] at hhi
    obtain ⟨⟨⟨⟨⟨hA, hne⟩, hU⟩, hB⟩, hK⟩, hex⟩ := hhi
    obtain ⟨ok, l, -, -⟩ := pinB_parts (hD.pins _ (hmem b hb))
    split at hK
    · cases hK
    rename_i K hC
    exact seg_hi hgs hparts hout ok l hA hne hU hC hK hB hp hx fun y h0 h1 =>
      hall _ (Or.inr ⟨b, hb, hob, GData.pinSet_of_open hex hA h0 h1⟩)

end

end ArtGallery.Orthogonal.Hard
