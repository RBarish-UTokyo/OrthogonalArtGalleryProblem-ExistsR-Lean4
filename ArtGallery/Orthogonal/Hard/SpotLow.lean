module

public import ArtGallery.Orthogonal.Hard.PinAssm

/-!
# What a helper sees in the low strip

A spot certificate (target: the spot of a helper) bounds the points seen from the spot: they lie
in the zone boxes of the group or in the escaping cone `C`.  If `C` lies in the slab
`xl < x < xr` on the *low strip* `−400 ≤ y ≤ 0` (`lowSlabB`), every point of the low strip seen
from the spot has its abscissa in `(ox + min x₀ xl, ox + max x₁ xr)`, where `[x₀, x₁]` is the
extent of the group (`spot_low_x`).  The nook segments of the gadgets lie in the low strip.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-- The low strip `−400 ≤ y ≤ 0`. -/
def lowLo : AH := (-400, 0)

/-- The top `y = 0` of the low strip. -/
def lowHi : AH := (0, 0)

/-- The coefficient of `z.2` in `det(u, v, z)` with the target at `a`. -/
def hpCoefY (a : LP) (h : HP) : ℚ := (h.2.getD a).1 - (h.1.getD a).1

/-- Two half-planes of the cone through the target point `a` (with `H`-free coefficients) whose
intersection lies in `x ≥ a.x`: their `y`-coefficients have opposite signs and a positive
combination cancels them, leaving a positive multiple of `z.1 − a.x`. -/
def wedgeRightB (a : LP) (K : List HP) : Bool :=
  K.any fun h1 => K.any fun h2 =>
    (h1.1.isNone || h1.2.isNone) && (h2.1.isNone || h2.2.isNone) &&
      decide ((hpCoefX a h1).2 = 0 ∧ (hpCoefX a h2).2 = 0 ∧ 0 ≤ hpCoefY a h1 ∧ hpCoefY a h2 ≤ 0 ∧
        0 < hpCoefY a h1 * (hpCoefX a h2).1 - hpCoefY a h2 * (hpCoefX a h1).1)

/-- The escaping cone of a target certificate lies in `xl < x < xr` on the low strip.  On the
left either one half-plane bounds the cone in the strip (`rightOfBA`), or the target is a point
left of which the cone has no point (`wedgeRightB`). -/
def lowSlabB (T : TCert) (xl xr : ℚ) : Bool :=
  match T.C with
  | none => true
  | some K =>
    (rightOfBA T.A K xl lowLo lowHi ||
      decide (T.A.x0 = T.A.x1 ∧ T.A.y0 = T.A.y1 ∧ xl < T.A.x0) && wedgeRightB (T.A.x0, T.A.y0) K) &&
      leftOfBA T.A K xr lowLo lowHi

/-- A half-plane through the target point, as a linear form in `z − w`. -/
theorem det_hp_lin (ox H : ℝ) (a : LP) {h : HP} (hn : (h.1.isNone || h.2.isNone) = true)
    (z : Point) :
    det (h.1.pt ox H (a.real ox H)) (h.2.pt ox H (a.real ox H)) z =
      (hpCoefX a h).ev H * (z.1 - (a.real ox H).1) + (hpCoefY a h : ℝ) * (z.2 - (a.real ox H).2) := by
  rcases h with ⟨e1, e2⟩
  cases e1 <;> cases e2 <;>
    simp_all [HE.pt, det_def, hpCoefX, hpCoefY, LP.real, AH.ev] <;> ring

theorem wedgeRightB_sound {a : LP} {K : List HP} (h : wedgeRightB a K = true) (ox H : ℝ) {z : Point}
    (hz : z ∈ cone ox H (a.real ox H) K) : (a.real ox H).1 ≤ z.1 := by
  simp only [wedgeRightB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, hh1, h2, hh2, ⟨n1, n2⟩, c1, c2, y1, y2, D⟩ := h
  have f1 : 0 ≤ det _ _ z := hz h1 hh1
  have f2 : 0 ≤ det _ _ z := hz h2 hh2
  rw [det_hp_lin ox H a n1] at f1
  rw [det_hp_lin ox H a n2] at f2
  have e1 : (hpCoefX a h1).ev H = (hpCoefX a h1).1 := by simp [AH.ev, c1]
  have e2 : (hpCoefX a h2).ev H = (hpCoefX a h2).1 := by simp [AH.ev, c2]
  rw [e1] at f1; rw [e2] at f2
  have y1' : (0 : ℝ) ≤ hpCoefY a h1 := by exact_mod_cast y1
  have y2' : (hpCoefY a h2 : ℝ) ≤ 0 := by exact_mod_cast y2
  have D' : (0 : ℝ) < hpCoefY a h1 * (hpCoefX a h2).1 - hpCoefY a h2 * (hpCoefX a h1).1 := by
    exact_mod_cast D
  set d := z.1 - (a.real ox H).1
  have key : 0 ≤ (hpCoefY a h1 * (hpCoefX a h2).1 - hpCoefY a h2 * (hpCoefX a h1).1 : ℝ) * d := by
    nlinarith [mul_nonneg y1' f2, mul_nonneg (neg_nonneg.2 y2') f1]
  have hd : 0 ≤ d := (mul_nonneg_iff_of_pos_left D').1 key
  linarith

variable {n : ℕ} {Φ : List Constraint}

/-- **What a helper sees in the low strip.** -/
theorem spot_low_x {D : GData} (hD : D.Valid) {ox : ℚ} (hgs : ∀ g ∈ D.gs, g.InPoly n Φ ox)
    {T : TCert} (ok : (T.cert D.gs).ok = true) (l : T.cones.length = (groupLR D.gs).length)
    {xl xr : ℚ} (hlow : lowSlabB T xl xr = true) {p : Point}
    (hp : p ∈ (T.A.real ox (Hr n Φ)).set) {s : Point}
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p s) (h1 : -400 ≤ s.2) (h2 : s.2 ≤ 0) :
    (ox : ℝ) + min D.x0 xl < s.1 ∧ s.1 < (ox : ℝ) + max D.x1 xr := by
  have hH := Hr_ge n Φ
  have hb := (groupOK_parts hD.group).1
  have he := hD.ext
  simp only [groupExtB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Option.isNone_iff_eq_none, decide_eq_true_eq] at he
  have m0 : ((min D.x0 xl : ℚ) : ℝ) ≤ D.x0 := by exact_mod_cast min_le_left _ _
  have m1 : ((min D.x0 xl : ℚ) : ℝ) ≤ xl := by exact_mod_cast min_le_right _ _
  have M0 : (D.x1 : ℝ) ≤ ((max D.x1 xr : ℚ) : ℝ) := by exact_mod_cast le_max_left _ _
  have M1 : (xr : ℝ) ≤ ((max D.x1 xr : ℚ) : ℝ) := by exact_mod_cast le_max_right _ _
  push_cast at m0 m1 M0 M1 ⊢
  rcases TCert.sees hgs ok l hb hp hs with ⟨q, hq, -, -, hpU⟩ | ⟨hC, -⟩
  · have hk' : q.2.1 < (D.gs.map GZ.box).length := LCert.box_lt ok hq
    have hpU' : s ∈ ((D.gs.map GZ.box).getD q.2.1 LBox.default).set ox (Hr n Φ) := hpU
    rw [List.getD_eq_getElem _ _ hk', List.getElem_map] at hpU'
    have hk'' : q.2.1 < D.gs.length := by simpa using hk'
    have hbx := he.1 _ (List.getElem_mem hk'')
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
  · cases hTC : T.C with
    | none => rw [hTC] at hC; exact absurd hC (by simp [optCone])
    | some K =>
      rw [hTC] at hC
      simp only [lowSlabB, hTC, Bool.and_eq_true] at hlow
      have e1 : lowLo.ev (Hr n Φ) = -400 := by simp [lowLo, AH.ev]
      have e2 : lowHi.ev (Hr n Φ) = 0 := by simp [lowHi, AH.ev]
      have a2 := leftOfBA_sound hlow.2 hH ox hp hC (by rw [e1]; exact h1) (by rw [e2]; exact h2)
      have a1 : ox + xl < s.1 := by
        rcases Bool.or_eq_true_iff.1 hlow.1 with hr | hw
        · exact rightOfBA_sound hr hH ox hp hC (by rw [e1]; exact h1) (by rw [e2]; exact h2)
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
          obtain ⟨⟨hx, hy, hxl⟩, hwr⟩ := hw
          have hpe : p = LP.real ox (Hr n Φ) (T.A.x0, T.A.y0) := by
            obtain ⟨p1, p2⟩ := p
            obtain ⟨g1, g2, g3, g4⟩ := hp
            simp only [LR.real, LP.real] at g1 g2 g3 g4 ⊢
            rw [← hx] at g2; rw [← hy] at g4
            exact Prod.ext (le_antisymm g2 g1) (le_antisymm g4 g3)
          rw [hpe] at hC
          have := wedgeRightB_sound hwr ox (Hr n Φ) hC
          have hxl' : (xl : ℝ) < T.A.x0 := by exact_mod_cast hxl
          simp only [LP.real] at this
          linarith
      constructor <;> linarith

end

end ArtGallery.Orthogonal.Hard
