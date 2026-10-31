module

public import ArtGallery.Orthogonal.Hard.Cert
public import ArtGallery.Orthogonal.Hard.GZone

/-!
# Grid certificates

The certificates of `Cert.lean` for a *grid frame*: the points of the frame are the points
`(φ i, ψ j)` of a grid whose coordinate maps `φ, ψ` are strictly increasing on the index ranges
`[0, NX)`, `[0, NY)`, but otherwise arbitrary.  Rectangles, intersections, faces and open boxes
are given by grid indices, so their comparisons are comparisons of indices; the only numerical
tests are signs of determinants of three grid points, delegated to a *sign oracle* (`GOr`) whose
soundness is a hypothesis.  For the copy nooks the coordinates are polynomials in the parameters
of the nook and the oracle is the polynomial sign test of `MPoly.lean` (`NookCert.lean`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry Set

/-! ### Grid points, half-planes, oracles -/

/-- An endpoint of the line of a half-plane: a grid point, or (`none`) the target point. -/
abbrev GHE := Option (ℕ × ℕ)

/-- A half-plane `{z | 0 ≤ det(u, v, z)}` through grid points and/or the target. -/
abbrev GHP := GHE × GHE

/-- A sign oracle: `nn u v z` claims `0 ≤ det(u, v, z)`, `pos u v z` claims `0 < det(u, v, z)`
(grid points). -/
structure GOr where
  nn : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → Bool
  pos : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → Bool

section Defs

variable (φ ψ : ℕ → ℝ)

/-- Soundness of an oracle for the grid `φ, ψ`. -/
def GOr.Sound (O : GOr) : Prop :=
  (∀ u v z, O.nn u v z = true → 0 ≤ det (gpt φ ψ u) (gpt φ ψ v) (gpt φ ψ z)) ∧
    ∀ u v z, O.pos u v z = true → 0 < det (gpt φ ψ u) (gpt φ ψ v) (gpt φ ψ z)

/-- The real endpoint for the target `w`. -/
def GHE.pt (w : Point) : GHE → Point
  | none => w
  | some p => gpt φ ψ p

/-- The real half-plane for the target `w`. -/
def GHP.set (w : Point) (h : GHP) : Set Point :=
  {z | 0 ≤ det (h.1.pt φ ψ w) (h.2.pt φ ψ w) z}

/-- A cone: an intersection of half-planes. -/
def gcone (w : Point) (K : List GHP) : Set Point := {z | ∀ h ∈ K, z ∈ h.set φ ψ w}

/-- A finite union of cones. -/
def gcones (w : Point) (Ks : List (List GHP)) : Set Point := {z | ∃ K ∈ Ks, z ∈ gcone φ ψ w K}

/-- An optional cone (`none`: empty). -/
def goptCone (w : Point) : Option (List GHP) → Set Point
  | none => ∅
  | some K => gcone φ ψ w K

end Defs

/-! ### Grid rectangles -/

/-- The four corners of a grid rectangle `(i₀, i₁, j₀, j₁)`. -/
def GRect.corners (r : GRect) : List (ℕ × ℕ) :=
  [(r.1, r.2.2.1), (r.2.1, r.2.2.1), (r.1, r.2.2.2), (r.2.1, r.2.2.2)]

/-- A grid rectangle is well formed in the grid `NX × NY`. -/
def GRect.wf (NX NY : ℕ) (r : GRect) : Bool :=
  decide (r.1 ≤ r.2.1 ∧ r.2.1 < NX ∧ r.2.2.1 ≤ r.2.2.2 ∧ r.2.2.2 < NY)

/-- The intersection of two grid rectangles (`none`: empty). -/
def GRect.inter (r r' : GRect) : Option GRect :=
  if min r.2.1 r'.2.1 < max r.1 r'.1 ∨ min r.2.2.2 r'.2.2.2 < max r.2.2.1 r'.2.2.1 then none
  else some (max r.1 r'.1, min r.2.1 r'.2.1, max r.2.2.1 r'.2.2.1, min r.2.2.2 r'.2.2.2)

/-- An open box of the grid; `none`: that side is at infinity. -/
structure GBox where
  x0 : Option ℕ
  x1 : Option ℕ
  y0 : Option ℕ
  y1 : Option ℕ

/-- The default box. -/
def GBox.default : GBox := ⟨none, none, none, none⟩

/-- The sides of a box are grid indices. -/
def GBox.wf (NX NY : ℕ) (U : GBox) : Bool :=
  (U.x0.all (· < NX)) && (U.x1.all (· < NX)) && (U.y0.all (· < NY)) && (U.y1.all (· < NY))

section Frame

variable {φ ψ : ℕ → ℝ} {NX NY : ℕ}

/-- The real open box. -/
def GBox.set (φ ψ : ℕ → ℝ) (U : GBox) : Set Point :=
  {z | (∀ a, U.x0 = some a → φ a < z.1) ∧ (∀ a, U.x1 = some a → z.1 < φ a) ∧
    (∀ a, U.y0 = some a → ψ a < z.2) ∧ (∀ a, U.y1 = some a → z.2 < ψ a)}

/-- Inside the open box (grid point). -/
def GBox.memB (U : GBox) (w : ℕ × ℕ) : Bool :=
  (U.x0.all (· < w.1)) && (U.x1.all (w.1 < ·)) && (U.y0.all (· < w.2)) && (U.y1.all (w.2 < ·))

/-- The sides of `r` on the boundary of `U`, if `r` lies in the closed box with every side strictly
inside or on the boundary; `none` otherwise. -/
def GRect.faces (U : GBox) (r : GRect) : Option (List GRect) :=
  let l : Option (List GRect) := match U.x0 with
    | none => some []
    | some a => if a < r.1 then some [] else if a = r.1 then some [(r.1, r.1, r.2.2.1, r.2.2.2)]
      else none
  let rt : Option (List GRect) := match U.x1 with
    | none => some []
    | some a => if r.2.1 < a then some [] else if r.2.1 = a then some [(r.2.1, r.2.1, r.2.2.1, r.2.2.2)]
      else none
  let b : Option (List GRect) := match U.y0 with
    | none => some []
    | some a => if a < r.2.2.1 then some [] else if a = r.2.2.1 then some [(r.1, r.2.1, r.2.2.1, r.2.2.1)]
      else none
  let t : Option (List GRect) := match U.y1 with
    | none => some []
    | some a => if r.2.2.2 < a then some [] else if r.2.2.2 = a then some [(r.1, r.2.1, r.2.2.2, r.2.2.2)]
      else none
  match l, rt, b, t with
  | some l, some rt, some b, some t => some (l ++ rt ++ b ++ t)
  | _, _, _, _ => none

variable (hφ : StrictMonoOn φ (Iio NX)) (hψ : StrictMonoOn ψ (Iio NY))
include hφ hψ

omit hφ hψ in
theorem GRect.wf_bounds {r : GRect} (h : r.wf NX NY = true) :
    r.1 < NX ∧ r.2.1 < NX ∧ r.2.2.1 < NY ∧ r.2.2.2 < NY ∧ r.1 ≤ r.2.1 ∧ r.2.2.1 ≤ r.2.2.2 := by
  simp only [GRect.wf, decide_eq_true_eq] at h
  omega

theorem GRect.inter_empty {r r' : GRect} (hr : r.wf NX NY = true) (hr' : r'.wf NX NY = true)
    (h : r.inter r' = none) {z : Point} (hz : z ∈ (realR φ ψ r).set)
    (hz' : z ∈ (realR φ ψ r').set) : False := by
  have b := GRect.wf_bounds hr
  have b' := GRect.wf_bounds hr'
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  obtain ⟨hx0', hx1', hy0', hy1'⟩ := hz'
  simp only [realR] at hx0 hx1 hy0 hy1 hx0' hx1' hy0' hy1'
  unfold GRect.inter at h
  split_ifs at h with hc
  rcases hc with hc | hc
  · -- `min i₁ < max i₀`
    rcases le_total r.2.1 r'.2.1 with h1 | h1 <;> rcases le_total r.1 r'.1 with h2 | h2
    · rw [min_eq_left h1, max_eq_right h2] at hc
      have := hφ (by simp only [mem_Iio]; omega) (by simp only [mem_Iio]; omega) hc; linarith
    · rw [min_eq_left h1, max_eq_left h2] at hc; omega
    · rw [min_eq_right h1, max_eq_right h2] at hc; omega
    · rw [min_eq_right h1, max_eq_left h2] at hc
      have := hφ (by simp only [mem_Iio]; omega) (by simp only [mem_Iio]; omega) hc; linarith
  · rcases le_total r.2.2.2 r'.2.2.2 with h1 | h1 <;> rcases le_total r.2.2.1 r'.2.2.1 with h2 | h2
    · rw [min_eq_left h1, max_eq_right h2] at hc
      have := hψ (by simp only [mem_Iio]; omega) (by simp only [mem_Iio]; omega) hc; linarith
    · rw [min_eq_left h1, max_eq_left h2] at hc; omega
    · rw [min_eq_right h1, max_eq_right h2] at hc; omega
    · rw [min_eq_right h1, max_eq_left h2] at hc
      have := hψ (by simp only [mem_Iio]; omega) (by simp only [mem_Iio]; omega) hc; linarith

omit hφ hψ in
theorem GRect.inter_sub {r r' X : GRect} (h : r.inter r' = some X) {z : Point}
    (hz : z ∈ (realR φ ψ r).set) (hz' : z ∈ (realR φ ψ r').set) : z ∈ (realR φ ψ X).set := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  obtain ⟨hx0', hx1', hy0', hy1'⟩ := hz'
  simp only [realR] at hx0 hx1 hy0 hy1 hx0' hx1' hy0' hy1'
  unfold GRect.inter at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  simp only [Rect.set, realR, mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases le_total r.1 r'.1 with h | h
    · rw [max_eq_right h]; exact hx0'
    · rw [max_eq_left h]; exact hx0
  · rcases le_total r.2.1 r'.2.1 with h | h
    · rw [min_eq_left h]; exact hx1
    · rw [min_eq_right h]; exact hx1'
  · rcases le_total r.2.2.1 r'.2.2.1 with h | h
    · rw [max_eq_right h]; exact hy0'
    · rw [max_eq_left h]; exact hy0
  · rcases le_total r.2.2.2 r'.2.2.2 with h | h
    · rw [min_eq_left h]; exact hy1
    · rw [min_eq_right h]; exact hy1'

omit hφ hψ in
theorem GRect.inter_wf {r r' X : GRect} (hr : r.wf NX NY = true) (hr' : r'.wf NX NY = true)
    (h : r.inter r' = some X) : X.wf NX NY = true := by
  unfold GRect.inter at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  simp only [GRect.wf, decide_eq_true_eq] at hr hr' ⊢
  push Not at hc
  omega

end Frame

/-! ### Robust tests on grid rectangles -/

/-- `0 ≤ det` for every corner target of `A` at every point of a list. -/
def ghNN (O : GOr) (A : GRect) (h : GHP) (cs : List (ℕ × ℕ)) : Bool :=
  A.corners.all fun a => cs.all fun c => O.nn (h.1.getD a) (h.2.getD a) c

/-- `det < 0` for every corner target of `A` at every point of a list. -/
def ghNeg (O : GOr) (A : GRect) (h : GHP) (cs : List (ℕ × ℕ)) : Bool :=
  A.corners.all fun a => cs.all fun c => O.pos (h.2.getD a) (h.1.getD a) c

/-- The star condition of a half-plane: automatic through the target; otherwise
`det(u, v, a) ≤ 0` at the corner targets. -/
def gstarB (O : GOr) (A : GRect) (h : GHP) : Bool :=
  match h with
  | (some u, some v) => A.corners.all fun a => O.nn v u a
  | _ => true

section Sound

variable {φ ψ : ℕ → ℝ} {O : GOr} (hO : O.Sound φ ψ)
include hO

omit hO in
theorem det_swap (u v z : Point) : det v u z = -det u v z := by simp only [det]; ring

omit hO in
theorem GHE.pt_gpt (w : ℕ × ℕ) (e : GHE) : e.pt φ ψ (gpt φ ψ w) = gpt φ ψ (e.getD w) := by
  cases e <;> rfl

omit hO in
/-- `det(E₁(w), E₂(w), z)` is affine in the target `w`. -/
theorem det_ghe_affine (h : GHP) (z : Point) : ∃ α β γ : ℝ, ∀ x y : ℝ,
    det (h.1.pt φ ψ (x, y)) (h.2.pt φ ψ (x, y)) z = α * x + β * y + γ := by
  rcases h with ⟨e1, e2⟩
  cases e1 with
  | none =>
    cases e2 with
    | none => exact ⟨0, 0, 0, fun x y => by simp only [GHE.pt, det]; ring⟩
    | some p =>
      exact ⟨(gpt φ ψ p).2 - z.2, z.1 - (gpt φ ψ p).1,
        (gpt φ ψ p).1 * z.2 - z.1 * (gpt φ ψ p).2, fun x y => by simp only [GHE.pt, det]; ring⟩
  | some p =>
    cases e2 with
    | none =>
      exact ⟨z.2 - (gpt φ ψ p).2, -(z.1 - (gpt φ ψ p).1),
        -(gpt φ ψ p).1 * (z.2 - (gpt φ ψ p).2) + (gpt φ ψ p).2 * (z.1 - (gpt φ ψ p).1),
        fun x y => by simp only [GHE.pt, det]; ring⟩
    | some q =>
      exact ⟨0, 0, det (gpt φ ψ p) (gpt φ ψ q) z, fun x y => by simp only [GHE.pt]; ring⟩

omit hO in
theorem gcorners_mem {r : GRect} {P : ℕ × ℕ → Prop} (h : ∀ c ∈ r.corners, P c) :
    P (r.1, r.2.2.1) ∧ P (r.2.1, r.2.2.1) ∧ P (r.1, r.2.2.2) ∧ P (r.2.1, r.2.2.2) := by
  simp only [GRect.corners, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  exact h

omit hO in
/-- A bound at the corners (for every corner target) gives the bound for every target of `A` at
every point of `r`. -/
theorem gh_bound_rect {h : GHP} {A r : GRect} {Q : ℝ → Prop}
    (hQ : ∀ (f : ℝ → ℝ → ℝ) (α β γ x0 x1 y0 y1 x y : ℝ), (∀ x y, f x y = α * x + β * y + γ) →
      Q (f x0 y0) → Q (f x1 y0) → Q (f x0 y1) → Q (f x1 y1) →
      x0 ≤ x → x ≤ x1 → y0 ≤ y → y ≤ y1 → Q (f x y))
    (hc : ∀ a ∈ A.corners, ∀ c ∈ r.corners,
      Q (det (gpt φ ψ (h.1.getD a)) (gpt φ ψ (h.2.getD a)) (gpt φ ψ c)))
    {w : Point} (hw : w ∈ (realR φ ψ A).set) {z : Point} (hz : z ∈ (realR φ ψ r).set) :
    Q (det (h.1.pt φ ψ w) (h.2.pt φ ψ w) z) := by
  have step1 : ∀ c ∈ r.corners, Q (det (h.1.pt φ ψ w) (h.2.pt φ ψ w) (gpt φ ψ c)) := by
    intro c hcm
    obtain ⟨α, β, γ, hf⟩ := det_ghe_affine (φ := φ) (ψ := ψ) h (gpt φ ψ c)
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
    simp only [realR] at hx0 hx1 hy0 hy1
    have hcA := gcorners_mem (P := fun a =>
      Q (det (h.1.pt φ ψ (gpt φ ψ a)) (h.2.pt φ ψ (gpt φ ψ a)) (gpt φ ψ c)))
      (fun a ha => by rw [GHE.pt_gpt, GHE.pt_gpt]; exact hc a ha c hcm)
    obtain ⟨q00, q10, q01, q11⟩ := hcA
    simp only [gpt] at q00 q10 q01 q11
    have := hQ (fun x y => det (h.1.pt φ ψ (x, y)) (h.2.pt φ ψ (x, y)) (gpt φ ψ c)) α β γ
      _ _ _ _ w.1 w.2 hf q00 q10 q01 q11 hx0 hx1 hy0 hy1
    simpa using this
  obtain ⟨q00, q10, q01, q11⟩ := gcorners_mem step1
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  simp only [realR] at hx0 hx1 hy0 hy1
  simp only [gpt] at q00 q10 q01 q11
  have := hQ (fun x y => det (h.1.pt φ ψ w) (h.2.pt φ ψ w) (x, y))
    (-((h.2.pt φ ψ w).2 - (h.1.pt φ ψ w).2)) ((h.2.pt φ ψ w).1 - (h.1.pt φ ψ w).1)
    (((h.2.pt φ ψ w).2 - (h.1.pt φ ψ w).2) * (h.1.pt φ ψ w).1 -
      ((h.2.pt φ ψ w).1 - (h.1.pt φ ψ w).1) * (h.1.pt φ ψ w).2)
    _ _ _ _ z.1 z.2 (fun x y => det_affine _ _ (x, y)) q00 q10 q01 q11 hx0 hx1 hy0 hy1
  simpa using this

theorem ghNN_sound {A r : GRect} {h : GHP} (hh : ghNN O A h r.corners = true)
    {w : Point} (hw : w ∈ (realR φ ψ A).set) {z : Point} (hz : z ∈ (realR φ ψ r).set) :
    z ∈ h.set φ ψ w := by
  refine gh_bound_rect (h := h) (Q := fun v => 0 ≤ v)
    (fun f α β γ x0 x1 y0 y1 x y hf a b c d e g i j => affine_rect (c := 0) f hf a b c d e g i j)
    (fun a ha c hc => ?_) hw hz
  simp only [ghNN, List.all_eq_true] at hh
  exact hO.1 _ _ _ (hh a ha c hc)

theorem ghNeg_sound {A r : GRect} {h : GHP} (hh : ghNeg O A h r.corners = true)
    {w : Point} (hw : w ∈ (realR φ ψ A).set) {z : Point} (hz : z ∈ (realR φ ψ r).set) :
    z ∉ h.set φ ψ w := by
  intro hzh
  have := gh_bound_rect (h := h) (Q := fun v => 0 < -v)
    (fun f α β γ x0 x1 y0 y1 x y hf a b c d e g i j =>
      affine_pos_rect (fun x y => -f x y) (A := -α) (B := -β) (G := -γ)
        (fun x y => by rw [hf]; ring) a b c d e g i j) (fun a ha c hc => ?_) hw hz
  · have h' : 0 ≤ det (h.1.pt φ ψ w) (h.2.pt φ ψ w) z := hzh
    linarith
  · simp only [ghNeg, List.all_eq_true] at hh
    have := hO.2 _ _ _ (hh a ha c hc)
    rw [det_swap] at this
    linarith

theorem gstarB_sound {A : GRect} {h : GHP} (hh : gstarB O A h = true)
    {w : Point} (hw : w ∈ (realR φ ψ A).set) : det (h.1.pt φ ψ w) (h.2.pt φ ψ w) w ≤ 0 := by
  rcases h with ⟨e1, e2⟩
  cases e1 with
  | none => simp only [GHE.pt, det]; nlinarith
  | some u =>
    cases e2 with
    | none => simp only [GHE.pt, det]; nlinarith
    | some v =>
      simp only [gstarB, List.all_eq_true] at hh
      have hc := gcorners_mem (P := fun a => 0 ≤ -det (gpt φ ψ u) (gpt φ ψ v) (gpt φ ψ a))
        (fun a ha => by have := hO.1 _ _ _ (hh a ha); rw [det_swap] at this; exact this)
      obtain ⟨q00, q10, q01, q11⟩ := hc
      obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
      simp only [realR] at hx0 hx1 hy0 hy1
      simp only [gpt] at q00 q10 q01 q11
      have := affine_rect (c := 0) (fun x y => -det (gpt φ ψ u) (gpt φ ψ v) (x, y))
        (A := ((gpt φ ψ v).2 - (gpt φ ψ u).2)) (B := -((gpt φ ψ v).1 - (gpt φ ψ u).1))
        (G := -(((gpt φ ψ v).2 - (gpt φ ψ u).2) * (gpt φ ψ u).1 -
          ((gpt φ ψ v).1 - (gpt φ ψ u).1) * (gpt φ ψ u).2))
        (fun x y => by rw [det_affine]; ring) q00 q10 q01 q11 hx0 hx1 hy0 hy1
      simp only [GHE.pt]
      have e : w = (w.1, w.2) := rfl
      rw [e]; linarith

omit hO in
theorem gstarFrom_hp {h : GHP} {w : Point}
    (hw : det (h.1.pt φ ψ w) (h.2.pt φ ψ w) w ≤ 0) : StarFrom w (h.set φ ψ w) := by
  intro z hz s hs
  show 0 ≤ det _ _ _
  rw [det_lerp_third]
  have hz' : 0 ≤ det (h.1.pt φ ψ w) (h.2.pt φ ψ w) z := hz
  nlinarith

omit hO in
theorem gstarFrom_cone {K : List GHP} {w : Point}
    (hw : ∀ h ∈ K, det (h.1.pt φ ψ w) (h.2.pt φ ψ w) w ≤ 0) : StarFrom w (gcone φ ψ w K) :=
  fun z hz s hs h hh => gstarFrom_hp (hw h hh) z (hz h hh) s hs

omit hO in
theorem gstarFrom_cones {Ks : List (List GHP)} {w : Point}
    (hw : ∀ K ∈ Ks, ∀ h ∈ K, det (h.1.pt φ ψ w) (h.2.pt φ ψ w) w ≤ 0) :
    StarFrom w (gcones φ ψ w Ks) := by
  rintro z ⟨K, hK, hz⟩ s hs
  exact ⟨K, hK, gstarFrom_cone (hw K hK) z hz s hs⟩

omit hO in
theorem gstarFrom_optCone {o : Option (List GHP)} {w : Point}
    (hw : ∀ K, o = some K → ∀ h ∈ K, det (h.1.pt φ ψ w) (h.2.pt φ ψ w) w ≤ 0) :
    StarFrom w (goptCone φ ψ w o) := by
  cases o with
  | none => intro z hz; exact absurd hz (by simp [goptCone])
  | some K => exact gstarFrom_cone (hw K rfl)

end Sound

/-! ### Faces and boxes -/

section Boxes

variable {φ ψ : ℕ → ℝ} {NX NY : ℕ} (hφ : StrictMonoOn φ (Iio NX)) (hψ : StrictMonoOn ψ (Iio NY))
include hφ hψ

theorem GBox.memB_sound {U : GBox} (hU : U.wf NX NY = true) {w : ℕ × ℕ} (hw1 : w.1 < NX)
    (hw2 : w.2 < NY) (h : U.memB w = true) : gpt φ ψ w ∈ U.set φ ψ := by
  simp only [GBox.memB, GBox.wf, Bool.and_eq_true, Option.all_eq_true_iff_get,
    decide_eq_true_eq] at h hU
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨⟨⟨u1, u2⟩, u3⟩, u4⟩ := hU
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have hs : U.x0.isSome := by rw [ha]; rfl
    have h1' := h1 hs; have u1' := u1 hs
    simp only [ha, Option.get_some] at h1' u1'
    exact hφ (by simpa using u1') (by simpa using hw1) h1'
  · have hs : U.x1.isSome := by rw [ha]; rfl
    have h2' := h2 hs; have u2' := u2 hs
    simp only [ha, Option.get_some] at h2' u2'
    exact hφ (by simpa using hw1) (by simpa using u2') h2'
  · have hs : U.y0.isSome := by rw [ha]; rfl
    have h3' := h3 hs; have u3' := u3 hs
    simp only [ha, Option.get_some] at h3' u3'
    exact hψ (by simpa using u3') (by simpa using hw2) h3'
  · have hs : U.y1.isSome := by rw [ha]; rfl
    have h4' := h4 hs; have u4' := u4 hs
    simp only [ha, Option.get_some] at h4' u4'
    exact hψ (by simpa using hw2) (by simpa using u4') h4'

/-- All corners of `A` in the open box: then `A` lies in it. -/
theorem GBox.corners_sound {U : GBox} (hU : U.wf NX NY = true) {A : GRect}
    (hA : A.wf NX NY = true) (h : A.corners.all U.memB = true) {w : Point}
    (hw : w ∈ (realR φ ψ A).set) : w ∈ U.set φ ψ := by
  have b := GRect.wf_bounds hA
  simp only [List.all_eq_true] at h
  have c00 := GBox.memB_sound hφ hψ hU (w := (A.1, A.2.2.1)) b.1 b.2.2.1
    (h _ (by simp [GRect.corners]))
  have c11 := GBox.memB_sound hφ hψ hU (w := (A.2.1, A.2.2.2)) b.2.1 b.2.2.2.1
    (h _ (by simp [GRect.corners]))
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  simp only [realR] at hx0 hx1 hy0 hy1
  simp only [gpt] at c00 c11
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have := c00.1 a ha; simp only at this; linarith
  · have := c11.2.1 a ha; simp only at this; linarith
  · have := c00.2.2.1 a ha; simp only at this; linarith
  · have := c11.2.2.2 a ha; simp only at this; linarith

theorem GRect.faces_sound {U : GBox} (hU : U.wf NX NY = true) {r : GRect}
    (hr : r.wf NX NY = true) {fs : List GRect} (h : r.faces U = some fs) {z : Point}
    (hz : z ∈ (realR φ ψ r).set) (hzU : z ∉ U.set φ ψ) :
    ∃ e ∈ fs, z ∈ (realR φ ψ e).set := by
  have b := GRect.wf_bounds hr
  simp only [GBox.wf, Bool.and_eq_true, Option.all_eq_true_iff_get, decide_eq_true_eq] at hU
  obtain ⟨⟨⟨u1, u2⟩, u3⟩, u4⟩ := hU
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  simp only [realR] at hx0 hx1 hy0 hy1
  unfold GRect.faces at h
  simp only at h
  split at h
  · rename_i l rt bt t hl hrt hb ht
    simp only [Option.some.injEq] at h
    subst h
    simp only [GBox.set, Set.mem_ofPred_eq, not_and_or, not_forall] at hzU
    rcases hzU with ⟨a, ha, hlt⟩ | ⟨a, ha, hlt⟩ | ⟨a, ha, hlt⟩ | ⟨a, ha, hlt⟩
    · have ua : a < NX := by have := u1 (by rw [ha]; rfl); simpa [ha] using this
      rw [ha] at hl
      simp only at hl
      split_ifs at hl with c1 c2
      · exfalso; have := hφ (by simpa using ua) (by simpa using b.1) c1; linarith
      · simp only [Option.some.injEq] at hl; subst hl
        rw [c2] at hlt
        exact ⟨(r.1, r.1, r.2.2.1, r.2.2.2), by simp,
          ⟨by simp only [realR]; linarith, by simp only [realR]; linarith, hy0, hy1⟩⟩
    · have ua : a < NX := by have := u2 (by rw [ha]; rfl); simpa [ha] using this
      rw [ha] at hrt
      simp only at hrt
      split_ifs at hrt with c1 c2
      · exfalso; have := hφ (by simpa using b.2.1) (by simpa using ua) c1; linarith
      · simp only [Option.some.injEq] at hrt; subst hrt
        refine ⟨(r.2.1, r.2.1, r.2.2.1, r.2.2.2), by simp, ?_⟩
        rw [← c2] at hlt
        exact ⟨by simp only [realR]; linarith, by simp only [realR]; linarith, hy0, hy1⟩
    · have ua : a < NY := by have := u3 (by rw [ha]; rfl); simpa [ha] using this
      rw [ha] at hb
      simp only at hb
      split_ifs at hb with c1 c2
      · exfalso; have := hψ (by simpa using ua) (by simpa using b.2.2.1) c1; linarith
      · simp only [Option.some.injEq] at hb; subst hb
        rw [c2] at hlt
        exact ⟨(r.1, r.2.1, r.2.2.1, r.2.2.1), by simp,
          ⟨hx0, hx1, by simp only [realR]; linarith, by simp only [realR]; linarith⟩⟩
    · have ua : a < NY := by have := u4 (by rw [ha]; rfl); simpa [ha] using this
      rw [ha] at ht
      simp only at ht
      split_ifs at ht with c1 c2
      · exfalso; have := hψ (by simpa using b.2.2.2.1) (by simpa using ua) c1; linarith
      · simp only [Option.some.injEq] at ht; subst ht
        refine ⟨(r.1, r.2.1, r.2.2.2, r.2.2.2), by simp, ?_⟩
        rw [← c2] at hlt
        exact ⟨hx0, hx1, by simp only [realR]; linarith, by simp only [realR]; linarith⟩
  · cases h

/-- A rectangle with computed faces lies in the closed box. -/
theorem GRect.faces_closed {U : GBox} (hU : U.wf NX NY = true) {r : GRect}
    (hr : r.wf NX NY = true) {fs : List GRect} (h : r.faces U = some fs) {z : Point}
    (hz : z ∈ (realR φ ψ r).set) :
    (∀ a, U.x0 = some a → φ a ≤ z.1) ∧ (∀ a, U.x1 = some a → z.1 ≤ φ a) ∧
    (∀ a, U.y0 = some a → ψ a ≤ z.2) ∧ (∀ a, U.y1 = some a → z.2 ≤ ψ a) := by
  have b := GRect.wf_bounds hr
  simp only [GBox.wf, Bool.and_eq_true, Option.all_eq_true_iff_get, decide_eq_true_eq] at hU
  obtain ⟨⟨⟨u1, u2⟩, u3⟩, u4⟩ := hU
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  simp only [realR] at hx0 hx1 hy0 hy1
  unfold GRect.faces at h
  simp only at h
  split at h
  · rename_i l rt bt t hl hrt hb ht
    refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
    · have ua : a < NX := by have := u1 (by rw [ha]; rfl); simpa [ha] using this
      rw [ha] at hl; simp only at hl
      split_ifs at hl with c1 c2
      · have := hφ (by simpa using ua) (by simpa using b.1) c1; linarith
      · subst c2; linarith
    · have ua : a < NX := by have := u2 (by rw [ha]; rfl); simpa [ha] using this
      rw [ha] at hrt; simp only at hrt
      split_ifs at hrt with c1 c2
      · have := hφ (by simpa using b.2.1) (by simpa using ua) c1; linarith
      · rw [← c2]; linarith
    · have ua : a < NY := by have := u3 (by rw [ha]; rfl); simpa [ha] using this
      rw [ha] at hb; simp only at hb
      split_ifs at hb with c1 c2
      · have := hψ (by simpa using ua) (by simpa using b.2.2.1) c1; linarith
      · subst c2; linarith
    · have ua : a < NY := by have := u4 (by rw [ha]; rfl); simpa [ha] using this
      rw [ha] at ht; simp only at ht
      split_ifs at ht with c1 c2
      · have := hψ (by simpa using b.2.2.2.1) (by simpa using ua) c1; linarith
      · rw [← c2]; linarith
  · cases h

omit hφ hψ in
theorem GRect.faces_wf {U : GBox} {r : GRect} (hr : r.wf NX NY = true) {fs : List GRect}
    (h : r.faces U = some fs) : ∀ e ∈ fs, e.wf NX NY = true := by
  simp only [GRect.wf, decide_eq_true_eq] at hr
  unfold GRect.faces at h
  simp only at h
  split at h
  · rename_i l rt bt t hl hrt hb ht
    simp only [Option.some.injEq] at h
    subst h
    intro e he
    simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he
    · split at hl
      · cases hl; simp at he
      · split_ifs at hl <;> cases hl
        · simp at he
        · simp only [List.mem_singleton] at he; subst he; simp [GRect.wf]; omega
    · split at hrt
      · cases hrt; simp at he
      · split_ifs at hrt <;> cases hrt
        · simp at he
        · simp only [List.mem_singleton] at he; subst he; simp [GRect.wf]; omega
    · split at hb
      · cases hb; simp at he
      · split_ifs at hb <;> cases hb
        · simp at he
        · simp only [List.mem_singleton] at he; subst he; simp [GRect.wf]; omega
    · split at ht
      · cases ht; simp at he
      · split_ifs at ht <;> cases ht
        · simp at he
        · simp only [List.mem_singleton] at he; subst he; simp [GRect.wf]; omega
  · cases h

/-- Two boxes are separated (their closures are disjoint). -/
def GBox.sepB (U V : GBox) : Bool :=
  (match U.x1, V.x0 with | some a, some b => decide (a ≤ b) | _, _ => false) ||
  (match V.x1, U.x0 with | some a, some b => decide (a ≤ b) | _, _ => false) ||
  (match U.y1, V.y0 with | some a, some b => decide (a ≤ b) | _, _ => false) ||
  (match V.y1, U.y0 with | some a, some b => decide (a ≤ b) | _, _ => false)

theorem GBox.sepB_sound {U V : GBox} (hU : U.wf NX NY = true) (hV : V.wf NX NY = true)
    (h : U.sepB V = true) {z : Point}
    (hz : (∀ a, U.x0 = some a → φ a ≤ z.1) ∧ (∀ a, U.x1 = some a → z.1 ≤ φ a) ∧
      (∀ a, U.y0 = some a → ψ a ≤ z.2) ∧ (∀ a, U.y1 = some a → z.2 ≤ ψ a)) :
    z ∉ V.set φ ψ := by
  rintro ⟨hv0, hv1, hv2, hv3⟩
  obtain ⟨hu0, hu1, hu2, hu3⟩ := hz
  simp only [GBox.wf, Bool.and_eq_true, Option.all_eq_true_iff_get, decide_eq_true_eq] at hU hV
  unfold GBox.sepB at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · split at h
    · rename_i a b ha hb
      have := of_decide_eq_true h
      have h1 := hu1 a ha; have h2 := hv0 b hb
      have ua : a < NX := by have := hU.1.1.2 (by rw [ha]; rfl); simpa [ha] using this
      have ub : b < NX := by have := hV.1.1.1 (by rw [hb]; rfl); simpa [hb] using this
      have := hφ.monotoneOn (by simpa using ua) (by simpa using ub) this
      linarith
    · cases h
  · split at h
    · rename_i a b ha hb
      have := of_decide_eq_true h
      have h1 := hv1 a ha; have h2 := hu0 b hb
      have ua : a < NX := by have := hV.1.1.2 (by rw [ha]; rfl); simpa [ha] using this
      have ub : b < NX := by have := hU.1.1.1 (by rw [hb]; rfl); simpa [hb] using this
      have := hφ.monotoneOn (by simpa using ua) (by simpa using ub) this
      linarith
    · cases h
  · split at h
    · rename_i a b ha hb
      have := of_decide_eq_true h
      have h1 := hu3 a ha; have h2 := hv2 b hb
      have ua : a < NY := by have := hU.2 (by rw [ha]; rfl); simpa [ha] using this
      have ub : b < NY := by have := hV.1.2 (by rw [hb]; rfl); simpa [hb] using this
      have := hψ.monotoneOn (by simpa using ua) (by simpa using ub) this
      linarith
    · cases h
  · split at h
    · rename_i a b ha hb
      have := of_decide_eq_true h
      have h1 := hv3 a ha; have h2 := hu2 b hb
      have ua : a < NY := by have := hV.2 (by rw [ha]; rfl); simpa [ha] using this
      have ub : b < NY := by have := hU.1.2 (by rw [hb]; rfl); simpa [hb] using this
      have := hψ.monotoneOn (by simpa using ua) (by simpa using ub) this
      linarith
    · cases h

end Boxes

/-! ### Certificates -/

/-- A grid certificate: the targets `A` in the open box `U[Ab]`; local rectangles, each with the
index of the open box containing it and a union of cones; the cone `C` of the other rectangles of
the region, which lie outside all boxes. -/
structure GCert where
  A : GRect
  Ab : ℕ
  cs : List (GRect × ℕ × List (List GHP))
  C : Option (List GHP)
  U : List GBox

/-- Base condition: the targets miss the rectangle, or one cone contains it. -/
def gbaseB (O : GOr) (A : GRect) (q : GRect × ℕ × List (List GHP)) : Bool :=
  decide (A.inter q.1 = none) || q.2.2.any fun K => K.all fun h => ghNN O A h q.1.corners

/-- Propagation from `q` to `q'`. -/
def gpropB (O : GOr) (A : GRect) (q q' : GRect × ℕ × List (List GHP)) : Bool :=
  q.2.2.isEmpty ||
  match q.1.inter q'.1 with
  | none => true
  | some X =>
    q.2.2.all fun K => K.any (fun h => ghNeg O A h X.corners) ||
      q'.2.2.any fun K' => K'.all fun h => decide (h ∈ K) || ghNN O A h X.corners

/-- On an exposed face `e`: leaving to the rest and entering from the rest. -/
def gfaceB (O : GOr) (A : GRect) (C : Option (List GHP)) (Ks : List (List GHP)) (e : GRect) :
    Bool :=
  match C with
  | none => Ks.all fun K => K.any fun h => ghNeg O A h e.corners
  | some hsC =>
    (Ks.all fun K => K.any (fun h => ghNeg O A h e.corners) ||
      hsC.all fun h => decide (h ∈ K) || ghNN O A h e.corners) &&
    (hsC.any (fun h => ghNeg O A h e.corners) ||
      Ks.any fun K => K.all fun h => decide (h ∈ hsC) || ghNN O A h e.corners)

/-- **The certificate check.** -/
def GCert.ok (NX NY : ℕ) (O : GOr) (c : GCert) : Bool :=
  c.A.wf NX NY && c.U.all (GBox.wf NX NY) && boxesSepG c.U &&
  (c.cs.flatMap (fun q => q.2.2.flatten) ++ c.C.getD []).all (gstarB O c.A) &&
  c.A.corners.all (c.U.getD c.Ab GBox.default).memB && decide (c.Ab < c.U.length) &&
  c.cs.all (fun q => q.1.wf NX NY && gbaseB O c.A q && decide (q.2.1 < c.U.length) &&
    match q.1.faces (c.U.getD q.2.1 GBox.default) with
    | none => false
    | some fs => fs.all fun e => gfaceB O c.A c.C q.2.2 e) &&
  c.cs.all (fun q => q.2.2.isEmpty || c.cs.all fun q' => gpropB O c.A q q')
where
  /-- The boxes are pairwise separated. -/
  boxesSepG (Us : List GBox) : Bool :=
    (List.range Us.length).all fun i => (List.range Us.length).all fun j =>
      decide (i = j) || (Us.getD i GBox.default).sepB (Us.getD j GBox.default)

section CertSound

variable {φ ψ : ℕ → ℝ} {NX NY : ℕ} (hφ : StrictMonoOn φ (Iio NX)) (hψ : StrictMonoOn ψ (Iio NY))
  {O : GOr} (hO : O.Sound φ ψ)
include hφ hψ hO

/-- **Soundness of the grid certificate check.**  For every target `w ∈ A`: if the segment from
`w` to `p` is covered by the local rectangles and closed sets `Rest` outside all boxes, then `p`
lies in a local rectangle, one of its cones and its box, or outside all boxes and in `C`. -/
theorem GCert.sound {c : GCert} (hok : c.ok NX NY O = true)
    {w : Point} (hw : w ∈ (realR φ ψ c.A).set)
    {Rest : List (Set Point)} (hRc : ∀ r ∈ Rest, IsClosed r)
    (hRU : ∀ r ∈ Rest, ∀ z ∈ r, ∀ U ∈ c.U, z ∉ U.set φ ψ) {p : Point}
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∃ q ∈ c.cs, lerp w p t ∈ (realR φ ψ q.1).set) ∨ ∃ r ∈ Rest, lerp w p t ∈ r) :
    (∃ q ∈ c.cs, p ∈ (realR φ ψ q.1).set ∧ p ∈ gcones φ ψ w q.2.2 ∧
      p ∈ (c.U.getD q.2.1 GBox.default).set φ ψ) ∨
      (p ∈ goptCone φ ψ w c.C ∧ ∀ U ∈ c.U, p ∉ U.set φ ψ) := by
  have hok' := hok
  simp only [GCert.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨⟨⟨⟨hAwf, hUwf⟩, hsep⟩, hstar⟩, hwU⟩, hAb⟩, hloc⟩, hpr⟩ := hok'
  have hUmem : ∀ k < c.U.length, c.U.getD k GBox.default ∈ c.U := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  have hwU' : w ∈ (c.U.getD c.Ab GBox.default).set φ ψ :=
    GBox.corners_sound hφ hψ (hUwf _ (hUmem _ hAb)) hAwf (List.all_eq_true.2 hwU) hw
  have hst : ∀ h ∈ c.cs.flatMap (fun q => q.2.2.flatten) ++ c.C.getD [],
      det (h.1.pt φ ψ w) (h.2.pt φ ψ w) w ≤ 0 := fun h hh => gstarB_sound hO (hstar h hh) hw
  set L := c.cs.map (fun q => ((realR φ ψ q.1).set, gcones φ ψ w q.2.2)) with hL
  have hmemL : ∀ x ∈ L, ∃ q ∈ c.cs, x = ((realR φ ψ q.1).set, gcones φ ψ w q.2.2) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    exact ⟨q, hq, rfl⟩
  have hqwf : ∀ q ∈ c.cs, q.1.wf NX NY = true := fun q hq => (hloc q hq).1.1.1
  -- a local point outside its box lies on an exposed face
  have hface : ∀ q ∈ c.cs, ∀ z ∈ (realR φ ψ q.1).set,
      z ∉ (c.U.getD q.2.1 GBox.default).set φ ψ →
      ∃ fs, q.1.faces (c.U.getD q.2.1 GBox.default) = some fs ∧
        (∀ e ∈ fs, gfaceB O c.A c.C q.2.2 e = true) ∧ ∃ e ∈ fs, z ∈ (realR φ ψ e).set := by
    intro q hq z hz hzU
    have hfc := (hloc q hq).2
    have hk := (hloc q hq).1.2
    cases hfa : q.1.faces (c.U.getD q.2.1 GBox.default) with
    | none => rw [hfa] at hfc; cases hfc
    | some fs =>
      rw [hfa] at hfc
      simp only [List.all_eq_true] at hfc
      exact ⟨fs, rfl, hfc,
        GRect.faces_sound hφ hψ (hUwf _ (hUmem _ hk)) (hqwf q hq) hfa hz hzU⟩
  have key := sees_mem_of_local (L := L) (Rest := Rest) (C := goptCone φ ψ w c.C) (w := w) (p := p)
    (fun x hx => by obtain ⟨q, _, rfl⟩ := hmemL x hx; exact isClosed_rect_set _) hRc
    (fun x hx => by
      obtain ⟨q, hq, rfl⟩ := hmemL x hx
      exact gstarFrom_cones (fun K hK h hh => hst h (List.mem_append_left _
        (List.mem_flatMap.2 ⟨q, hq, List.mem_flatten.2 ⟨K, hK, hh⟩⟩))))
    (gstarFrom_optCone (fun K hK h hh => hst h (List.mem_append_right _ (by rw [hK]; exact hh))))
    (fun x hx hwx => by
      obtain ⟨q, hq, rfl⟩ := hmemL x hx
      have hb := (hloc q hq).1.1.2
      simp only [gbaseB, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
        List.all_eq_true] at hb
      rcases hb with hb | ⟨K, hK, hb⟩
      · exact (GRect.inter_empty hφ hψ hAwf (hqwf q hq) hb hw hwx).elim
      · intro z hz
        exact ⟨K, hK, fun h hh => ghNN_sound hO (hb h hh) hw hz⟩)
    (fun r hr hwr => hRU r hr w hwr _ (hUmem _ hAb) hwU')
    (fun x hx x' hx' z hz hz' hzF _ => by
      obtain ⟨q, hq, rfl⟩ := hmemL x hx
      obtain ⟨q', hq', rfl⟩ := hmemL x' hx'
      obtain ⟨K, hK, hzK⟩ := hzF
      have hp : gpropB O c.A q q' = true := by
        have := hpr q hq
        simp only [Bool.or_eq_true, List.isEmpty_iff, List.all_eq_true] at this
        rcases this with h | h
        · rw [h] at hK; simp at hK
        · exact h q' hq'
      unfold gpropB at hp
      simp only [Bool.or_eq_true, List.isEmpty_iff] at hp
      rcases hp with hp | hp
      · rw [hp] at hK; simp at hK
      split at hp
      · rename_i hi; exact (GRect.inter_empty hφ hψ (hqwf q hq) (hqwf q' hq') hi hz hz').elim
      · rename_i X hi
        have hzX := GRect.inter_sub hi hz hz'
        simp only [List.all_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at hp
        rcases hp K hK with ⟨h, hh, hneg⟩ | ⟨K', hK', hall⟩
        · exact absurd (hzK h hh) (ghNeg_sound hO hneg hw hzX)
        · refine ⟨K', hK', fun h hh => ?_⟩
          rcases hall h hh with hin | hnn
          · exact hzK h hin
          · exact ghNN_sound hO hnn hw hzX)
    (fun x hx r hr z hz hzr hzF _ => by
      obtain ⟨q, hq, rfl⟩ := hmemL x hx
      obtain ⟨fs, -, hfc, e, he, hze⟩ := hface q hq z hz
        (hRU r hr z hzr _ (hUmem _ (hloc q hq).1.2))
      obtain ⟨K, hK, hzK⟩ := hzF
      have hf := hfc e he
      unfold gfaceB at hf
      cases hC : c.C with
      | none =>
        exfalso
        rw [hC] at hf
        simp only [List.all_eq_true, List.any_eq_true] at hf
        obtain ⟨h, hh, hneg⟩ := hf K hK
        exact ghNeg_sound hO hneg hw hze (hzK h hh)
      | some hsC =>
        rw [hC] at hf
        simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true,
          decide_eq_true_eq] at hf
        rcases hf.1 K hK with ⟨h, hh, hneg⟩ | hall
        · exact absurd (hzK h hh) (ghNeg_sound hO hneg hw hze)
        · intro h hh
          rcases hall h hh with hin | hnn
          · exact hzK h hin
          · exact ghNN_sound hO hnn hw hze)
    (fun r hr x hx z hzr hz hzC _ => by
      obtain ⟨q, hq, rfl⟩ := hmemL x hx
      obtain ⟨fs, -, hfc, e, he, hze⟩ := hface q hq z hz
        (hRU r hr z hzr _ (hUmem _ (hloc q hq).1.2))
      have hf := hfc e he
      unfold gfaceB at hf
      cases hC : c.C with
      | none => rw [hC] at hzC; exact absurd hzC (by simp [goptCone])
      | some hsC =>
        rw [hC] at hzC hf
        simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true,
          decide_eq_true_eq] at hf
        rcases hf.2 with ⟨h, hh, hneg⟩ | ⟨K, hK, hall⟩
        · exact absurd (hzC h hh) (ghNeg_sound hO hneg hw hze)
        · refine ⟨K, hK, fun h hh => ?_⟩
          rcases hall h hh with hin | hnn
          · exact hzC h hin
          · exact ghNN_sound hO hnn hw hze)
    (fun t h0 h1 => by
      rcases hseg t h0 h1 with ⟨q, hq, hz⟩ | ⟨r, hr, hz⟩
      · exact Or.inl ⟨_, List.mem_map.2 ⟨q, hq, rfl⟩, hz⟩
      · exact Or.inr ⟨r, hr, hz⟩)
  rcases key with ⟨x, hx, hp1, hp2⟩ | ⟨r, hr, hp1, hp2⟩
  · obtain ⟨q, hq, rfl⟩ := hmemL x hx
    by_cases hin : p ∈ (c.U.getD q.2.1 GBox.default).set φ ψ
    · exact Or.inl ⟨q, hq, hp1, hp2, hin⟩
    right
    have hk := (hloc q hq).1.2
    obtain ⟨fs, hfa, hfc, e, he, hze⟩ := hface q hq p hp1 hin
    have hf := hfc e he
    obtain ⟨K, hK, hpK⟩ := hp2
    refine ⟨?_, fun U hU hpU => ?_⟩
    · unfold gfaceB at hf
      cases hC : c.C with
      | none =>
        rw [hC] at hf
        simp only [List.all_eq_true, List.any_eq_true] at hf
        obtain ⟨h, hh, hneg⟩ := hf K hK
        exact absurd (hpK h hh) (ghNeg_sound hO hneg hw hze)
      | some hsC =>
        rw [hC] at hf
        simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true,
          decide_eq_true_eq] at hf
        rcases hf.1 K hK with ⟨h, hh, hneg⟩ | hall
        · exact absurd (hpK h hh) (ghNeg_sound hO hneg hw hze)
        · intro h hh
          rcases hall h hh with hin' | hnn
          · exact hpK h hin'
          · exact ghNN_sound hO hnn hw hze
    · obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem hU
      by_cases hkk : k' = q.2.1
      · subst hkk
        rw [List.getD_eq_getElem _ _ hk'] at hin
        exact hin hpU
      · simp only [GCert.ok.boxesSepG, List.all_eq_true, List.mem_range, Bool.or_eq_true,
          decide_eq_true_eq] at hsep
        rcases hsep q.2.1 hk k' hk' with h | h
        · exact hkk h.symm
        · have := GBox.sepB_sound hφ hψ (hUwf _ (hUmem _ hk)) (hUwf _ (hUmem _ hk')) h
            (GRect.faces_closed hφ hψ (hUwf _ (hUmem _ hk)) (hqwf q hq) hfa hp1)
          rw [List.getD_eq_getElem _ _ hk'] at this
          exact this hpU
  · exact Or.inr ⟨hp2, hRU r hr p hp1⟩

end CertSound

/-! ### Disjointness of pieces -/

/-- Two cones are disjoint on the rectangle `X`: a half-plane of one of them is strictly negative
on it, possibly after splitting it at a middle grid line at most `d` times. -/
def gsepB (O : GOr) (A1 : GRect) (K1 : List GHP) (A2 : GRect) (K2 : List GHP) : ℕ → GRect → Bool
  | 0, X => K1.any (fun h => ghNeg O A1 h X.corners) || K2.any (fun h => ghNeg O A2 h X.corners)
  | d + 1, X => K1.any (fun h => ghNeg O A1 h X.corners) || K2.any (fun h => ghNeg O A2 h X.corners) ||
      (decide (X.1 + 1 < X.2.1) &&
        gsepB O A1 K1 A2 K2 d (X.1, (X.1 + X.2.1) / 2, X.2.2.1, X.2.2.2) &&
        gsepB O A1 K1 A2 K2 d ((X.1 + X.2.1) / 2, X.2.1, X.2.2.1, X.2.2.2)) ||
      (decide (X.2.2.1 + 1 < X.2.2.2) &&
        gsepB O A1 K1 A2 K2 d (X.1, X.2.1, X.2.2.1, (X.2.2.1 + X.2.2.2) / 2) &&
        gsepB O A1 K1 A2 K2 d (X.1, X.2.1, (X.2.2.1 + X.2.2.2) / 2, X.2.2.2))

section Disj

variable {φ ψ : ℕ → ℝ} {NX NY : ℕ} (hφ : StrictMonoOn φ (Iio NX)) (hψ : StrictMonoOn ψ (Iio NY))
  {O : GOr} (hO : O.Sound φ ψ)
include hφ hψ hO

omit hφ hψ in
theorem gsepB_sound {A1 A2 : GRect} {K1 K2 : List GHP}
    {w1 w2 : Point} (hw1 : w1 ∈ (realR φ ψ A1).set) (hw2 : w2 ∈ (realR φ ψ A2).set) :
    ∀ (d : ℕ) (X : GRect), X.wf NX NY = true → gsepB O A1 K1 A2 K2 d X = true →
      ∀ z ∈ (realR φ ψ X).set, z ∈ gcone φ ψ w1 K1 → z ∉ gcone φ ψ w2 K2
  | 0, X, _, h, z, hz, h1, h2 => by
    simp only [gsepB, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨h, hh, hn⟩ | ⟨h, hh, hn⟩
    · exact ghNeg_sound hO hn hw1 hz (h1 h hh)
    · exact ghNeg_sound hO hn hw2 hz (h2 h hh)
  | d + 1, X, hX, h, z, hz, h1, h2 => by
    have b := GRect.wf_bounds hX
    simp only [gsepB, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
    simp only [realR] at hx0 hx1 hy0 hy1
    rcases h with ((⟨h, hh, hn⟩ | ⟨h, hh, hn⟩) | ⟨⟨hlt, hlo⟩, hhi⟩) | ⟨⟨hlt, hlo⟩, hhi⟩
    · exact ghNeg_sound hO hn hw1 ⟨hx0, hx1, hy0, hy1⟩ (h1 h hh)
    · exact ghNeg_sound hO hn hw2 ⟨hx0, hx1, hy0, hy1⟩ (h2 h hh)
    · rcases le_total z.1 (φ ((X.1 + X.2.1) / 2)) with hc | hc
      · exact gsepB_sound hw1 hw2 d _ (by simp only [GRect.wf, decide_eq_true_eq]; omega) hlo z
          ⟨hx0, hc, hy0, hy1⟩ h1 h2
      · exact gsepB_sound hw1 hw2 d _ (by simp only [GRect.wf, decide_eq_true_eq]; omega) hhi z
          ⟨hc, hx1, hy0, hy1⟩ h1 h2
    · rcases le_total z.2 (ψ ((X.2.2.1 + X.2.2.2) / 2)) with hc | hc
      · exact gsepB_sound hw1 hw2 d _ (by simp only [GRect.wf, decide_eq_true_eq]; omega) hlo z
          ⟨hx0, hx1, hy0, hc⟩ h1 h2
      · exact gsepB_sound hw1 hw2 d _ (by simp only [GRect.wf, decide_eq_true_eq]; omega) hhi z
          ⟨hx0, hx1, hc, hy1⟩ h1 h2

end Disj

/-- The pieces of two certificates (same grid) are disjoint. -/
def gdisjB (O : GOr) (d : ℕ) (c1 c2 : GCert) : Bool :=
  c1.cs.all fun q1 => q1.2.2.isEmpty || c2.cs.all fun q2 => q2.2.2.isEmpty ||
    match q1.1.inter q2.1 with
    | none => true
    | some X => q1.2.2.all fun K1 => q2.2.2.all fun K2 => gsepB O c1.A K1 c2.A K2 d X

section Disj2

variable {φ ψ : ℕ → ℝ} {NX NY : ℕ} (hφ : StrictMonoOn φ (Iio NX)) (hψ : StrictMonoOn ψ (Iio NY))
  {O : GOr} (hO : O.Sound φ ψ)
include hφ hψ hO

theorem gdisjB_sound {d : ℕ} {c1 c2 : GCert} (h : gdisjB O d c1 c2 = true)
    {w1 w2 : Point} (hw1 : w1 ∈ (realR φ ψ c1.A).set) (hw2 : w2 ∈ (realR φ ψ c2.A).set) {p : Point}
    {q1 : GRect × ℕ × List (List GHP)} (hq1 : q1 ∈ c1.cs) (hwf1 : q1.1.wf NX NY = true)
    (hp1 : p ∈ (realR φ ψ q1.1).set) (hc1 : p ∈ gcones φ ψ w1 q1.2.2)
    {q2 : GRect × ℕ × List (List GHP)} (hq2 : q2 ∈ c2.cs) (hwf2 : q2.1.wf NX NY = true)
    (hp2 : p ∈ (realR φ ψ q2.1).set) (hc2 : p ∈ gcones φ ψ w2 q2.2.2) : False := by
  simp only [gdisjB, List.all_eq_true, Bool.or_eq_true, List.isEmpty_iff] at h
  obtain ⟨K1, hK1, hpK1⟩ := hc1
  obtain ⟨K2, hK2, hpK2⟩ := hc2
  have h' : (match q1.1.inter q2.1 with
    | none => true
    | some X => q1.2.2.all fun K1 => q2.2.2.all fun K2 => gsepB O c1.A K1 c2.A K2 d X) = true := by
    rcases h q1 hq1 with h1 | h1
    · rw [h1] at hK1; simp at hK1
    rcases h1 q2 hq2 with h2 | h2
    · rw [h2] at hK2; simp at hK2
    exact h2
  split at h'
  · rename_i hi; exact GRect.inter_empty hφ hψ hwf1 hwf2 hi hp1 hp2
  · rename_i X hi
    simp only [List.all_eq_true] at h'
    exact gsepB_sound hO hw1 hw2 d X (GRect.inter_wf hwf1 hwf2 hi) (h' K1 hK1 K2 hK2) p
      (GRect.inter_sub hi hp1 hp2) hpK1 hpK2

end Disj2

end

end ArtGallery.Orthogonal.Hard
