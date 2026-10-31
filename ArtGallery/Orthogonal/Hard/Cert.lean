module

public import ArtGallery.Orthogonal.Hard.Propagate
public import ArtGallery.Orthogonal.Hard.CombRegion

/-!
# Visibility certificates

A certificate proves "every point of the region that sees the target `w` lies in an explicit
set" for all values `H ≥ 1000` of the parameter at once.  It lives in a *local frame* (origin
`ox`): abscissae are rationals (independent of `H`), ordinates are affine functions `a + b H`
(`AH`).  A certificate lists *local rectangles* `r_i` with *cones* `F_i` (intersections of
half-planes `det(u, v, ·) ≥ 0` through points of the frame; `none` is the empty set) and a set
`C` for all other rectangles of the region, which lie outside an open box `U` (`none`: empty).

The abstract statement (`sees_mem_of_local`) is the cone propagation of `Propagate.lean` for the
cover "local rectangles ++ the rest".  The checker `LCert.ok` verifies its hypotheses robustly:
every sign test `0 ≤ a + b H` is decided by `0 ≤ b ∧ 0 ≤ a + 1000 b`.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry Set

/-! ### Localised cone propagation (abstract) -/

/-- **Localised cone propagation.**  Local closed sets `q.1` with cones `q.2`, the other closed
sets `Rest` with the common set `C`; if the segment `w p` is covered, then `p` lies in a local set
and its cone, or in a rest set and `C`. -/
theorem sees_mem_of_local {L : List (Set Point × Set Point)} {Rest : List (Set Point)}
    {C : Set Point} {w p : Point}
    (hcl : ∀ q ∈ L, IsClosed q.1) (hclR : ∀ r ∈ Rest, IsClosed r)
    (hF : ∀ q ∈ L, StarFrom w q.2) (hC : StarFrom w C)
    (hbase : ∀ q ∈ L, w ∈ q.1 → q.1 ⊆ q.2) (hbaseR : ∀ r ∈ Rest, w ∉ r)
    (hLL : ∀ q ∈ L, ∀ q' ∈ L, ∀ z ∈ q.1, z ∈ q'.1 → z ∈ q.2 → z ≠ w → z ∈ q'.2)
    (hLR : ∀ q ∈ L, ∀ r ∈ Rest, ∀ z ∈ q.1, z ∈ r → z ∈ q.2 → z ≠ w → z ∈ C)
    (hRL : ∀ r ∈ Rest, ∀ q ∈ L, ∀ z ∈ r, z ∈ q.1 → z ∈ C → z ≠ w → z ∈ q.2)
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (∃ q ∈ L, lerp w p t ∈ q.1) ∨ ∃ r ∈ Rest, lerp w p t ∈ r) :
    (∃ q ∈ L, p ∈ q.1 ∧ p ∈ q.2) ∨ (∃ r ∈ Rest, p ∈ r ∧ p ∈ C) := by
  classical
  let ι := Fin L.length ⊕ Fin Rest.length
  let r : ι → Set Point := fun i => Sum.elim (fun k => L[k].1) (fun k => Rest[k]) i
  let F : ι → Set Point := fun i => Sum.elim (fun k => L[k].2) (fun _ => C) i
  have hmemL : ∀ k : Fin L.length, L[k] ∈ L := fun k => List.getElem_mem _
  have hmemR : ∀ k : Fin Rest.length, Rest[k] ∈ Rest := fun k => List.getElem_mem _
  have key := mem_of_propagate (ι := ι) r F (w := w) (p := p)
    (fun i => by rcases i with k | k; exacts [hcl _ (hmemL k), hclR _ (hmemR k)])
    (fun i => by rcases i with k | k; exacts [hF _ (hmemL k), hC])
    (fun i hw => by
      rcases i with k | k
      · exact hbase _ (hmemL k) hw
      · exact absurd hw (hbaseR _ (hmemR k)))
    (fun i j z hzi hzj hzF hzw => by
      rcases i with k | k <;> rcases j with k' | k'
      · exact hLL _ (hmemL k) _ (hmemL k') z hzi hzj hzF hzw
      · exact hLR _ (hmemL k) _ (hmemR k') z hzi hzj hzF hzw
      · exact hRL _ (hmemR k) _ (hmemL k') z hzi hzj hzF hzw
      · exact hzF)
    (fun t h0 h1 => by
      rcases hseg t h0 h1 with ⟨q, hq, hz⟩ | ⟨q, hq, hz⟩
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
        exact ⟨Sum.inl ⟨k, hk⟩, hz⟩
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
        exact ⟨Sum.inr ⟨k, hk⟩, hz⟩)
  have hp := hseg 1 zero_le_one le_rfl
  have e1 : lerp w p 1 = p := by ext <;> simp [lerp]
  rw [e1] at hp
  rcases hp with ⟨q, hq, hz⟩ | ⟨q, hq, hz⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
    exact Or.inl ⟨_, hq, hz, key (Sum.inl ⟨k, hk⟩) hz⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
    exact Or.inr ⟨_, hq, hz, key (Sum.inr ⟨k, hk⟩) hz⟩

/-! ### Affine functions of `H` and robust signs -/

/-- `a + b H`. -/
abbrev AH := ℚ × ℚ

/-- The value of `a + b H`. -/
def AH.ev (H : ℝ) (e : AH) : ℝ := (e.1 : ℝ) + (e.2 : ℝ) * H

/-- Robust `0 ≤ a + b H` for all `H ≥ 1000`. -/
def AH.nn (e : AH) : Bool := decide (0 ≤ e.2 ∧ 0 ≤ e.1 + e.2 * 1000)

/-- Robust `0 < a + b H` for all `H ≥ 1000`. -/
def AH.pos (e : AH) : Bool := decide (0 ≤ e.2 ∧ 0 < e.1 + e.2 * 1000)

theorem AH.nn_sound {e : AH} (h : e.nn = true) {H : ℝ} (hH : 1000 ≤ H) : 0 ≤ e.ev H := by
  obtain ⟨h1, h2⟩ := of_decide_eq_true h
  have h1' : (0 : ℝ) ≤ e.2 := by exact_mod_cast h1
  have h2' : (0 : ℝ) ≤ e.1 + e.2 * 1000 := by exact_mod_cast h2
  unfold AH.ev; nlinarith

theorem AH.pos_sound {e : AH} (h : e.pos = true) {H : ℝ} (hH : 1000 ≤ H) : 0 < e.ev H := by
  obtain ⟨h1, h2⟩ := of_decide_eq_true h
  have h1' : (0 : ℝ) ≤ e.2 := by exact_mod_cast h1
  have h2' : (0 : ℝ) < e.1 + e.2 * 1000 := by exact_mod_cast h2
  unfold AH.ev; nlinarith

/-- Robust `e ≤ e'`. -/
def AH.le (e e' : AH) : Bool := AH.nn (e'.1 - e.1, e'.2 - e.2)

/-- Robust `e < e'`. -/
def AH.lt (e e' : AH) : Bool := AH.pos (e'.1 - e.1, e'.2 - e.2)

theorem AH.le_sound {e e' : AH} (h : AH.le e e' = true) {H : ℝ} (hH : 1000 ≤ H) :
    e.ev H ≤ e'.ev H := by
  have := AH.nn_sound h hH
  unfold AH.ev at *; push_cast at this; linarith

theorem AH.lt_sound {e e' : AH} (h : AH.lt e e' = true) {H : ℝ} (hH : 1000 ≤ H) :
    e.ev H < e'.ev H := by
  have := AH.pos_sound h hH
  unfold AH.ev at *; push_cast at this; linarith

/-! ### Points, half-planes, rectangles of a frame -/

/-- A point of a local frame: `(x, a + b H)`. -/
abbrev LP := ℚ × AH

/-- The real point (frame origin `ox`). -/
def LP.real (ox H : ℝ) (p : LP) : Point := (ox + p.1, p.2.ev H)

/-- `det(u, v, z)` as an affine function of `H` (abscissae do not depend on `H`). -/
def hpv (u v z : LP) : AH :=
  ((v.1 - u.1) * (z.2.1 - u.2.1) - (z.1 - u.1) * (v.2.1 - u.2.1),
    (v.1 - u.1) * (z.2.2 - u.2.2) - (z.1 - u.1) * (v.2.2 - u.2.2))

theorem hpv_ev (ox H : ℝ) (u v z : LP) :
    det (u.real ox H) (v.real ox H) (z.real ox H) = (hpv u v z).ev H := by
  simp only [det, LP.real, hpv, AH.ev]; push_cast; ring

/-! ### Half-planes through frame points and the target -/

/-- An endpoint of the line of a half-plane: a frame point, or (`none`) the target point. -/
abbrev HE := Option LP

/-- A half-plane `{z | 0 ≤ det(u, v, z)}` (to the left of `u → v`); the endpoints may be the
target point. -/
abbrev HP := HE × HE

/-- The real endpoint for the target `w`. -/
def HE.pt (ox H : ℝ) (w : Point) : HE → Point
  | none => w
  | some p => p.real ox H

/-- The real half-plane for the target `w`. -/
def HP.set (ox H : ℝ) (w : Point) (h : HP) : Set Point :=
  {z | 0 ≤ det (h.1.pt ox H w) (h.2.pt ox H w) z}

/-- A cone: an intersection of half-planes. -/
def cone (ox H : ℝ) (w : Point) (K : List HP) : Set Point := {z | ∀ h ∈ K, z ∈ h.set ox H w}

/-- A finite union of cones. -/
def conesSet (ox H : ℝ) (w : Point) (Ks : List (List HP)) : Set Point :=
  {z | ∃ K ∈ Ks, z ∈ cone ox H w K}

/-- An optional cone (`none`: empty). -/
def optCone (ox H : ℝ) (w : Point) : Option (List HP) → Set Point
  | none => ∅
  | some K => cone ox H w K

/-- A rectangle `[x₀, x₁] × [y₀, y₁]` of a frame. -/
structure LR where
  x0 : ℚ
  x1 : ℚ
  y0 : AH
  y1 : AH

/-- Decidable equality of rectangles by their fields, without casts along the field equalities
(see `ArtGallery/Orthogonal/Hard/RatEq.lean`). -/
instance LR.decEq : DecidableEq LR := fun a b =>
  if h : a.x0 = b.x0 ∧ a.x1 = b.x1 ∧ a.y0 = b.y0 ∧ a.y1 = b.y1 then
    isTrue (by cases a; cases b; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl)
  else isFalse (by rintro rfl; exact h ⟨rfl, rfl, rfl, rfl⟩)

/-- The real rectangle. -/
def LR.real (ox H : ℝ) (r : LR) : Rect := (ox + r.x0, ox + r.x1, r.y0.ev H, r.y1.ev H)

/-- The four corners. -/
def LR.corners (r : LR) : List LP := [(r.x0, r.y0), (r.x1, r.y0), (r.x0, r.y1), (r.x1, r.y1)]

/-- An affine function nonnegative at the four corners is nonnegative on the rectangle. -/
theorem affine_nonneg_rect {α β γ x0 x1 y0 y1 x y : ℝ}
    (h00 : 0 ≤ α * x0 + β * y0 + γ) (h10 : 0 ≤ α * x1 + β * y0 + γ)
    (h01 : 0 ≤ α * x0 + β * y1 + γ) (h11 : 0 ≤ α * x1 + β * y1 + γ)
    (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hy0 : y0 ≤ y) (hy1 : y ≤ y1) : 0 ≤ α * x + β * y + γ := by
  have hy : ∀ x', (0 ≤ α * x' + β * y0 + γ) → (0 ≤ α * x' + β * y1 + γ) →
      0 ≤ α * x' + β * y + γ := by
    intro x' a b
    rcases le_total 0 β with hb | hb
    · nlinarith [mul_le_mul_of_nonneg_left hy0 hb]
    · nlinarith [mul_le_mul_of_nonpos_left hy1 hb]
  have e0 := hy x0 h00 h01
  have e1 := hy x1 h10 h11
  rcases le_total 0 α with ha | ha
  · nlinarith [mul_le_mul_of_nonneg_left hx0 ha]
  · nlinarith [mul_le_mul_of_nonpos_left hx1 ha]

theorem det_affine (u v z : Point) :
    det u v z = (-(v.2 - u.2)) * z.1 + (v.1 - u.1) * z.2 +
      ((v.2 - u.2) * u.1 - (v.1 - u.1) * u.2) := by
  simp only [det]; ring

/-- A lower bound of an affine function at the four corners holds on the rectangle. -/
theorem affine_rect {A B G x0 x1 y0 y1 c : ℝ} (f : ℝ → ℝ → ℝ)
    (hf : ∀ x y, f x y = A * x + B * y + G)
    (h00 : c ≤ f x0 y0) (h10 : c ≤ f x1 y0) (h01 : c ≤ f x0 y1) (h11 : c ≤ f x1 y1)
    {x y : ℝ} (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hy0 : y0 ≤ y) (hy1 : y ≤ y1) : c ≤ f x y := by
  rw [hf] at h00 h10 h01 h11 ⊢
  have := affine_nonneg_rect (α := A) (β := B) (γ := G - c) (by linarith) (by linarith)
    (by linarith) (by linarith) hx0 hx1 hy0 hy1
  linarith

theorem affine_pos_rect {A B G x0 x1 y0 y1 : ℝ} (f : ℝ → ℝ → ℝ)
    (hf : ∀ x y, f x y = A * x + B * y + G)
    (h00 : 0 < f x0 y0) (h10 : 0 < f x1 y0) (h01 : 0 < f x0 y1) (h11 : 0 < f x1 y1)
    {x y : ℝ} (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hy0 : y0 ≤ y) (hy1 : y ≤ y1) : 0 < f x y := by
  have hm : 0 < min (min (f x0 y0) (f x1 y0)) (min (f x0 y1) (f x1 y1)) :=
    lt_min (lt_min h00 h10) (lt_min h01 h11)
  have := affine_rect f hf ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _)) ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) hx0 hx1 hy0 hy1
  linarith

/-- `det(E₁(w), E₂(w), z)` is affine in the target `w`. -/
theorem det_he_affine (ox H : ℝ) (h : HP) (z : Point) : ∃ α β γ : ℝ, ∀ x y : ℝ,
    det (h.1.pt ox H (x, y)) (h.2.pt ox H (x, y)) z = α * x + β * y + γ := by
  rcases h with ⟨e1, e2⟩
  cases e1 with
  | none =>
    cases e2 with
    | none => exact ⟨0, 0, 0, fun x y => by simp only [HE.pt, det]; ring⟩
    | some p =>
      exact ⟨(p.real ox H).2 - z.2, z.1 - (p.real ox H).1,
        (p.real ox H).1 * z.2 - z.1 * (p.real ox H).2, fun x y => by simp only [HE.pt, det]; ring⟩
  | some p =>
    cases e2 with
    | none =>
      exact ⟨z.2 - (p.real ox H).2, -(z.1 - (p.real ox H).1),
        -(p.real ox H).1 * (z.2 - (p.real ox H).2) + (p.real ox H).2 * (z.1 - (p.real ox H).1),
        fun x y => by simp only [HE.pt, det]; ring⟩
    | some q =>
      exact ⟨0, 0, det (p.real ox H) (q.real ox H) z, fun x y => by simp only [HE.pt]; ring⟩

/-- The value `det(u, v, z)` with the target at the frame point `a`. -/
def hpvA (a : LP) (h : HP) (z : LP) : AH := hpv (h.1.getD a) (h.2.getD a) z

theorem HE.pt_real (ox H : ℝ) (a : LP) (e : HE) :
    e.pt ox H (a.real ox H) = (e.getD a).real ox H := by
  cases e <;> rfl

theorem hpvA_ev (ox H : ℝ) (a : LP) (h : HP) (z : LP) :
    det (h.1.pt ox H (a.real ox H)) (h.2.pt ox H (a.real ox H)) (z.real ox H) =
      (hpvA a h z).ev H := by
  rw [HE.pt_real, HE.pt_real, hpvA, hpv_ev]

/-- Corners of the rectangle of targets and of the rectangle of points. -/
theorem corners_mem {r : LR} {P : LP → Prop} (h : ∀ c ∈ r.corners, P c) :
    P (r.x0, r.y0) ∧ P (r.x1, r.y0) ∧ P (r.x0, r.y1) ∧ P (r.x1, r.y1) := by
  simp only [LR.corners, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  exact h

/-- A bound at the corners (for every corner target) gives the bound for every target of `A` at
every point of `r`. -/
theorem hp_bound_rect {ox H : ℝ} {h : HP} {A r : LR} {Q : ℝ → Prop}
    (hQ : ∀ (f : ℝ → ℝ → ℝ) (α β γ x0 x1 y0 y1 x y : ℝ), (∀ x y, f x y = α * x + β * y + γ) →
      Q (f x0 y0) → Q (f x1 y0) → Q (f x0 y1) → Q (f x1 y1) →
      x0 ≤ x → x ≤ x1 → y0 ≤ y → y ≤ y1 → Q (f x y))
    (hc : ∀ a ∈ A.corners, ∀ c ∈ r.corners, Q ((hpvA a h c).ev H))
    {w : Point} (hw : w ∈ (A.real ox H).set) {z : Point} (hz : z ∈ (r.real ox H).set) :
    Q (det (h.1.pt ox H w) (h.2.pt ox H w) z) := by
  -- first every corner of `r`, for the target `w`
  have step1 : ∀ c ∈ r.corners, Q (det (h.1.pt ox H w) (h.2.pt ox H w) (c.real ox H)) := by
    intro c hcm
    obtain ⟨α, β, γ, hf⟩ := det_he_affine ox H h (c.real ox H)
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
    simp only [LR.real] at hx0 hx1 hy0 hy1
    have hcA := corners_mem (P := fun a => Q ((hpvA a h c).ev H)) (fun a ha => hc a ha c hcm)
    obtain ⟨q00, q10, q01, q11⟩ := hcA
    rw [← hpvA_ev] at q00 q10 q01 q11
    simp only [LP.real] at q00 q10 q01 q11
    have := hQ (fun x y => det (h.1.pt ox H (x, y)) (h.2.pt ox H (x, y)) (c.real ox H)) α β γ
      _ _ _ _ w.1 w.2 hf q00 q10 q01 q11 hx0 hx1 hy0 hy1
    simpa using this
  obtain ⟨q00, q10, q01, q11⟩ := corners_mem step1
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  simp only [LR.real] at hx0 hx1 hy0 hy1
  simp only [LP.real] at q00 q10 q01 q11
  have := hQ (fun x y => det (h.1.pt ox H w) (h.2.pt ox H w) (x, y))
    (-((h.2.pt ox H w).2 - (h.1.pt ox H w).2)) ((h.2.pt ox H w).1 - (h.1.pt ox H w).1)
    (((h.2.pt ox H w).2 - (h.1.pt ox H w).2) * (h.1.pt ox H w).1 -
      ((h.2.pt ox H w).1 - (h.1.pt ox H w).1) * (h.1.pt ox H w).2)
    _ _ _ _ z.1 z.2 (fun x y => det_affine _ _ (x, y)) q00 q10 q01 q11 hx0 hx1 hy0 hy1
  simpa using this

/-! ### Robust tests on rectangles -/

/-- `0 ≤ det` robustly, for every corner target of `A`, at every point of a list. -/
def hpNN (A : LR) (h : HP) (cs : List LP) : Bool :=
  A.corners.all fun a => cs.all fun c => (hpvA a h c).nn

/-- `det < 0` robustly, for every corner target of `A`, at every point of a list. -/
def hpNeg (A : LR) (h : HP) (cs : List LP) : Bool :=
  A.corners.all fun a => cs.all fun c => AH.pos (-(hpvA a h c).1, -(hpvA a h c).2)

theorem hpNN_sound {A r : LR} {h : HP} (hh : hpNN A h r.corners = true) {H : ℝ} (hH : 1000 ≤ H)
    (ox : ℝ) {w : Point} (hw : w ∈ (A.real ox H).set) {z : Point} (hz : z ∈ (r.real ox H).set) :
    z ∈ h.set ox H w := by
  refine hp_bound_rect (h := h) (Q := fun v => 0 ≤ v) (fun f α β γ x0 x1 y0 y1 x y hf a b c d e g i j =>
    affine_rect (c := 0) f hf a b c d e g i j) (fun a ha c hc => ?_) hw hz
  simp only [hpNN, List.all_eq_true] at hh
  exact AH.nn_sound (hh a ha c hc) hH

theorem hpNeg_sound {A r : LR} {h : HP} (hh : hpNeg A h r.corners = true) {H : ℝ} (hH : 1000 ≤ H)
    (ox : ℝ) {w : Point} (hw : w ∈ (A.real ox H).set) {z : Point} (hz : z ∈ (r.real ox H).set) :
    z ∉ h.set ox H w := by
  intro hzh
  have := hp_bound_rect (h := h) (Q := fun v => 0 < -v)
    (fun f α β γ x0 x1 y0 y1 x y hf a b c d e g i j =>
      affine_pos_rect (fun x y => -f x y) (A := -α) (B := -β) (G := -γ)
        (fun x y => by rw [hf]; ring) a b c d e g i j) (fun a ha c hc => ?_) hw hz
  · have h' : 0 ≤ det (h.1.pt ox H w) (h.2.pt ox H w) z := hzh
    linarith
  · simp only [hpNeg, List.all_eq_true] at hh
    have := AH.pos_sound (hh a ha c hc) hH
    simp only [AH.ev] at this ⊢; push_cast at this; linarith

/-- The distinct corners of a rectangle (one for a point, two for a segment). -/
def LR.cornersD (r : LR) : List LP :=
  if r.x0 = r.x1 then (if r.y0 = r.y1 then [(r.x0, r.y0)] else [(r.x0, r.y0), (r.x0, r.y1)])
  else if r.y0 = r.y1 then [(r.x0, r.y0), (r.x1, r.y0)] else r.corners

theorem LR.mem_cornersD {r : LR} {a : LP} : a ∈ r.cornersD ↔ a ∈ r.corners := by
  unfold LR.cornersD LR.corners
  split_ifs with h1 h2 h2 <;>
    simp only [h1, h2, List.mem_cons, List.not_mem_nil, or_false] <;> tauto

/-- `hpNN` at the corners of a rectangle `r`, evaluated at its distinct corners only, and once
(not for every corner target) for a half-plane through two fixed points. -/
def hpNNr (A : LR) (h : HP) (r : LR) : Bool :=
  if h.1.isSome && h.2.isSome then r.cornersD.all fun c => (hpvA (A.x0, A.y0) h c).nn
  else A.cornersD.all fun a => r.cornersD.all fun c => (hpvA a h c).nn

/-- `hpNeg` at the corners of a rectangle `r`, as `hpNNr`. -/
def hpNegr (A : LR) (h : HP) (r : LR) : Bool :=
  if h.1.isSome && h.2.isSome then
    r.cornersD.all fun c => AH.pos (-(hpvA (A.x0, A.y0) h c).1, -(hpvA (A.x0, A.y0) h c).2)
  else A.cornersD.all fun a => r.cornersD.all fun c => AH.pos (-(hpvA a h c).1, -(hpvA a h c).2)

theorem hpvA_fixed {u v : LP} (a b : LP) (z : LP) :
    hpvA a (some u, some v) z = hpvA b (some u, some v) z := rfl

theorem hpNN_of_r {A r : LR} {h : HP} (hh : hpNNr A h r = true) : hpNN A h r.corners = true := by
  obtain ⟨e1, e2⟩ := h
  simp only [hpNN, List.all_eq_true]
  intro a ha c hc
  rw [← LR.mem_cornersD] at hc
  cases e1 <;> cases e2 <;>
    simp only [hpNNr, Option.isSome_none, Option.isSome_some, Bool.false_and, Bool.and_false,
      Bool.and_self, ite_true, Bool.false_eq_true, ite_false, List.all_eq_true] at hh
  · exact hh a (LR.mem_cornersD.2 ha) c hc
  · exact hh a (LR.mem_cornersD.2 ha) c hc
  · exact hh a (LR.mem_cornersD.2 ha) c hc
  · exact hh c hc

theorem hpNeg_of_r {A r : LR} {h : HP} (hh : hpNegr A h r = true) : hpNeg A h r.corners = true := by
  obtain ⟨e1, e2⟩ := h
  simp only [hpNeg, List.all_eq_true]
  intro a ha c hc
  rw [← LR.mem_cornersD] at hc
  cases e1 <;> cases e2 <;>
    simp only [hpNegr, Option.isSome_none, Option.isSome_some, Bool.false_and, Bool.and_false,
      Bool.and_self, ite_true, Bool.false_eq_true, ite_false, List.all_eq_true] at hh
  · exact hh a (LR.mem_cornersD.2 ha) c hc
  · exact hh a (LR.mem_cornersD.2 ha) c hc
  · exact hh a (LR.mem_cornersD.2 ha) c hc
  · exact hh c hc

theorem hpNNr_sound {A r : LR} {h : HP} (hh : hpNNr A h r = true) {H : ℝ} (hH : 1000 ≤ H)
    (ox : ℝ) {w : Point} (hw : w ∈ (A.real ox H).set) {z : Point} (hz : z ∈ (r.real ox H).set) :
    z ∈ h.set ox H w := hpNN_sound (hpNN_of_r hh) hH ox hw hz

theorem hpNegr_sound {A r : LR} {h : HP} (hh : hpNegr A h r = true) {H : ℝ} (hH : 1000 ≤ H)
    (ox : ℝ) {w : Point} (hw : w ∈ (A.real ox H).set) {z : Point} (hz : z ∈ (r.real ox H).set) :
    z ∉ h.set ox H w := hpNeg_sound (hpNeg_of_r hh) hH ox hw hz

/-- Robust maximum (`none`: undecided). -/
def AH.rmax (a b : AH) : Option AH := if AH.le a b then some b else if AH.le b a then some a else none

/-- Robust minimum (`none`: undecided). -/
def AH.rmin (a b : AH) : Option AH := if AH.le a b then some a else if AH.le b a then some b else none

theorem AH.rmax_sound {a b m : AH} (h : AH.rmax a b = some m) {H : ℝ} (_hH : 1000 ≤ H) {y : ℝ}
    (ha : a.ev H ≤ y) (hb : b.ev H ≤ y) : m.ev H ≤ y := by
  unfold AH.rmax at h
  split_ifs at h <;> (cases h; assumption)

theorem AH.rmin_sound {a b m : AH} (h : AH.rmin a b = some m) {H : ℝ} (_hH : 1000 ≤ H) {y : ℝ}
    (ha : y ≤ a.ev H) (hb : y ≤ b.ev H) : y ≤ m.ev H := by
  unfold AH.rmin at h
  split_ifs at h <;> (cases h; assumption)

/-- The intersection of two rectangles: `some none` if robustly empty, `some (some X)` with `X`
containing it, `none` if undecided.  Rectangles strictly apart in `x` or in `y` are recognised first
(the cheap test that decides most pairs). -/
def LR.inter (r r' : LR) : Option (Option LR) :=
  if r.x1 < r'.x0 || r'.x1 < r.x0 || AH.lt r.y1 r'.y0 || AH.lt r'.y1 r.y0 then some none else
  match AH.rmax r.y0 r'.y0, AH.rmin r.y1 r'.y1 with
  | some y0, some y1 =>
    if min r.x1 r'.x1 < max r.x0 r'.x0 || AH.lt y1 y0 then some none
    else some (some ⟨max r.x0 r'.x0, min r.x1 r'.x1, y0, y1⟩)
  | _, _ => none

theorem LR.inter_empty {r r' : LR} (h : r.inter r' = some none) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {z : Point} (hz : z ∈ (r.real ox H).set) (hz' : z ∈ (r'.real ox H).set) : False := by
  unfold LR.inter at h
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  obtain ⟨hx0', hx1', hy0', hy1'⟩ := hz'
  simp only [LR.real] at hx0 hx1 hy0 hy1 hx0' hx1' hy0' hy1'
  split_ifs at h with ha
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at ha
    rcases ha with ((ha | ha) | ha) | ha
    · have : (r.x1 : ℝ) < r'.x0 := by exact_mod_cast ha
      linarith
    · have : (r'.x1 : ℝ) < r.x0 := by exact_mod_cast ha
      linarith
    · have := AH.lt_sound ha hH
      linarith
    · have := AH.lt_sound ha hH
      linarith
  split at h
  · rename_i y0 y1 e0 e1
    have hl := AH.rmax_sound e0 hH hy0 hy0'
    have hu := AH.rmin_sound e1 hH hy1 hy1'
    split_ifs at h with hc
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · have a1 : ((max r.x0 r'.x0 : ℚ) : ℝ) ≤ z.1 - ox := by
          rw [Rat.cast_max]; exact max_le (by linarith) (by linarith)
        have a2 : z.1 - ox ≤ ((min r.x1 r'.x1 : ℚ) : ℝ) := by
          rw [Rat.cast_min]; exact le_min (by linarith) (by linarith)
        have : ((min r.x1 r'.x1 : ℚ) : ℝ) < ((max r.x0 r'.x0 : ℚ) : ℝ) := by exact_mod_cast hc
        linarith
      · have := AH.lt_sound hc hH
        linarith
    · cases h
  · cases h

theorem LR.inter_sub {r r' X : LR} (h : r.inter r' = some (some X)) {H : ℝ} (hH : 1000 ≤ H)
    (ox : ℝ) {z : Point} (hz : z ∈ (r.real ox H).set) (hz' : z ∈ (r'.real ox H).set) :
    z ∈ (X.real ox H).set := by
  unfold LR.inter at h
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  obtain ⟨hx0', hx1', hy0', hy1'⟩ := hz'
  simp only [LR.real] at hx0 hx1 hy0 hy1 hx0' hx1' hy0' hy1'
  split_ifs at h with ha
  · cases h
  split at h
  · rename_i y0 y1 e0 e1
    split_ifs at h
    · simp at h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, ?_, AH.rmax_sound e0 hH hy0 hy0', AH.rmin_sound e1 hH hy1 hy1'⟩
    · show ox + ((max r.x0 r'.x0 : ℚ) : ℝ) ≤ z.1
      rw [Rat.cast_max]
      have := max_le (show (r.x0 : ℝ) ≤ z.1 - ox by linarith) (show (r'.x0 : ℝ) ≤ z.1 - ox by linarith)
      linarith
    · show z.1 ≤ ox + ((min r.x1 r'.x1 : ℚ) : ℝ)
      rw [Rat.cast_min]
      have := le_min (show z.1 - ox ≤ (r.x1 : ℝ) by linarith) (show z.1 - ox ≤ (r'.x1 : ℝ) by linarith)
      linarith
  · cases h

/-! ### Star-closed cones -/

theorem det_lerp_third (u v w z : Point) (s : ℝ) :
    det u v (lerp w z s) = (1 - s) * det u v w + s * det u v z := by
  simp only [det, lerp]; ring

theorem starFrom_hp {ox H : ℝ} {h : HP} {w : Point}
    (hw : det (h.1.pt ox H w) (h.2.pt ox H w) w ≤ 0) : StarFrom w (h.set ox H w) := by
  intro z hz s hs
  show 0 ≤ det _ _ _
  rw [det_lerp_third]
  have hz' : 0 ≤ det (h.1.pt ox H w) (h.2.pt ox H w) z := hz
  nlinarith

theorem starFrom_cone {ox H : ℝ} {K : List HP} {w : Point}
    (hw : ∀ h ∈ K, det (h.1.pt ox H w) (h.2.pt ox H w) w ≤ 0) : StarFrom w (cone ox H w K) :=
  fun z hz s hs h hh => starFrom_hp (hw h hh) z (hz h hh) s hs

theorem starFrom_cones {ox H : ℝ} {Ks : List (List HP)} {w : Point}
    (hw : ∀ K ∈ Ks, ∀ h ∈ K, det (h.1.pt ox H w) (h.2.pt ox H w) w ≤ 0) :
    StarFrom w (conesSet ox H w Ks) := by
  rintro z ⟨K, hK, hz⟩ s hs
  exact ⟨K, hK, starFrom_cone (hw K hK) z hz s hs⟩

theorem starFrom_optCone {ox H : ℝ} {o : Option (List HP)} {w : Point}
    (hw : ∀ K, o = some K → ∀ h ∈ K, det (h.1.pt ox H w) (h.2.pt ox H w) w ≤ 0) :
    StarFrom w (optCone ox H w o) := by
  cases o with
  | none => intro z hz; exact absurd hz (by simp [optCone])
  | some K => exact starFrom_cone (hw K rfl)

/-- The star condition of a half-plane: automatic when the line passes through the target;
otherwise robustly `det(u, v, a) ≤ 0` at the corner targets. -/
def starB (A : LR) (h : HP) : Bool :=
  match h with
  | (some u, some v) => A.corners.all fun a => AH.nn (-(hpv u v a).1, -(hpv u v a).2)
  | _ => true

theorem starB_sound {A : LR} {h : HP} (hh : starB A h = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {w : Point} (hw : w ∈ (A.real ox H).set) : det (h.1.pt ox H w) (h.2.pt ox H w) w ≤ 0 := by
  rcases h with ⟨e1, e2⟩
  cases e1 with
  | none => simp only [HE.pt, det]; nlinarith
  | some u =>
    cases e2 with
    | none => simp only [HE.pt, det]; nlinarith
    | some v =>
      simp only [starB, List.all_eq_true] at hh
      have hc := corners_mem (P := fun a => 0 ≤ -(hpv u v a).ev H) (fun a ha => by
        have := AH.nn_sound (hh a ha) hH
        simp only [AH.ev] at this ⊢; push_cast at this; linarith)
      obtain ⟨q00, q10, q01, q11⟩ := hc
      rw [← hpv_ev] at q00 q10 q01 q11
      obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
      simp only [LR.real] at hx0 hx1 hy0 hy1
      simp only [LP.real] at q00 q10 q01 q11
      have := affine_rect (c := 0) (fun x y => -det (u.real ox H) (v.real ox H) (x, y))
        (A := ((v.real ox H).2 - (u.real ox H).2)) (B := -((v.real ox H).1 - (u.real ox H).1))
        (G := -(((v.real ox H).2 - (u.real ox H).2) * (u.real ox H).1 -
          ((v.real ox H).1 - (u.real ox H).1) * (u.real ox H).2))
        (fun x y => by rw [det_affine]; ring) q00 q10 q01 q11 hx0 hx1 hy0 hy1
      simp only [HE.pt]
      have e : w = (w.1, w.2) := rfl
      rw [e]; linarith

theorem isClosed_rect_set (r : Rect) : IsClosed r.set := by
  have h1 : IsClosed {p : Point | r.1 ≤ p.1} := isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {p : Point | p.1 ≤ r.2.1} := isClosed_le continuous_fst continuous_const
  have h3 : IsClosed {p : Point | r.2.2.1 ≤ p.2} := isClosed_le continuous_const continuous_snd
  have h4 : IsClosed {p : Point | p.2 ≤ r.2.2.2} := isClosed_le continuous_snd continuous_const
  have : r.set = {p : Point | r.1 ≤ p.1} ∩ ({p | p.1 ≤ r.2.1} ∩ ({p | r.2.2.1 ≤ p.2} ∩
      {p | p.2 ≤ r.2.2.2})) := by
    ext p; simp [Rect.set]
  rw [this]; exact h1.inter (h2.inter (h3.inter h4))

/-! ### Open boxes and exposed faces -/

/-- An open box of a frame; `none`: that side is at infinity. -/
structure LBox where
  x0 : Option ℚ
  x1 : Option ℚ
  y0 : Option AH
  y1 : Option AH

/-- The real open box. -/
def LBox.set (ox H : ℝ) (U : LBox) : Set Point :=
  {z | (∀ a, U.x0 = some a → ox + a < z.1) ∧ (∀ a, U.x1 = some a → z.1 < ox + a) ∧
    (∀ a, U.y0 = some a → a.ev H < z.2) ∧ (∀ a, U.y1 = some a → z.2 < a.ev H)}

/-- Robustly inside the open box. -/
def LBox.memB (U : LBox) (w : LP) : Bool :=
  (match U.x0 with | none => true | some a => decide (a < w.1)) &&
  (match U.x1 with | none => true | some a => decide (w.1 < a)) &&
  (match U.y0 with | none => true | some a => AH.lt a w.2) &&
  (match U.y1 with | none => true | some a => AH.lt w.2 a)

theorem LBox.memB_sound {U : LBox} {w : LP} (h : U.memB w = true) {H : ℝ} (hH : 1000 ≤ H)
    (ox : ℝ) : w.real ox H ∈ U.set ox H := by
  simp only [LBox.memB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · rw [ha] at h1
    have : (a : ℝ) < w.1 := by exact_mod_cast of_decide_eq_true h1
    simp only [LP.real]; linarith
  · rw [ha] at h2
    have : (w.1 : ℝ) < a := by exact_mod_cast of_decide_eq_true h2
    simp only [LP.real]; linarith
  · rw [ha] at h3; exact AH.lt_sound h3 hH
  · rw [ha] at h4; exact AH.lt_sound h4 hH

/-- The sides of `r` on the boundary of `U` (degenerate rectangles), if `r` lies in the closed
box with every side either strictly inside or on the boundary; `none` otherwise. -/
def LR.faces (U : LBox) (r : LR) : Option (List LR) :=
  let l : Option (List LR) := match U.x0 with
    | none => some []
    | some a => if a < r.x0 then some [] else if a = r.x0 then some [⟨r.x0, r.x0, r.y0, r.y1⟩]
      else none
  let rt : Option (List LR) := match U.x1 with
    | none => some []
    | some a => if r.x1 < a then some [] else if r.x1 = a then some [⟨r.x1, r.x1, r.y0, r.y1⟩]
      else none
  let b : Option (List LR) := match U.y0 with
    | none => some []
    | some a => if AH.lt a r.y0 then some [] else if a = r.y0 then some [⟨r.x0, r.x1, r.y0, r.y0⟩]
      else none
  let t : Option (List LR) := match U.y1 with
    | none => some []
    | some a => if AH.lt r.y1 a then some [] else if r.y1 = a then some [⟨r.x0, r.x1, r.y1, r.y1⟩]
      else none
  match l, rt, b, t with
  | some l, some rt, some b, some t => some (l ++ rt ++ b ++ t)
  | _, _, _, _ => none

theorem LR.faces_sound {U : LBox} {r : LR} {fs : List LR} (h : r.faces U = some fs) {H : ℝ}
    (hH : 1000 ≤ H) (ox : ℝ) {z : Point} (hz : z ∈ (r.real ox H).set) (hzU : z ∉ U.set ox H) :
    ∃ e ∈ fs, z ∈ (e.real ox H).set := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  simp only [LR.real] at hx0 hx1 hy0 hy1
  unfold LR.faces at h
  simp only at h
  split at h
  · rename_i l rt b t hl hrt hb ht
    simp only [Option.some.injEq] at h
    subst h
    simp only [LBox.set, Set.mem_ofPred_eq, not_and_or, not_forall] at hzU
    rcases hzU with ⟨a, ha, hlt⟩ | ⟨a, ha, hlt⟩ | ⟨a, ha, hlt⟩ | ⟨a, ha, hlt⟩
    · rw [ha] at hl
      simp only at hl
      split_ifs at hl with c1 c2
      · exfalso; have : (a : ℝ) < r.x0 := by exact_mod_cast c1
        linarith
      · simp only [Option.some.injEq] at hl; subst hl
        refine ⟨⟨r.x0, r.x0, r.y0, r.y1⟩, by simp, ?_⟩
        refine ⟨by simp only [LR.real]; linarith, ?_, hy0, hy1⟩
        simp only [LR.real]; subst c2; linarith
    · rw [ha] at hrt
      simp only at hrt
      split_ifs at hrt with c1 c2
      · exfalso; have : (r.x1 : ℝ) < a := by exact_mod_cast c1
        linarith
      · simp only [Option.some.injEq] at hrt; subst hrt
        refine ⟨⟨r.x1, r.x1, r.y0, r.y1⟩, by simp, ?_⟩
        refine ⟨?_, by simp only [LR.real]; linarith, hy0, hy1⟩
        simp only [LR.real]; subst c2; linarith
    · rw [ha] at hb
      simp only at hb
      split_ifs at hb with c1 c2
      · exfalso; have := AH.lt_sound c1 hH
        linarith
      · simp only [Option.some.injEq] at hb; subst hb
        refine ⟨⟨r.x0, r.x1, r.y0, r.y0⟩, by simp, ?_⟩
        refine ⟨hx0, hx1, hy0, ?_⟩
        simp only [LR.real]; subst c2; linarith
    · rw [ha] at ht
      simp only at ht
      split_ifs at ht with c1 c2
      · exfalso; have := AH.lt_sound c1 hH
        linarith
      · simp only [Option.some.injEq] at ht; subst ht
        refine ⟨⟨r.x0, r.x1, r.y1, r.y1⟩, by simp, ?_⟩
        refine ⟨hx0, hx1, ?_, hy1⟩
        simp only [LR.real]; subst c2; linarith
  · cases h

/-- All corners of `A` robustly in the open box: then `A` lies in it. -/
theorem LBox.corners_sound {U : LBox} {A : LR} (h : A.corners.all U.memB = true) {H : ℝ}
    (hH : 1000 ≤ H) (ox : ℝ) {w : Point} (hw : w ∈ (A.real ox H).set) : w ∈ U.set ox H := by
  simp only [List.all_eq_true] at h
  obtain ⟨c00, c10, c01, c11⟩ := corners_mem (P := fun a => a.real ox H ∈ U.set ox H)
    (fun a ha => LBox.memB_sound (h a ha) hH ox)
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  simp only [LR.real] at hx0 hx1 hy0 hy1
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have := c00.1 a ha; simp only [LP.real] at this; linarith
  · have := c11.2.1 a ha; simp only [LP.real] at this; linarith
  · have := c00.2.2.1 a ha; simp only [LP.real] at this; linarith
  · have := c11.2.2.2 a ha; simp only [LP.real] at this; linarith

/-! ### Certificates -/

/-- A visibility certificate: the targets `A` (a rectangle, possibly degenerate) in the open box
`U[Ab]`; local rectangles, each with the index of the open box `U[k]` containing it and a union of
cones; the cone `C` of the other rectangles of the region, which lie outside all boxes. -/
structure LCert where
  A : LR
  Ab : ℕ
  cs : List (LR × ℕ × List (List HP))
  C : Option (List HP)
  U : List LBox

/-- The default box. -/
def LBox.default : LBox := ⟨none, none, none, none⟩

/-- Base condition: the targets robustly miss the rectangle, or one cone contains it. -/
def baseB (A : LR) (q : LR × ℕ × List (List HP)) : Bool :=
  decide (A.inter q.1 = some none) || q.2.2.any fun K => K.all fun h => hpNNr A h q.1

/-- Propagation from `q` to `q'`. -/
def propB (A : LR) (q q' : LR × ℕ × List (List HP)) : Bool :=
  q.2.2.isEmpty ||
  match q.1.inter q'.1 with
  | none => false
  | some none => true
  | some (some X) =>
    q.2.2.all fun K => K.any (fun h => hpNegr A h X) ||
      q'.2.2.any fun K' => K'.all fun h => decide (h ∈ K) || hpNNr A h X

/-- On an exposed face `e`: leaving to the rest (every cone misses `e` or its part on `e` lies in
`C`) and entering from the rest (`C ∩ e` lies in a cone, or is empty). -/
def faceB (A : LR) (C : Option (List HP)) (Ks : List (List HP)) (e : LR) : Bool :=
  match C with
  | none => Ks.all fun K => K.any fun h => hpNegr A h e
  | some hsC =>
    (Ks.all fun K => K.any (fun h => hpNegr A h e) ||
      hsC.all fun h => decide (h ∈ K) || hpNNr A h e) &&
    (hsC.any (fun h => hpNegr A h e) ||
      Ks.any fun K => K.all fun h => decide (h ∈ hsC) || hpNNr A h e)

/-- **The certificate check.** -/
def LCert.ok (c : LCert) : Bool :=
  (c.cs.flatMap (fun q => q.2.2.flatten) ++ c.C.getD []).all (starB c.A) &&
  c.A.corners.all (c.U.getD c.Ab LBox.default).memB && decide (c.Ab < c.U.length) &&
  c.cs.all (fun q => baseB c.A q && decide (q.2.1 < c.U.length) &&
    match q.1.faces (c.U.getD q.2.1 LBox.default) with
    | none => false
    | some fs => fs.all fun e => faceB c.A c.C q.2.2 e) &&
  c.cs.all (fun q => q.2.2.isEmpty || c.cs.all fun q' => propB c.A q q')

/-- **Soundness of the certificate check.**  For every target `w ∈ A`: if the segment from `w` to
`p` is covered by the local rectangles and closed sets `Rest` outside all boxes, then `p` lies in a
local rectangle and one of its cones, or outside all boxes and in `C`. -/
theorem LCert.sound {c : LCert} (hok : c.ok = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {w : Point} (hw : w ∈ (c.A.real ox H).set)
    {Rest : List (Set Point)} (hRc : ∀ r ∈ Rest, IsClosed r)
    (hRU : ∀ r ∈ Rest, ∀ z ∈ r, ∀ U ∈ c.U, z ∉ U.set ox H) {p : Point}
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∃ q ∈ c.cs, lerp w p t ∈ (q.1.real ox H).set) ∨ ∃ r ∈ Rest, lerp w p t ∈ r) :
    (∃ q ∈ c.cs, p ∈ (q.1.real ox H).set ∧ p ∈ conesSet ox H w q.2.2) ∨
      (p ∈ optCone ox H w c.C ∧ ∀ U ∈ c.U, p ∉ U.set ox H) := by
  simp only [LCert.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hstar, hwU⟩, hAb⟩, hloc⟩, hpr⟩ := hok
  have hUmem : ∀ k < c.U.length, c.U.getD k LBox.default ∈ c.U := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  have hwU' : w ∈ (c.U.getD c.Ab LBox.default).set ox H :=
    LBox.corners_sound (List.all_eq_true.2 hwU) hH ox hw
  have hst : ∀ h ∈ c.cs.flatMap (fun q => q.2.2.flatten) ++ c.C.getD [],
      det (h.1.pt ox H w) (h.2.pt ox H w) w ≤ 0 := fun h hh => starB_sound (hstar h hh) hH ox hw
  set L := c.cs.map (fun q => ((q.1.real ox H).set, conesSet ox H w q.2.2)) with hL
  have hmemL : ∀ x ∈ L, ∃ q ∈ c.cs, x = ((q.1.real ox H).set, conesSet ox H w q.2.2) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    exact ⟨q, hq, rfl⟩
  -- a local point outside its box lies on an exposed face
  have hface : ∀ q ∈ c.cs, ∀ r ∈ Rest, ∀ z ∈ (q.1.real ox H).set, z ∈ r →
      ∃ fs, q.1.faces (c.U.getD q.2.1 LBox.default) = some fs ∧
        (∀ e ∈ fs, faceB c.A c.C q.2.2 e = true) ∧ ∃ e ∈ fs, z ∈ (e.real ox H).set := by
    intro q hq r hr z hz hzr
    have hfc := (hloc q hq).2
    have hk := (hloc q hq).1.2
    cases hfa : q.1.faces (c.U.getD q.2.1 LBox.default) with
    | none => rw [hfa] at hfc; cases hfc
    | some fs =>
      rw [hfa] at hfc
      simp only [List.all_eq_true] at hfc
      refine ⟨fs, rfl, hfc, LR.faces_sound hfa hH ox hz (hRU r hr z hzr _ (hUmem _ hk))⟩
  have key := sees_mem_of_local (L := L) (Rest := Rest) (C := optCone ox H w c.C) (w := w) (p := p)
    (fun x hx => by obtain ⟨q, _, rfl⟩ := hmemL x hx; exact isClosed_rect_set _) hRc
    (fun x hx => by
      obtain ⟨q, hq, rfl⟩ := hmemL x hx
      exact starFrom_cones (fun K hK h hh => hst h (List.mem_append_left _
        (List.mem_flatMap.2 ⟨q, hq, List.mem_flatten.2 ⟨K, hK, hh⟩⟩))))
    (starFrom_optCone (fun K hK h hh => hst h (List.mem_append_right _ (by rw [hK]; exact hh))))
    (fun x hx hwx => by
      obtain ⟨q, hq, rfl⟩ := hmemL x hx
      have hb := (hloc q hq).1.1
      simp only [baseB, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
        List.all_eq_true] at hb
      rcases hb with hb | ⟨K, hK, hb⟩
      · exact (LR.inter_empty hb hH ox hw hwx).elim
      · intro z hz
        exact ⟨K, hK, fun h hh => hpNNr_sound (hb h hh) hH ox hw hz⟩)
    (fun r hr hwr => hRU r hr w hwr _ (hUmem _ hAb) hwU')
    (fun x hx x' hx' z hz hz' hzF _ => by
      obtain ⟨q, hq, rfl⟩ := hmemL x hx
      obtain ⟨q', hq', rfl⟩ := hmemL x' hx'
      obtain ⟨K, hK, hzK⟩ := hzF
      have hp : propB c.A q q' = true := by
        have := hpr q hq
        simp only [Bool.or_eq_true, List.isEmpty_iff, List.all_eq_true] at this
        rcases this with h | h
        · rw [h] at hK; simp at hK
        · exact h q' hq'
      unfold propB at hp
      simp only [Bool.or_eq_true, List.isEmpty_iff] at hp
      rcases hp with hp | hp
      · rw [hp] at hK; simp at hK
      split at hp
      · cases hp
      · rename_i hi; exact (LR.inter_empty hi hH ox hz hz').elim
      · rename_i X hi
        have hzX := LR.inter_sub hi hH ox hz hz'
        simp only [List.all_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at hp
        rcases hp K hK with ⟨h, hh, hneg⟩ | ⟨K', hK', hall⟩
        · exact absurd (hzK h hh) (hpNegr_sound hneg hH ox hw hzX)
        · refine ⟨K', hK', fun h hh => ?_⟩
          rcases hall h hh with hin | hnn
          · exact hzK h hin
          · exact hpNNr_sound hnn hH ox hw hzX)
    (fun x hx r hr z hz hzr hzF _ => by
      obtain ⟨q, hq, rfl⟩ := hmemL x hx
      obtain ⟨fs, -, hfc, e, he, hze⟩ := hface q hq r hr z hz hzr
      obtain ⟨K, hK, hzK⟩ := hzF
      have hf := hfc e he
      unfold faceB at hf
      cases hC : c.C with
      | none =>
        exfalso
        rw [hC] at hf
        simp only [List.all_eq_true, List.any_eq_true] at hf
        obtain ⟨h, hh, hneg⟩ := hf K hK
        exact hpNegr_sound hneg hH ox hw hze (hzK h hh)
      | some hsC =>
        rw [hC] at hf
        simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true,
          decide_eq_true_eq] at hf
        rcases hf.1 K hK with ⟨h, hh, hneg⟩ | hall
        · exact absurd (hzK h hh) (hpNegr_sound hneg hH ox hw hze)
        · intro h hh
          rcases hall h hh with hin | hnn
          · exact hzK h hin
          · exact hpNNr_sound hnn hH ox hw hze)
    (fun r hr x hx z hzr hz hzC _ => by
      obtain ⟨q, hq, rfl⟩ := hmemL x hx
      obtain ⟨fs, -, hfc, e, he, hze⟩ := hface q hq r hr z hz hzr
      have hf := hfc e he
      unfold faceB at hf
      cases hC : c.C with
      | none => rw [hC] at hzC; exact absurd hzC (by simp [optCone])
      | some hsC =>
        rw [hC] at hzC hf
        simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true,
          decide_eq_true_eq] at hf
        rcases hf.2 with ⟨h, hh, hneg⟩ | ⟨K, hK, hall⟩
        · exact absurd (hzC h hh) (hpNegr_sound hneg hH ox hw hze)
        · refine ⟨K, hK, fun h hh => ?_⟩
          rcases hall h hh with hin | hnn
          · exact hzC h hin
          · exact hpNNr_sound hnn hH ox hw hze)
    (fun t h0 h1 => by
      rcases hseg t h0 h1 with ⟨q, hq, hz⟩ | ⟨r, hr, hz⟩
      · exact Or.inl ⟨_, List.mem_map.2 ⟨q, hq, rfl⟩, hz⟩
      · exact Or.inr ⟨r, hr, hz⟩)
  rcases key with ⟨x, hx, hp1, hp2⟩ | ⟨r, hr, hp1, hp2⟩
  · obtain ⟨q, hq, rfl⟩ := hmemL x hx
    exact Or.inl ⟨q, hq, hp1, hp2⟩
  · exact Or.inr ⟨hp2, hRU r hr p hp1⟩

/-! ### Pieces in the open boxes -/

/-- Two boxes are robustly separated (their closures are disjoint). -/
def LBox.sepB (U V : LBox) : Bool :=
  (match U.x1, V.x0 with | some a, some b => decide (a ≤ b) | _, _ => false) ||
  (match V.x1, U.x0 with | some a, some b => decide (a ≤ b) | _, _ => false) ||
  (match U.y1, V.y0 with | some a, some b => AH.le a b | _, _ => false) ||
  (match V.y1, U.y0 with | some a, some b => AH.le a b | _, _ => false)

/-- The boxes of a list are pairwise separated. -/
def boxesSepB (Us : List LBox) : Bool :=
  (List.range Us.length).all fun i => (List.range Us.length).all fun j =>
    decide (i = j) || (Us.getD i LBox.default).sepB (Us.getD j LBox.default)

/-- A rectangle with computed faces lies in the closed box. -/
theorem LR.faces_closed {U : LBox} {r : LR} {fs : List LR} (h : r.faces U = some fs) {H : ℝ}
    (hH : 1000 ≤ H) (ox : ℝ) {z : Point} (hz : z ∈ (r.real ox H).set) :
    (∀ a, U.x0 = some a → ox + a ≤ z.1) ∧ (∀ a, U.x1 = some a → z.1 ≤ ox + a) ∧
    (∀ a, U.y0 = some a → a.ev H ≤ z.2) ∧ (∀ a, U.y1 = some a → z.2 ≤ a.ev H) := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  simp only [LR.real] at hx0 hx1 hy0 hy1
  unfold LR.faces at h
  simp only at h
  split at h
  · rename_i l rt b t hl hrt hb ht
    refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
    · rw [ha] at hl; simp only at hl
      split_ifs at hl with c1 c2
      · have : (a : ℝ) < r.x0 := by exact_mod_cast c1
        linarith
      · subst c2; linarith
    · rw [ha] at hrt; simp only at hrt
      split_ifs at hrt with c1 c2
      · have : (r.x1 : ℝ) < a := by exact_mod_cast c1
        linarith
      · subst c2; linarith
    · rw [ha] at hb; simp only at hb
      split_ifs at hb with c1 c2
      · have := AH.lt_sound c1 hH; linarith
      · subst c2; linarith
    · rw [ha] at ht; simp only at ht
      split_ifs at ht with c1 c2
      · have := AH.lt_sound c1 hH; linarith
      · subst c2; linarith
  · cases h

theorem LBox.sepB_sound {U V : LBox} (h : U.sepB V = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {z : Point} (hz : (∀ a, U.x0 = some a → ox + a ≤ z.1) ∧ (∀ a, U.x1 = some a → z.1 ≤ ox + a) ∧
      (∀ a, U.y0 = some a → a.ev H ≤ z.2) ∧ (∀ a, U.y1 = some a → z.2 ≤ a.ev H)) :
    z ∉ V.set ox H := by
  rintro ⟨hv0, hv1, hv2, hv3⟩
  obtain ⟨hu0, hu1, hu2, hu3⟩ := hz
  unfold LBox.sepB at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · split at h
    · rename_i a b ha hb
      have := of_decide_eq_true h
      have h1 := hu1 a ha; have h2 := hv0 b hb
      have : (a : ℝ) ≤ b := by exact_mod_cast this
      linarith
    · cases h
  · split at h
    · rename_i a b ha hb
      have := of_decide_eq_true h
      have h1 := hv1 a ha; have h2 := hu0 b hb
      have : (a : ℝ) ≤ b := by exact_mod_cast this
      linarith
    · cases h
  · split at h
    · rename_i a b ha hb
      have := AH.le_sound h hH
      have h1 := hu3 a ha; have h2 := hv2 b hb
      linarith
    · cases h
  · split at h
    · rename_i a b ha hb
      have := AH.le_sound h hH
      have h1 := hv3 a ha; have h2 := hu2 b hb
      linarith
    · cases h

/-- **Soundness, box form.**  With pairwise separated boxes: `p` lies in a local piece inside the
open box of its rectangle, or in `C` outside all boxes. -/
theorem LCert.sound_box {c : LCert} (hok : c.ok = true) (hsep : boxesSepB c.U = true) {H : ℝ}
    (hH : 1000 ≤ H) (ox : ℝ) {w : Point} (hw : w ∈ (c.A.real ox H).set)
    {Rest : List (Set Point)} (hRc : ∀ r ∈ Rest, IsClosed r)
    (hRU : ∀ r ∈ Rest, ∀ z ∈ r, ∀ U ∈ c.U, z ∉ U.set ox H) {p : Point}
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∃ q ∈ c.cs, lerp w p t ∈ (q.1.real ox H).set) ∨ ∃ r ∈ Rest, lerp w p t ∈ r) :
    (∃ q ∈ c.cs, p ∈ (q.1.real ox H).set ∧ p ∈ conesSet ox H w q.2.2 ∧
      p ∈ (c.U.getD q.2.1 LBox.default).set ox H) ∨
      (p ∈ optCone ox H w c.C ∧ ∀ U ∈ c.U, p ∉ U.set ox H) := by
  rcases LCert.sound hok hH ox hw hRc hRU hseg with ⟨q, hq, hp1, hp2⟩ | h
  · by_cases hin : p ∈ (c.U.getD q.2.1 LBox.default).set ox H
    · exact Or.inl ⟨q, hq, hp1, hp2, hin⟩
    right
    have hok' := hok
    simp only [LCert.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok'
    have hloc := hok'.1.2 q hq
    have hk := hloc.1.2
    have hfc := hloc.2
    cases hfa : q.1.faces (c.U.getD q.2.1 LBox.default) with
    | none => rw [hfa] at hfc; cases hfc
    | some fs =>
      rw [hfa] at hfc
      simp only [List.all_eq_true] at hfc
      obtain ⟨e, he, hze⟩ := LR.faces_sound hfa hH ox hp1 hin
      have hf := hfc e he
      obtain ⟨K, hK, hpK⟩ := hp2
      refine ⟨?_, fun U hU hpU => ?_⟩
      · unfold faceB at hf
        cases hC : c.C with
        | none =>
          rw [hC] at hf
          simp only [List.all_eq_true, List.any_eq_true] at hf
          obtain ⟨h, hh, hneg⟩ := hf K hK
          exact absurd (hpK h hh) (hpNegr_sound hneg hH ox hw hze)
        | some hsC =>
          rw [hC] at hf
          simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true,
            decide_eq_true_eq] at hf
          rcases hf.1 K hK with ⟨h, hh, hneg⟩ | hall
          · exact absurd (hpK h hh) (hpNegr_sound hneg hH ox hw hze)
          · intro h hh
            rcases hall h hh with hin' | hnn
            · exact hpK h hin'
            · exact hpNNr_sound hnn hH ox hw hze
      · obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem hU
        by_cases hkk : k' = q.2.1
        · subst hkk
          rw [List.getD_eq_getElem _ _ hk'] at hin
          exact hin hpU
        · have hs := hsep
          simp only [boxesSepB, List.all_eq_true, List.mem_range, Bool.or_eq_true,
            decide_eq_true_eq] at hs
          rcases hs q.2.1 hk k' hk' with h | h
          · exact hkk h.symm
          · have := LBox.sepB_sound h hH ox (LR.faces_closed hfa hH ox hp1)
            rw [List.getD_eq_getElem _ _ hk'] at this
            exact this hpU
  · exact Or.inr h

/-! ### Disjointness of pieces -/

/-- Two cones are disjoint on the rectangle `X`: a half-plane of one of them is strictly negative
on it, possibly after splitting it in halves (in `x`) at most `d` times. -/
def sepB (A1 : LR) (K1 : List HP) (A2 : LR) (K2 : List HP) : ℕ → LR → Bool
  | 0, X => K1.any (fun h => hpNegr A1 h X) || K2.any (fun h => hpNegr A2 h X)
  | d + 1, X => K1.any (fun h => hpNegr A1 h X) || K2.any (fun h => hpNegr A2 h X) ||
      (decide (X.x0 < X.x1) &&
        sepB A1 K1 A2 K2 d ⟨X.x0, (X.x0 + X.x1) / 2, X.y0, X.y1⟩ &&
        sepB A1 K1 A2 K2 d ⟨(X.x0 + X.x1) / 2, X.x1, X.y0, X.y1⟩)

theorem sepB_sound {A1 A2 : LR} {K1 K2 : List HP} {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {w1 w2 : Point} (hw1 : w1 ∈ (A1.real ox H).set) (hw2 : w2 ∈ (A2.real ox H).set) :
    ∀ (d : ℕ) (X : LR), sepB A1 K1 A2 K2 d X = true → ∀ z ∈ (X.real ox H).set,
      z ∈ cone ox H w1 K1 → z ∉ cone ox H w2 K2
  | 0, X, h, z, hz, h1, h2 => by
    simp only [sepB, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨h, hh, hn⟩ | ⟨h, hh, hn⟩
    · exact hpNegr_sound hn hH ox hw1 hz (h1 h hh)
    · exact hpNegr_sound hn hH ox hw2 hz (h2 h hh)
  | d + 1, X, h, z, hz, h1, h2 => by
    simp only [sepB, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    rcases h with (⟨h, hh, hn⟩ | ⟨h, hh, hn⟩) | ⟨⟨-, hlo⟩, hhi⟩
    · exact hpNegr_sound hn hH ox hw1 hz (h1 h hh)
    · exact hpNegr_sound hn hH ox hw2 hz (h2 h hh)
    · obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
      simp only [LR.real] at hx0 hx1 hy0 hy1
      rcases le_total z.1 (ox + (((X.x0 + X.x1) / 2 : ℚ) : ℝ)) with hc | hc
      · exact sepB_sound hH ox hw1 hw2 d _ hlo z ⟨hx0, hc, hy0, hy1⟩ h1 h2
      · exact sepB_sound hH ox hw1 hw2 d _ hhi z ⟨hc, hx1, hy0, hy1⟩ h1 h2

/-- The pieces of two certificates (same frame) are disjoint. -/
def disjB (c1 c2 : LCert) : Bool :=
  c1.cs.all fun q1 => q1.2.2.isEmpty || c2.cs.all fun q2 => q2.2.2.isEmpty ||
    match q1.1.inter q2.1 with
    | none => false
    | some none => true
    | some (some X) => q1.2.2.all fun K1 => q2.2.2.all fun K2 => sepB c1.A K1 c2.A K2 6 X

theorem disjB_sound {c1 c2 : LCert} (h : disjB c1 c2 = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {w1 w2 : Point} (hw1 : w1 ∈ (c1.A.real ox H).set) (hw2 : w2 ∈ (c2.A.real ox H).set) {p : Point}
    {q1 : LR × ℕ × List (List HP)} (hq1 : q1 ∈ c1.cs) (hp1 : p ∈ (q1.1.real ox H).set)
    (hc1 : p ∈ conesSet ox H w1 q1.2.2)
    {q2 : LR × ℕ × List (List HP)} (hq2 : q2 ∈ c2.cs) (hp2 : p ∈ (q2.1.real ox H).set)
    (hc2 : p ∈ conesSet ox H w2 q2.2.2) : False := by
  simp only [disjB, List.all_eq_true, Bool.or_eq_true, List.isEmpty_iff] at h
  obtain ⟨K1, hK1, hpK1⟩ := hc1
  obtain ⟨K2, hK2, hpK2⟩ := hc2
  have h' : (match q1.1.inter q2.1 with
    | none => false
    | some none => true
    | some (some X) => q1.2.2.all fun K1 => q2.2.2.all fun K2 => sepB c1.A K1 c2.A K2 6 X) = true := by
    rcases h q1 hq1 with h1 | h1
    · rw [h1] at hK1; simp at hK1
    rcases h1 q2 hq2 with h2 | h2
    · rw [h2] at hK2; simp at hK2
    exact h2
  split at h'
  · cases h'
  · rename_i hi; exact LR.inter_empty hi hH ox hp1 hp2
  · rename_i X hi
    simp only [List.all_eq_true] at h'
    exact sepB_sound hH ox hw1 hw2 6 X (h' K1 hK1 K2 hK2) p (LR.inter_sub hi hH ox hp1 hp2) hpK1 hpK2

end

end ArtGallery.Orthogonal.Hard
