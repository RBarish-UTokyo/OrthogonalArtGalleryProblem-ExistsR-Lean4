module

public import ArtGallery.Orthogonal.Hard.ZoneSound

/-!
# The region of a comb of zones

Abstract form of the region decomposition of the orthogonal polygon.  A *half comb* is a line
`y = y₀` with features hanging below it, each surrounded by a *zone* (a finite family of
rectangles inside a box `[L, R] × (−∞, T]`), and *gap rectangles* `[R_i, L_{i+1}] × [y₀, T]`
filling the strip between consecutive zones.  From the properties of the zones (`FZone.Good`)
we derive (`halfComb_*`):

* every frontier point of every piece lies on a given set `B` (the boundary of the polygon), is
  interior to the union, or lies on the strip top `y = T`;
* near every point of the strip top, the lower quadrants are covered;
* the comb chain is covered, and every piece lies below `y = T`.

Pieces are rectangles `[x₀, x₁] × [y₀, y₁]`, given by their four coordinates.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational Set Metric

/-! ### Rectangles as quadruples -/

/-- A rectangle `(x₀, x₁, y₀, y₁)`. -/
abbrev Rect := ℝ × ℝ × ℝ × ℝ

/-- The point set of a rectangle. -/
def Rect.set (r : Rect) : Set Point := {p | r.1 ≤ p.1 ∧ p.1 ≤ r.2.1 ∧ r.2.2.1 ≤ p.2 ∧ p.2 ≤ r.2.2.2}

/-- The rectangle as a polygon. -/
def Rect.poly (r : Rect) : Polygon := rectP r.1 r.2.1 r.2.2.1 r.2.2.2

/-- A non-degenerate rectangle. -/
def Rect.Pos (r : Rect) : Prop := r.1 < r.2.1 ∧ r.2.2.1 < r.2.2.2

/-- The union of a list of rectangles. -/
def RU (rs : List Rect) : Set Point := {p | ∃ r ∈ rs, p ∈ r.set}

theorem Rect.piece_poly {r : Rect} (h : r.Pos) : piece r.poly = r.set := piece_rectP h.1 h.2

theorem RU_mono {rs rs' : List Rect} (h : ∀ r ∈ rs, r ∈ rs') : RU rs ⊆ RU rs' := by
  rintro p ⟨r, hr, hp⟩; exact ⟨r, h r hr, hp⟩

theorem RU_mono' {rs : List Rect} {r : Rect} (hr : r ∈ rs) : r.set ⊆ RU rs :=
  fun _ hp => ⟨r, hr, hp⟩

theorem mem_RU {rs : List Rect} {r : Rect} (hr : r ∈ rs) {p : Point} (hp : p ∈ r.set) :
    p ∈ RU rs := ⟨r, hr, hp⟩

/-! ### Covered quadrants -/

/-- The quadrant `(sx, sy)` of `y` lies, near `y`, in `U`. -/
def QuadIn (U : Set Point) (y : Point) (sx sy : Bool) : Prop :=
  ∃ δ > 0, ∀ z, dist z y < δ → z ∈ quadrant y sx sy → z ∈ U

theorem QuadIn.mono {U V : Set Point} {y : Point} {sx sy : Bool} (h : QuadIn U y sx sy)
    (hUV : U ⊆ V) : QuadIn V y sx sy := by
  obtain ⟨δ, hδ, h⟩ := h
  exact ⟨δ, hδ, fun z hz hq => hUV (h z hz hq)⟩

theorem interior_of_quadIn {U : Set Point} {y : Point} (h : ∀ sx sy, QuadIn U y sx sy) :
    y ∈ interior U :=
  mem_interior_of_quadrants h

/-- A rectangle covers a quadrant of `y` when `y` lies in it, strictly inside in the quadrant's
directions. -/
theorem quadIn_rect {r : Rect} {y : Point} {sx sy : Bool}
    (hx : if sx then r.1 ≤ y.1 ∧ y.1 < r.2.1 else r.1 < y.1 ∧ y.1 ≤ r.2.1)
    (hy : if sy then r.2.2.1 ≤ y.2 ∧ y.2 < r.2.2.2 else r.2.2.1 < y.2 ∧ y.2 ≤ r.2.2.2) :
    QuadIn r.set y sx sy := by
  obtain ⟨δ, hδ, h⟩ := quadrant_of_rect hx hy
  exact ⟨δ, hδ, fun z hz hq => h z hz hq⟩

theorem RU_cons (r : Rect) (rs : List Rect) : RU (r :: rs) = r.set ∪ RU rs := by
  ext p; simp [RU]

theorem RU_append (rs rs' : List Rect) : RU (rs ++ rs') = RU rs ∪ RU rs' := by
  ext p; simp only [RU, List.mem_append, mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨r, hr | hr, hp⟩
    · exact Or.inl ⟨r, hr, hp⟩
    · exact Or.inr ⟨r, hr, hp⟩
  · rintro (⟨r, hr, hp⟩ | ⟨r, hr, hp⟩)
    · exact ⟨r, Or.inl hr, hp⟩
    · exact ⟨r, Or.inr hr, hp⟩

theorem interior_of_lr {U : Set Point} {y : Point} (h1 : QuadIn U y false false)
    (h2 : QuadIn U y false true) (h3 : QuadIn U y true false) (h4 : QuadIn U y true true) :
    y ∈ interior U :=
  interior_of_quadIn (fun sx sy => by cases sx <;> cases sy <;> assumption)

/-! ### Sides -/

/-- `y` lies on a side of the rectangle (seen as a polygon). -/
def RSide (r : Rect) (y : Point) : Prop := ∃ j < 4, y ∈ r.poly.edge j

theorem RSide.mem {r : Rect} (h : r.Pos) {y : Point} (hy : RSide r y) :
    y ∈ r.set ∧ (y.1 = r.1 ∨ y.1 = r.2.1 ∨ y.2 = r.2.2.1 ∨ y.2 = r.2.2.2) := by
  obtain ⟨x₀, x₁, y₀, y₁⟩ := r
  obtain ⟨hx, hy'⟩ := h
  obtain ⟨j, hj, hyj⟩ := hy
  simp only [Rect.poly] at hyj
  rw [rectP_edge hj] at hyj
  simp only [Rect.set, mem_ofPred_eq]
  interval_cases j <;> norm_num at hyj
  · have a1 := seg_fst_ge hyj; have a2 := seg_fst_le hyj
    have a3 := seg_snd_ge hyj; have a4 := seg_snd_le hyj
    simp only [min_eq_left hx.le, max_eq_right hx.le, min_self, max_self] at a1 a2 a3 a4
    exact ⟨⟨a1, a2, by linarith, by linarith⟩, Or.inr (Or.inr (Or.inl (by linarith)))⟩
  · have a1 := seg_fst_ge hyj; have a2 := seg_fst_le hyj
    have a3 := seg_snd_ge hyj; have a4 := seg_snd_le hyj
    simp only [min_eq_left hy'.le, max_eq_right hy'.le, min_self, max_self] at a1 a2 a3 a4
    exact ⟨⟨by linarith, by linarith, a3, a4⟩, Or.inr (Or.inl (by linarith))⟩
  · have a1 := seg_fst_ge hyj; have a2 := seg_fst_le hyj
    have a3 := seg_snd_ge hyj; have a4 := seg_snd_le hyj
    simp only [min_eq_right hx.le, max_eq_left hx.le, min_self, max_self] at a1 a2 a3 a4
    exact ⟨⟨a1, a2, by linarith, by linarith⟩, Or.inr (Or.inr (Or.inr (by linarith)))⟩
  · have a1 := seg_fst_ge hyj; have a2 := seg_fst_le hyj
    have a3 := seg_snd_ge hyj; have a4 := seg_snd_le hyj
    simp only [min_eq_right hy'.le, max_eq_left hy'.le, min_self, max_self] at a1 a2 a3 a4
    exact ⟨⟨by linarith, by linarith, a3, a4⟩, Or.inl (by linarith)⟩

/-! ### Zones of a half comb -/

/-- A zone of a half comb (floor form): a feature `f` hanging from the line `y = y₀`, and
rectangles `rs` in the box `[L, R] × (−∞, T]`. -/
structure FZone where
  /-- The feature. -/
  f : List Point
  /-- The rectangles. -/
  rs : List Rect
  /-- Left side of the box. -/
  L : ℝ
  /-- Right side of the box. -/
  R : ℝ

/-- The properties of a zone (floor form, line `y₀`, strip top `T`). -/
structure FZone.Good (y₀ T : ℝ) (Z : FZone) : Prop where
  len : 2 ≤ Z.f.length
  fy : (fstPt Z.f).2 = y₀
  ly : (lstPt Z.f).2 = y₀
  Lf : Z.L < (fstPt Z.f).1
  fl : (fstPt Z.f).1 < (lstPt Z.f).1
  lR : (lstPt Z.f).1 < Z.R
  pos : ∀ r ∈ Z.rs, r.Pos
  box : ∀ r ∈ Z.rs, ∀ p ∈ r.set, Z.L ≤ p.1 ∧ p.1 ≤ Z.R ∧ p.2 ≤ T
  chain : chainSet Z.f ⊆ RU Z.rs
  floorL : ∀ x, Z.L ≤ x → x ≤ (fstPt Z.f).1 → ((x, y₀) : Point) ∈ RU Z.rs
  floorR : ∀ x, (lstPt Z.f).1 ≤ x → x ≤ Z.R → ((x, y₀) : Point) ∈ RU Z.rs
  side : ∀ r ∈ Z.rs, ∀ y, RSide r y → y ∈ chainSet Z.f ∨
    (y.2 = y₀ ∧ Z.L ≤ y.1 ∧ y.1 ≤ (fstPt Z.f).1) ∨ (y.2 = y₀ ∧ (lstPt Z.f).1 ≤ y.1 ∧ y.1 ≤ Z.R) ∨
    y ∈ interior (RU Z.rs) ∨ (y.2 = T ∧ Z.L ≤ y.1 ∧ y.1 ≤ Z.R) ∨
    ((y.1 = Z.L ∨ y.1 = Z.R) ∧ y₀ ≤ y.2 ∧ y.2 ≤ T)
  tiles : ∀ x, Z.L ≤ x → x ≤ Z.R → (x < Z.R → QuadIn (RU Z.rs) (x, T) true false) ∧
    (Z.L < x → QuadIn (RU Z.rs) (x, T) false false)
  left : ∀ t, y₀ < t → t ≤ T → QuadIn (RU Z.rs) (Z.L, t) true false ∧
    (t < T → QuadIn (RU Z.rs) (Z.L, t) true true)
  right : ∀ t, y₀ < t → t ≤ T → QuadIn (RU Z.rs) (Z.R, t) false false ∧
    (t < T → QuadIn (RU Z.rs) (Z.R, t) false true)

/-- The zones are ordered from `s` to `e`, with gaps between their boxes. -/
def ZOrd : ℝ → List FZone → ℝ → Prop
  | s, [], e => s < e
  | s, Z :: zs, e => s < Z.L ∧ ZOrd Z.R zs e

theorem ZOrd.mono {s s' e : ℝ} {zs : List FZone} (h : ZOrd s zs e) (hs : s' ≤ s) : ZOrd s' zs e := by
  cases zs with
  | nil => exact lt_of_le_of_lt hs h
  | cons Z zs => exact ⟨lt_of_le_of_lt hs h.1, h.2⟩

section Half

variable {y₀ T : ℝ}

theorem ZOrd.bounds {e : ℝ} : ∀ {zs : List FZone} {s : ℝ}, (∀ Z ∈ zs, Z.Good y₀ T) →
    ZOrd s zs e → s < e ∧ ∀ Z ∈ zs, s < Z.L ∧ Z.R < e
  | [], s, _, h => ⟨h, by simp⟩
  | Z :: zs, s, hG, h => by
    obtain ⟨h1, h2⟩ := h
    have hZ := hG Z (by simp)
    have ih := ZOrd.bounds (fun Z' hZ' => hG Z' (by simp [hZ'])) h2
    have hLR : Z.L < Z.R := by linarith [hZ.Lf, hZ.fl, hZ.lR]
    refine ⟨by linarith [ih.1], fun Z' hZ' => ?_⟩
    rcases List.mem_cons.1 hZ' with rfl | hZ'
    · exact ⟨h1, ih.1⟩
    · have := ih.2 Z' hZ'
      have hZ'G := hG Z' (by simp [hZ'])
      exact ⟨by linarith, this.2⟩

/-- The rectangles of a half comb from `s` to `e`: gap rectangles `[R_i, L_{i+1}] × [y₀, T]` and
the rectangles of the zones. -/
def hcRects (y₀ T : ℝ) : ℝ → List FZone → ℝ → List Rect
  | s, [], e => [(s, e, y₀, T)]
  | s, Z :: zs, e => (s, Z.L, y₀, T) :: (Z.rs ++ hcRects y₀ T Z.R zs e)

/-- The points of the line `y = y₀` between `s` and `e` outside the open spans of the features. -/
def LineOut (y₀ s e : ℝ) (zs : List FZone) : Set Point :=
  {p | p.2 = y₀ ∧ s ≤ p.1 ∧ p.1 ≤ e ∧ ∀ Z ∈ zs, p.1 ≤ (fstPt Z.f).1 ∨ (lstPt Z.f).1 ≤ p.1}

/-- The points of the features. -/
def FeatSet (zs : List FZone) : Set Point := {p | ∃ Z ∈ zs, p ∈ chainSet Z.f}

theorem hc_pos (hT : y₀ < T) {e : ℝ} : ∀ {zs : List FZone} {s : ℝ}, (∀ Z ∈ zs, Z.Good y₀ T) →
    ZOrd s zs e → ∀ r ∈ hcRects y₀ T s zs e, r.Pos
  | [], s, _, h, r, hr => by
    simp only [hcRects, List.mem_singleton] at hr; subst hr; exact ⟨h, hT⟩
  | Z :: zs, s, hG, h, r, hr => by
    simp only [hcRects, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · exact ⟨h.1, hT⟩
    · exact (hG Z (by simp)).pos r hr
    · exact hc_pos hT (fun Z' hZ' => hG Z' (by simp [hZ'])) h.2 r hr

theorem hc_box {e : ℝ} : ∀ {zs : List FZone} {s : ℝ}, (∀ Z ∈ zs, Z.Good y₀ T) →
    ZOrd s zs e → ∀ r ∈ hcRects y₀ T s zs e, ∀ p ∈ r.set, s ≤ p.1 ∧ p.1 ≤ e ∧ p.2 ≤ T
  | [], s, _, _, r, hr, p, hp => by
    simp only [hcRects, List.mem_singleton] at hr; subst hr
    exact ⟨hp.1, hp.2.1, hp.2.2.2⟩
  | Z :: zs, s, hG, h, r, hr, p, hp => by
    have hb := ZOrd.bounds hG h
    have hZ := hb.2 Z (by simp)
    have hZG := hG Z (by simp)
    simp only [hcRects, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · exact ⟨hp.1, by linarith [hp.2.1, hZG.Lf, hZG.fl, hZG.lR], hp.2.2.2⟩
    · have := hZG.box r hr p hp
      exact ⟨by linarith, by linarith, this.2.2⟩
    · have := hc_box (fun Z' hZ' => hG Z' (by simp [hZ'])) h.2 r hr p hp
      exact ⟨by linarith [hZG.Lf, hZG.fl, hZG.lR], this.2.1, this.2.2⟩

/-- The left end of a half comb: the first gap rectangle. -/
theorem hc_left {e : ℝ} {zs : List FZone} {s : ℝ} (h : ZOrd s zs e) :
    ∀ t, y₀ < t → t ≤ T → QuadIn (RU (hcRects y₀ T s zs e)) (s, t) true false ∧
      (t < T → QuadIn (RU (hcRects y₀ T s zs e)) (s, t) true true) := by
  intro t h1 h2
  obtain ⟨n, hn, hmem⟩ : ∃ n, s < n ∧ (s, n, y₀, T) ∈ hcRects y₀ T s zs e := by
    cases zs with
    | nil => exact ⟨e, h, by simp [hcRects]⟩
    | cons Z zs => exact ⟨Z.L, h.1, by simp [hcRects]⟩
  refine ⟨(quadIn_rect (r := (s, n, y₀, T)) ?_ ?_).mono (RU_mono' hmem),
    fun h3 => (quadIn_rect (r := (s, n, y₀, T)) ?_ ?_).mono (RU_mono' hmem)⟩
  · simp only [↓reduceIte]; exact ⟨le_rfl, hn⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨h1, h2⟩
  · simp only [↓reduceIte]; exact ⟨le_rfl, hn⟩
  · simp only [↓reduceIte]; exact ⟨h1.le, h3⟩

/-- The right end of a half comb: the last gap rectangle. -/
theorem hc_right {e : ℝ} : ∀ {zs : List FZone} {s : ℝ}, ZOrd s zs e →
    ∀ t, y₀ < t → t ≤ T → QuadIn (RU (hcRects y₀ T s zs e)) (e, t) false false ∧
      (t < T → QuadIn (RU (hcRects y₀ T s zs e)) (e, t) false true)
  | [], s, h, t, h1, h2 => by
    have hmem : (s, e, y₀, T) ∈ hcRects y₀ T s [] e := by simp [hcRects]
    refine ⟨(quadIn_rect (r := (s, e, y₀, T)) ?_ ?_).mono (RU_mono' hmem),
      fun h3 => (quadIn_rect (r := (s, e, y₀, T)) ?_ ?_).mono (RU_mono' hmem)⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨h, le_rfl⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨h1, h2⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨h, le_rfl⟩
    · simp only [↓reduceIte]; exact ⟨h1.le, h3⟩
  | Z :: zs, s, h, t, h1, h2 => by
    have ih := hc_right h.2 t h1 h2
    have hsub : RU (hcRects y₀ T Z.R zs e) ⊆ RU (hcRects y₀ T s (Z :: zs) e) :=
      RU_mono (fun r hr => by simp [hcRects, hr])
    exact ⟨ih.1.mono hsub, fun h3 => (ih.2 h3).mono hsub⟩

/-- The strip top of a half comb is tiled. -/
theorem hc_tiles {e : ℝ} (hT : y₀ < T) : ∀ {zs : List FZone} {s : ℝ}, (∀ Z ∈ zs, Z.Good y₀ T) →
    ZOrd s zs e → ∀ x, s ≤ x → x ≤ e →
      (x < e → QuadIn (RU (hcRects y₀ T s zs e)) (x, T) true false) ∧
      (s < x → QuadIn (RU (hcRects y₀ T s zs e)) (x, T) false false)
  | [], s, _, h, x, h1, h2 => by
    have hmem : (s, e, y₀, T) ∈ hcRects y₀ T s [] e := by simp [hcRects]
    refine ⟨fun h3 => (quadIn_rect (r := (s, e, y₀, T)) ?_ ?_).mono (RU_mono' hmem),
      fun h3 => (quadIn_rect (r := (s, e, y₀, T)) ?_ ?_).mono (RU_mono' hmem)⟩
    · simp only [↓reduceIte]; exact ⟨h1, h3⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hT, le_rfl⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨h3, h2⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hT, le_rfl⟩
  | Z :: zs, s, hG, h, x, h1, h2 => by
    have hZG := hG Z (by simp)
    have hb := ZOrd.bounds hG h
    have hZ := hb.2 Z (by simp)
    have hgap : (s, Z.L, y₀, T) ∈ hcRects y₀ T s (Z :: zs) e := by simp [hcRects]
    have hsubZ : RU Z.rs ⊆ RU (hcRects y₀ T s (Z :: zs) e) :=
      RU_mono (fun r hr => by simp [hcRects, hr])
    have hsubT : RU (hcRects y₀ T Z.R zs e) ⊆ RU (hcRects y₀ T s (Z :: zs) e) :=
      RU_mono (fun r hr => by simp [hcRects, hr])
    have hG' : ∀ Z' ∈ zs, Z'.Good y₀ T := fun Z' hZ' => hG Z' (by simp [hZ'])
    have hLR : Z.L < Z.R := by linarith [hZG.Lf, hZG.fl, hZG.lR]
    by_cases hxL : x ≤ Z.L
    · refine ⟨fun h3 => ?_, fun h3 => ?_⟩
      · rcases lt_or_eq_of_le hxL with hx | hx
        · refine (quadIn_rect (r := (s, Z.L, y₀, T)) ?_ ?_).mono (RU_mono' hgap)
          · simp only [↓reduceIte]; exact ⟨h1, hx⟩
          · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hT, le_rfl⟩
        · subst hx; exact ((hZG.tiles _ le_rfl hLR.le).1 hLR).mono hsubZ
      · refine (quadIn_rect (r := (s, Z.L, y₀, T)) ?_ ?_).mono (RU_mono' hgap)
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨h3, hxL⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hT, le_rfl⟩
    push Not at hxL
    by_cases hxR : x ≤ Z.R
    · refine ⟨fun h3 => ?_, fun _ => ((hZG.tiles x hxL.le hxR).2 hxL).mono hsubZ⟩
      rcases lt_or_eq_of_le hxR with hx | hx
      · exact ((hZG.tiles x hxL.le hxR).1 hx).mono hsubZ
      · subst hx; exact ((hc_tiles hT hG' h.2 _ le_rfl h2).1 h3).mono hsubT
    · push Not at hxR
      have ih := hc_tiles hT hG' h.2 x hxR.le h2
      exact ⟨fun h3 => (ih.1 h3).mono hsubT, fun _ => (ih.2 hxR).mono hsubT⟩

/-- The line outside the spans and the features are covered. -/
theorem hc_cover {e : ℝ} (hT : y₀ < T) : ∀ {zs : List FZone} {s : ℝ}, (∀ Z ∈ zs, Z.Good y₀ T) →
    ZOrd s zs e → LineOut y₀ s e zs ∪ FeatSet zs ⊆ RU (hcRects y₀ T s zs e)
  | [], s, _, _, p, hp => by
    rcases hp with ⟨h1, h2, h3, -⟩ | ⟨Z, hZ, -⟩
    · exact ⟨(s, e, y₀, T), by simp [hcRects], h2, h3, h1.ge, by rw [h1]; exact hT.le⟩
    · simp at hZ
  | Z :: zs, s, hG, h, p, hp => by
    have hZG := hG Z (by simp)
    have hb := ZOrd.bounds hG h
    have hZ := hb.2 Z (by simp)
    have hsubZ : RU Z.rs ⊆ RU (hcRects y₀ T s (Z :: zs) e) :=
      RU_mono (fun r hr => by simp [hcRects, hr])
    have hsubT : RU (hcRects y₀ T Z.R zs e) ⊆ RU (hcRects y₀ T s (Z :: zs) e) :=
      RU_mono (fun r hr => by simp [hcRects, hr])
    have hG' : ∀ Z' ∈ zs, Z'.Good y₀ T := fun Z' hZ' => hG Z' (by simp [hZ'])
    rcases hp with ⟨h1, h2, h3, h4⟩ | ⟨Z', hZ', hpZ'⟩
    · have hp' : p = (p.1, y₀) := Prod.ext rfl h1
      by_cases hxL : p.1 ≤ Z.L
      · exact ⟨(s, Z.L, y₀, T), by simp [hcRects], h2, hxL, h1.ge, by rw [h1]; exact hT.le⟩
      push Not at hxL
      by_cases hxR : p.1 ≤ Z.R
      · rcases h4 Z (by simp) with h5 | h5
        · rw [hp']; exact hsubZ (hZG.floorL _ hxL.le h5)
        · rw [hp']; exact hsubZ (hZG.floorR _ h5 hxR)
      · push Not at hxR
        exact hsubT (hc_cover hT hG' h.2 (Or.inl ⟨h1, hxR.le, h3,
          fun Z' hZ' => h4 Z' (by simp [hZ'])⟩))
    · rcases List.mem_cons.1 hZ' with rfl | hZ'
      · exact hsubZ (hZG.chain hpZ')
      · exact hsubT (hc_cover hT hG' h.2 (Or.inr ⟨Z', hZ', hpZ'⟩))

/-- The conclusion of the side lemma of a half comb. -/
def HCConcl (y₀ T s e : ℝ) (zs : List FZone) (U : Set Point) (y : Point) : Prop :=
  y ∈ LineOut y₀ s e zs ∪ FeatSet zs ∨ y ∈ interior U ∨ (y.2 = T ∧ s ≤ y.1 ∧ y.1 ≤ e) ∨
    ((y.1 = s ∨ y.1 = e) ∧ y₀ ≤ y.2 ∧ y.2 ≤ T)

/-- **Half comb: sides.** -/
theorem hc_side {e : ℝ} (hT : y₀ < T) : ∀ {zs : List FZone} {s : ℝ}, (∀ Z ∈ zs, Z.Good y₀ T) →
    ZOrd s zs e → ∀ r ∈ hcRects y₀ T s zs e, ∀ y, RSide r y →
      HCConcl y₀ T s e zs (RU (hcRects y₀ T s zs e)) y
  | [], s, _, h, r, hr, y, hy => by
    simp only [hcRects, List.mem_singleton] at hr; subst hr
    obtain ⟨⟨a1, a2, a3, a4⟩, hs⟩ := RSide.mem (r := (s, e, y₀, T)) ⟨(show s < e from h), hT⟩ hy
    simp only at a1 a2 a3 a4 hs
    rcases hs with hs | hs | hs | hs
    · exact Or.inr (Or.inr (Or.inr ⟨Or.inl hs, a3, a4⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Or.inr hs, a3, a4⟩))
    · exact Or.inl (Or.inl ⟨hs, a1, a2, by simp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hs, a1, a2⟩))
  | Z :: zs, s, hG, h, r, hr, y, hy => by
    set U := RU (hcRects y₀ T s (Z :: zs) e)
    have hZG := hG Z (by simp)
    have hb := ZOrd.bounds hG h
    have hZ := hb.2 Z (by simp)
    have hgap : (s, Z.L, y₀, T) ∈ hcRects y₀ T s (Z :: zs) e := by simp [hcRects]
    have hsubZ : RU Z.rs ⊆ U := RU_mono (fun r hr => by simp [hcRects, hr])
    have hsubT : RU (hcRects y₀ T Z.R zs e) ⊆ U := RU_mono (fun r hr => by simp [hcRects, hr])
    have hG' : ∀ Z' ∈ zs, Z'.Good y₀ T := fun Z' hZ' => hG Z' (by simp [hZ'])
    have hbT := ZOrd.bounds hG' h.2
    have hLR : Z.L < Z.R := by linarith [hZG.Lf, hZG.fl, hZG.lR]
    -- later features start after `R`
    have hlater : ∀ Z' ∈ zs, Z.R < (fstPt Z'.f).1 := fun Z' hZ' => by
      have := hbT.2 Z' hZ'; have := (hG' Z' hZ').Lf; linarith
    -- the point `(L, t)`
    have atL : ∀ y : Point, y.1 = Z.L → y₀ ≤ y.2 → y.2 ≤ T →
        HCConcl y₀ T s e (Z :: zs) U y := by
      intro y hy1 hy2 hy3
      have hy' : y = (Z.L, y.2) := Prod.ext hy1 rfl
      rcases eq_or_lt_of_le hy2 with hy2 | hy2
      · refine Or.inl (Or.inl ⟨hy2.symm, by linarith, by linarith, fun Z' hZ' => ?_⟩)
        rcases List.mem_cons.1 hZ' with rfl | hZ'
        · exact Or.inl (by linarith [hZG.Lf])
        · exact Or.inl (by linarith [hlater Z' hZ'])
      rcases eq_or_lt_of_le hy3 with hy3 | hy3
      · exact Or.inr (Or.inr (Or.inl ⟨hy3, by linarith, by linarith⟩))
      refine Or.inr (Or.inl ?_)
      rw [hy']
      have hl := hZG.left y.2 hy2 hy3.le
      refine interior_of_lr ?_ ?_ (hl.1.mono hsubZ) ((hl.2 hy3).mono hsubZ)
      · refine (quadIn_rect (r := (s, Z.L, y₀, T)) ?_ ?_).mono (RU_mono' hgap)
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨h.1, le_rfl⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hy2, hy3.le⟩
      · refine (quadIn_rect (r := (s, Z.L, y₀, T)) ?_ ?_).mono (RU_mono' hgap)
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨h.1, le_rfl⟩
        · simp only [↓reduceIte]; exact ⟨hy2.le, hy3⟩
    -- the point `(R, t)`
    have atR : ∀ y : Point, y.1 = Z.R → y₀ ≤ y.2 → y.2 ≤ T →
        HCConcl y₀ T s e (Z :: zs) U y := by
      intro y hy1 hy2 hy3
      have hy' : y = (Z.R, y.2) := Prod.ext hy1 rfl
      rcases eq_or_lt_of_le hy2 with hy2 | hy2
      · refine Or.inl (Or.inl ⟨hy2.symm, by linarith, by linarith, fun Z' hZ' => ?_⟩)
        rcases List.mem_cons.1 hZ' with rfl | hZ'
        · exact Or.inr (by linarith [hZG.lR])
        · exact Or.inl (by linarith [hlater Z' hZ'])
      rcases eq_or_lt_of_le hy3 with hy3 | hy3
      · exact Or.inr (Or.inr (Or.inl ⟨hy3, by linarith, by linarith⟩))
      refine Or.inr (Or.inl ?_)
      rw [hy']
      have hr := hZG.right y.2 hy2 hy3.le
      have hl := hc_left (y₀ := y₀) (T := T) h.2 y.2 hy2 hy3.le
      exact interior_of_lr (hr.1.mono hsubZ) ((hr.2 hy3).mono hsubZ) (hl.1.mono hsubT)
        ((hl.2 hy3).mono hsubT)
    simp only [hcRects, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · -- the gap rectangle
      obtain ⟨⟨a1, a2, a3, a4⟩, hs⟩ := RSide.mem ⟨h.1, hT⟩ hy
      simp only at a1 a2 a3 a4 hs
      rcases hs with hs | hs | hs | hs
      · exact Or.inr (Or.inr (Or.inr ⟨Or.inl hs, a3, a4⟩))
      · exact atL y hs a3 a4
      · refine Or.inl (Or.inl ⟨hs, a1, by linarith, fun Z' hZ' => ?_⟩)
        rcases List.mem_cons.1 hZ' with rfl | hZ'
        · exact Or.inl (by linarith [hZG.Lf])
        · exact Or.inl (by linarith [hlater Z' hZ'])
      · exact Or.inr (Or.inr (Or.inl ⟨hs, a1, by linarith⟩))
    · -- a rectangle of the zone
      rcases hZG.side r hr y hy with h1 | h1 | h1 | h1 | h1 | h1
      · exact Or.inl (Or.inr ⟨Z, by simp, h1⟩)
      · obtain ⟨h1, h2, h3⟩ := h1
        refine Or.inl (Or.inl ⟨h1, by linarith, by linarith [hZG.fl, hZG.lR], fun Z' hZ' => ?_⟩)
        rcases List.mem_cons.1 hZ' with rfl | hZ'
        · exact Or.inl h3
        · exact Or.inl (by linarith [hlater Z' hZ', hZG.fl, hZG.lR])
      · obtain ⟨h1, h2, h3⟩ := h1
        refine Or.inl (Or.inl ⟨h1, by linarith [hZG.Lf, hZG.fl], by linarith, fun Z' hZ' => ?_⟩)
        rcases List.mem_cons.1 hZ' with rfl | hZ'
        · exact Or.inr h2
        · exact Or.inl (by linarith [hlater Z' hZ'])
      · exact Or.inr (Or.inl (interior_mono hsubZ h1))
      · obtain ⟨h1, h2, h3⟩ := h1
        exact Or.inr (Or.inr (Or.inl ⟨h1, by linarith, by linarith⟩))
      · obtain ⟨h1 | h1, h2, h3⟩ := h1
        · exact atL y h1 h2 h3
        · exact atR y h1 h2 h3
    · -- a rectangle of the rest
      rcases hc_side hT hG' h.2 r hr y hy with h1 | h1 | h1 | h1
      · rcases h1 with ⟨h1, h2, h3, h4⟩ | ⟨Z', hZ', h5⟩
        · refine Or.inl (Or.inl ⟨h1, by linarith, h3, fun Z' hZ' => ?_⟩)
          rcases List.mem_cons.1 hZ' with rfl | hZ'
          · exact Or.inr (by linarith [hZG.lR])
          · exact h4 Z' hZ'
        · exact Or.inl (Or.inr ⟨Z', by simp [hZ'], h5⟩)
      · exact Or.inr (Or.inl (interior_mono hsubT h1))
      · obtain ⟨h1, h2, h3⟩ := h1
        exact Or.inr (Or.inr (Or.inl ⟨h1, by linarith, h3⟩))
      · obtain ⟨h1 | h1, h2, h3⟩ := h1
        · exact atR y h1 h2 h3
        · exact Or.inr (Or.inr (Or.inr ⟨Or.inr h1, h2, h3⟩))

/-! ### The comb chain -/

/-- **The comb chain** lies on the line outside the spans, or on the features. -/
theorem comb_sub {e : ℝ} : ∀ {zs : List FZone} {s : ℝ}, (∀ Z ∈ zs, Z.Good y₀ T) →
    ZOrd s zs e → chainSet ((s, y₀) :: (zs.map FZone.f).flatten ++ [(e, y₀)]) ⊆
      LineOut y₀ s e zs ∪ FeatSet zs
  | [], s, _, h => by
    simp only [List.map_nil, List.flatten_nil, List.nil_append, List.cons_append,
      chainSet_cons_cons, chainSet_single, union_empty]
    intro p hp
    have := segment_subset_hline h.le hp
    exact Or.inl ⟨this.1, this.2.1, this.2.2, by simp⟩
  | Z :: zs, s, hG, h => by
    have hZG := hG Z (by simp)
    have hb := ZOrd.bounds hG h
    have hZ := hb.2 Z (by simp)
    have hG' : ∀ Z' ∈ zs, Z'.Good y₀ T := fun Z' hZ' => hG Z' (by simp [hZ'])
    have hbT := ZOrd.bounds hG' h.2
    have hlater : ∀ Z' ∈ zs, Z.R < (fstPt Z'.f).1 := fun Z' hZ' => by
      have := hbT.2 Z' hZ'; have := (hG' Z' hZ').Lf; linarith
    set a := fstPt Z.f
    set q := lstPt Z.f
    have hq : q = (q.1, y₀) := Prod.ext rfl hZG.ly
    set f' := Z.f.tail.dropLast
    have hfdec : Z.f = a :: (f' ++ [q]) := decomp_of_two_le hZG.len
    have ih := comb_sub (s := q.1) hG' (h.2.mono (by linarith [hZG.lR]))
    have he : (s, y₀) :: ((Z :: zs).map FZone.f).flatten ++ [(e, y₀)] =
        ((s, y₀) :: (a :: f')) ++ q :: ((zs.map FZone.f).flatten ++ [(e, y₀)]) := by
      simp only [List.map_cons, List.flatten_cons]
      conv_lhs => rw [hfdec]
      simp
    have hS1 : chainSet ((s, y₀) :: (a :: f') ++ [q]) =
        ArtGallery.segment (s, y₀) a ∪ chainSet Z.f := by
      have e' : (s, y₀) :: (a :: f') ++ [q] = (s, y₀) :: a :: (f' ++ [q]) := rfl
      rw [e', chainSet_cons_cons, ← hfdec]
    rw [he, chainSet_append_cons, hS1]
    refine union_subset (union_subset ?_ ?_) ?_
    · intro p hp
      have := segment_subset_hline' (y₀ := y₀) (a := (s, y₀)) rfl hZG.fy (by linarith [hZG.Lf]) hp
      refine Or.inl ⟨this.1, this.2.1, by linarith [this.2.2, hZG.fl, hZG.lR], fun Z' hZ' => ?_⟩
      rcases List.mem_cons.1 hZ' with rfl | hZ'
      · exact Or.inl this.2.2
      · exact Or.inl (by linarith [this.2.2, hlater Z' hZ', hZG.fl, hZG.lR])
    · intro p hp; exact Or.inr ⟨Z, by simp, hp⟩
    · intro p hp
      rw [hq] at hp
      rcases ih (by simpa using hp) with ⟨h1, h2, h3, h4⟩ | ⟨Z', hZ', h5⟩
      · refine Or.inl ⟨h1, by linarith [hZG.Lf, hZG.fl], h3, fun Z' hZ' => ?_⟩
        rcases List.mem_cons.1 hZ' with rfl | hZ'
        · exact Or.inr h2
        · exact h4 Z' hZ'
      · exact Or.inr ⟨Z', by simp [hZ'], h5⟩

/-- **The comb chain** contains the line outside the spans and the features. -/
theorem comb_sup {e : ℝ} : ∀ {zs : List FZone} {s : ℝ}, (∀ Z ∈ zs, Z.Good y₀ T) →
    ZOrd s zs e → LineOut y₀ s e zs ∪ FeatSet zs ⊆
      chainSet ((s, y₀) :: (zs.map FZone.f).flatten ++ [(e, y₀)])
  | [], s, _, h => by
    simp only [List.map_nil, List.flatten_nil, List.nil_append, List.cons_append,
      chainSet_cons_cons, chainSet_single, union_empty]
    rintro p (⟨h1, h2, h3, -⟩ | ⟨Z, hZ, -⟩)
    · have : p = (p.1, y₀) := Prod.ext rfl h1
      rw [this]
      exact mem_segment_horiz (by rw [min_eq_left h.le]; exact h2)
        (by rw [max_eq_right h.le]; exact h3)
    · simp at hZ
  | Z :: zs, s, hG, h => by
    have hZG := hG Z (by simp)
    have hG' : ∀ Z' ∈ zs, Z'.Good y₀ T := fun Z' hZ' => hG Z' (by simp [hZ'])
    set a := fstPt Z.f
    set q := lstPt Z.f
    have hq : q = (q.1, y₀) := Prod.ext rfl hZG.ly
    have ha : a = (a.1, y₀) := Prod.ext rfl hZG.fy
    set f' := Z.f.tail.dropLast
    have hfdec : Z.f = a :: (f' ++ [q]) := decomp_of_two_le hZG.len
    have ih := comb_sup (s := q.1) hG' (h.2.mono (by linarith [hZG.lR]))
    have he : (s, y₀) :: ((Z :: zs).map FZone.f).flatten ++ [(e, y₀)] =
        ((s, y₀) :: (a :: f')) ++ q :: ((zs.map FZone.f).flatten ++ [(e, y₀)]) := by
      simp only [List.map_cons, List.flatten_cons]
      conv_lhs => rw [hfdec]
      simp
    have hS1 : chainSet ((s, y₀) :: (a :: f') ++ [q]) =
        ArtGallery.segment (s, y₀) a ∪ chainSet Z.f := by
      have e' : (s, y₀) :: (a :: f') ++ [q] = (s, y₀) :: a :: (f' ++ [q]) := rfl
      rw [e', chainSet_cons_cons, ← hfdec]
    have htail : chainSet ((q.1, y₀) :: (zs.map FZone.f).flatten ++ [(e, y₀)]) ⊆
        chainSet ((s, y₀) :: ((Z :: zs).map FZone.f).flatten ++ [(e, y₀)]) := by
      intro p hp
      rw [he, chainSet_append_cons ((s, y₀) :: a :: f')]
      rw [← hq] at hp
      exact mem_union_right _ hp
    have hhead : ArtGallery.segment (s, y₀) a ∪ chainSet Z.f ⊆
        chainSet ((s, y₀) :: ((Z :: zs).map FZone.f).flatten ++ [(e, y₀)]) := by
      intro p hp
      rw [he, chainSet_append_cons ((s, y₀) :: a :: f'), hS1]; exact mem_union_left _ hp
    rintro p (⟨h1, h2, h3, h4⟩ | ⟨Z', hZ', h5⟩)
    · rcases h4 Z (by simp) with h5 | h5
      · have : p = (p.1, y₀) := Prod.ext rfl h1
        refine hhead (Or.inl ?_)
        rw [this, ha]
        exact mem_segment_horiz (by rw [min_eq_left (by linarith [hZG.Lf, h.1])]; exact h2)
          (by rw [max_eq_right (by linarith [hZG.Lf, h.1])]; exact h5)
      · exact htail (ih (Or.inl ⟨h1, h5, h3, fun Z' hZ' => h4 Z' (by simp [hZ'])⟩))
    · rcases List.mem_cons.1 hZ' with rfl | hZ'
      · exact hhead (Or.inr h5)
      · exact htail (ih (Or.inr ⟨Z', hZ', h5⟩))

end Half

/-! ### Reflection through the origin -/

/-- The rectangle reflected through the origin. -/
def Rect.neg (r : Rect) : Rect := (-r.2.1, -r.1, -r.2.2.2, -r.2.2.1)

theorem Rect.mem_neg {r : Rect} {p : Point} : p ∈ r.neg.set ↔ -p ∈ r.set := by
  simp only [Rect.set, Rect.neg, mem_ofPred_eq, Prod.fst_neg, Prod.snd_neg]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem Rect.Pos.neg {r : Rect} (h : r.Pos) : r.neg.Pos :=
  ⟨by simp only [Rect.neg]; linarith [h.1], by simp only [Rect.neg]; linarith [h.2]⟩

theorem RU_map_neg (rs : List Rect) : RU (rs.map Rect.neg) = {p | -p ∈ RU rs} := by
  ext p
  simp only [RU, List.mem_map, mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, hp⟩; exact ⟨r, hr, Rect.mem_neg.1 hp⟩
  · rintro ⟨r, hr, hp⟩; exact ⟨r.neg, ⟨r, hr, rfl⟩, Rect.mem_neg.2 hp⟩

theorem RSide.neg {r : Rect} {y : Point} (h : RSide r.neg y) : RSide r (-y) := by
  obtain ⟨x₀, x₁, y₀, y₁⟩ := r
  obtain ⟨j, hj, hy⟩ := h
  simp only [Rect.poly, Rect.neg] at hy
  rw [rectP_edge hj] at hy
  have key : ∀ a b : Point, y ∈ ArtGallery.segment (-a) (-b) → -y ∈ ArtGallery.segment a b :=
    fun a b h => mem_segment_neg.1 h
  interval_cases j <;> norm_num at hy
  · exact ⟨2, by norm_num, by
      simp only [Rect.poly]; rw [rectP_edge (by norm_num)]; norm_num
      exact key (x₁, y₁) (x₀, y₁) (by simpa using hy)⟩
  · exact ⟨3, by norm_num, by
      simp only [Rect.poly]; rw [rectP_edge (by norm_num)]; norm_num
      exact key (x₀, y₁) (x₀, y₀) (by simpa using hy)⟩
  · exact ⟨0, by norm_num, by
      simp only [Rect.poly]; rw [rectP_edge (by norm_num)]; norm_num
      exact key (x₀, y₀) (x₁, y₀) (by simpa using hy)⟩
  · exact ⟨1, by norm_num, by
      simp only [Rect.poly]; rw [rectP_edge (by norm_num)]; norm_num
      exact key (x₁, y₀) (x₁, y₁) (by simpa using hy)⟩

theorem QuadIn.mem {U : Set Point} {y : Point} {sx sy : Bool} (h : QuadIn U y sx sy) : y ∈ U := by
  obtain ⟨δ, hδ, h⟩ := h
  refine h y (by rw [dist_self]; exact hδ) ?_
  simp only [quadrant, mem_ofPred_eq]
  cases sx <;> cases sy <;> simp

theorem QuadIn.neg {U : Set Point} {a b : ℝ} {sx sy : Bool} (h : QuadIn U (-a, -b) sx sy) :
    QuadIn {p | -p ∈ U} (a, b) (!sx) (!sy) := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, fun z hz hq => h (-z) ?_ ?_⟩
  · have e : ((-a, -b) : Point) = -((a, b) : Point) := rfl
    rw [e, dist_neg_neg]; exact hz
  · simp only [quadrant, mem_ofPred_eq, Prod.fst_neg, Prod.snd_neg] at hq ⊢
    cases sx <;> cases sy <;> simp at hq ⊢ <;> constructor <;> linarith [hq.1, hq.2]

theorem interior_neg {U : Set Point} {p : Point} (h : -p ∈ interior U) :
    p ∈ interior {q : Point | -q ∈ U} := by
  have := (Homeomorph.neg Point).preimage_interior U
  have e : {q : Point | -q ∈ U} = (Homeomorph.neg Point) ⁻¹' U := rfl
  rw [e, ← this]; exact h

/-! ### Unions of rectangles as unions of pieces -/

theorem pieceUnion_rects {rs : List Rect} (h : ∀ r ∈ rs, r.Pos) :
    pieceUnion {K | K ∈ rs.map Rect.poly} = RU rs := by
  ext p
  rw [mem_pieceUnion]
  constructor
  · rintro ⟨K, hK, hp⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hK
    rw [Rect.piece_poly (h r hr)] at hp
    exact ⟨r, hr, hp⟩
  · rintro ⟨r, hr, hp⟩
    exact ⟨r.poly, List.mem_map.2 ⟨r, hr, rfl⟩, by rw [Rect.piece_poly (h r hr)]; exact hp⟩

theorem isBoundedSet_RU : ∀ rs : List Rect, IsBoundedSet (RU rs)
  | [] => ⟨0, fun p ⟨r, hr, _⟩ => by simp at hr⟩
  | r :: rs => by
    obtain ⟨M, hM⟩ := isBoundedSet_RU rs
    refine ⟨max M (|r.1| + |r.2.1| + |r.2.2.1| + |r.2.2.2|), fun p hp => ?_⟩
    rw [RU_cons] at hp
    rcases hp with ⟨h1, h2, h3, h4⟩ | hp
    · set B := |r.1| + |r.2.1| + |r.2.2.1| + |r.2.2.2|
      have b1 := neg_abs_le r.1; have b2 := le_abs_self r.2.1
      have b3 := neg_abs_le r.2.2.1; have b4 := le_abs_self r.2.2.2
      have c1 := abs_nonneg r.1; have c2 := abs_nonneg r.2.1
      have c3 := abs_nonneg r.2.2.1; have c4 := abs_nonneg r.2.2.2
      have d1 := le_abs_self r.1; have d2 := neg_abs_le r.2.1
      have d3 := le_abs_self r.2.2.1; have d4 := neg_abs_le r.2.2.2
      have a1 : |p.1| ≤ B := abs_le.2 ⟨by linarith, by linarith⟩
      have a2 : |p.2| ≤ B := abs_le.2 ⟨by linarith, by linarith⟩
      exact ⟨a1.trans (le_max_right _ _), a2.trans (le_max_right _ _)⟩
    · have := hM p hp
      exact ⟨this.1.trans (le_max_left _ _), this.2.trans (le_max_left _ _)⟩

/-! ### The closing edge -/

theorem closing_subset_boundary (a z : Point) (l : List Point) :
    ArtGallery.segment z a ⊆ (Polygon.mk (a :: l ++ [z])).boundary := by
  intro y hy
  refine ⟨l.length + 1, by simp [Polygon.n], ?_⟩
  have hn : (Polygon.mk (a :: l ++ [z])).n = l.length + 2 := by simp [Polygon.n]
  unfold Polygon.edge Polygon.vtx
  rw [hn, Nat.mod_self]
  simpa [List.getD_eq_getElem?_getD, List.getElem?_append_right] using hy

/-! ### The region of a rectangle with two half combs -/

/-- The rectangles of the region: the hall `[x_lo, x_hi] × [T_f, T_c]`, the floor half comb,
and the ceiling half comb (given reflected through the origin). -/
def combRects (xlo xhi ylo yhi Tf Tc : ℝ) (zf zc : List FZone) : List Rect :=
  (xlo, xhi, Tf, Tc) :: (hcRects ylo Tf xlo zf xhi ++
    (hcRects (-yhi) (-Tc) (-xhi) zc (-xlo)).map Rect.neg)

/-- **The region of a rectangle with two half combs.**  For the polygon of
`simple_of_combsD`, with zones around the floor features (line `y_lo`, strip top `T_f`) and
zones around the reflected ceiling features (line `−y_hi`, strip top `−T_c`), the region is the
union of the rectangles `combRects`. -/
theorem filled_combs {xlo xhi ylo yhi Tf Tc : ℝ} (hx : xlo < xhi) (h1 : ylo < Tf) (h2 : Tf < Tc)
    (h3 : Tc < yhi) (F C : List (List Point)) (zf zc : List FZone)
    (hzf : zf.map FZone.f = F) (hGf : ∀ Z ∈ zf, Z.Good ylo Tf) (hOf : ZOrd xlo zf xhi)
    (hzc : zc.map FZone.f = C.map (List.map (fun q => -q)))
    (hGc : ∀ Z ∈ zc, Z.Good (-yhi) (-Tc)) (hOc : ZOrd (-xhi) zc (-xlo))
    (hP : (Polygon.mk ([(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten ++
      [(xlo, yhi)])).Simple) :
    (Polygon.mk ([(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten ++
      [(xlo, yhi)])).filled = RU (combRects xlo xhi ylo yhi Tf Tc zf zc) := by
  set P := Polygon.mk ([(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten ++
      [(xlo, yhi)]) with hPdef
  set hall : Rect := (xlo, xhi, Tf, Tc) with hhall
  set Uf := RU (hcRects ylo Tf xlo zf xhi) with hUf
  set Uc := RU (hcRects (-yhi) (-Tc) (-xhi) zc (-xlo)) with hUc
  set U := RU (combRects xlo xhi ylo yhi Tf Tc zf zc) with hU
  have hUeq : U = hall.set ∪ (Uf ∪ {p | -p ∈ Uc}) := by
    rw [hU, combRects, RU_cons, RU_append, RU_map_neg]
  have hsubh : hall.set ⊆ U := by rw [hUeq]; exact subset_union_left
  have hsubf : Uf ⊆ U := by rw [hUeq]; exact subset_union_left.trans subset_union_right
  have hsubc : {p | -p ∈ Uc} ⊆ U := by
    rw [hUeq]; exact subset_union_right.trans subset_union_right
  have hTc : -yhi < -Tc := by linarith
  have hbf := ZOrd.bounds hGf hOf
  have hbc := ZOrd.bounds hGc hOc
  -- the rectangles
  have hpos : ∀ r ∈ combRects xlo xhi ylo yhi Tf Tc zf zc, r.Pos := by
    intro r hr
    simp only [combRects, List.mem_cons, List.mem_append, List.mem_map] at hr
    rcases hr with rfl | hr | ⟨r', hr', rfl⟩
    · exact ⟨hx, h2⟩
    · exact hc_pos h1 hGf hOf r hr
    · exact (hc_pos hTc hGc hOc r' hr').neg
  -- the floor comb
  set FC := chainSet ((xlo, ylo) :: F.flatten ++ [(xhi, ylo)]) with hFC
  have hFCsub : FC ⊆ LineOut ylo xlo xhi zf ∪ FeatSet zf := by
    rw [hFC, ← hzf]; exact comb_sub hGf hOf
  have hFCsup : LineOut ylo xlo xhi zf ∪ FeatSet zf ⊆ FC := by
    rw [hFC, ← hzf]; exact comb_sup hGf hOf
  have hFCbd : FC ⊆ P.boundary := by
    apply chainSet_subset_boundary
    refine List.IsPrefix.isInfix ⟨(xhi, yhi) :: C.flatten ++ [(xlo, yhi)], by simp⟩
  -- the ceiling comb
  set CC := chainSet ((xhi, yhi) :: C.flatten ++ [(xlo, yhi)]) with hCC
  have hCCneg : ∀ p, p ∈ CC ↔
      -p ∈ chainSet ((-xhi, -yhi) :: (zc.map FZone.f).flatten ++ [(-xlo, -yhi)]) := by
    intro p
    have e : (-xhi, -yhi) :: (zc.map FZone.f).flatten ++ [(-xlo, -yhi)] =
        ((xhi, yhi) :: C.flatten ++ [(xlo, yhi)]).map (fun q => -q) := by
      rw [hzc]; simp [List.map_flatten]
    rw [e, chainSet_map_neg, neg_neg]
  have hCCbd : CC ⊆ P.boundary := by
    apply chainSet_subset_boundary
    refine List.IsSuffix.isInfix ⟨[(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo)], by simp⟩
  -- the walls
  have hRW : ArtGallery.segment (xhi, ylo) (xhi, yhi) ⊆ P.boundary := by
    have := chainSet_subset_boundary (L := [(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++
      C.flatten ++ [(xlo, yhi)]) (M := [(xhi, ylo), (xhi, yhi)])
      ⟨[(xlo, ylo)] ++ F.flatten, C.flatten ++ [(xlo, yhi)], by simp⟩
    simp only [chainSet_cons_cons, chainSet_single, union_empty] at this
    exact this
  have hLW : ArtGallery.segment (xlo, yhi) (xlo, ylo) ⊆ P.boundary := by
    have e : [(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten ++ [(xlo, yhi)] =
        (xlo, ylo) :: (F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten) ++ [(xlo, yhi)] := by
      simp
    rw [hPdef, e]; exact closing_subset_boundary _ _ _
  have wallR : ∀ t, ylo ≤ t → t ≤ yhi → ((xhi, t) : Point) ∈ P.boundary := fun t a b =>
    hRW (mem_segment_vert (by rw [min_eq_left (by linarith)]; exact a)
      (by rw [max_eq_right (by linarith)]; exact b))
  have wallL : ∀ t, ylo ≤ t → t ≤ yhi → ((xlo, t) : Point) ∈ P.boundary := fun t a b =>
    hLW (mem_segment_vert (by rw [min_eq_right (by linarith)]; exact a)
      (by rw [max_eq_left (by linarith)]; exact b))
  -- the boundary
  have hbdec : P.boundary ⊆ FC ∪ ArtGallery.segment (xhi, ylo) (xhi, yhi) ∪ CC ∪
      ArtGallery.segment (xlo, yhi) (xlo, ylo) := by
    have hne : [(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten ++
        [(xlo, yhi)] ≠ [] := by simp
    intro p hp
    have hb := boundary_subset_chainSet hne hp
    have hhead : ([(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten ++
        [(xlo, yhi)]).headD 0 = (xlo, ylo) := rfl
    rw [hhead] at hb
    have e : [(xlo, ylo)] ++ F.flatten ++ [(xhi, ylo), (xhi, yhi)] ++ C.flatten ++ [(xlo, yhi)] ++
        [(xlo, ylo)] = ((xlo, ylo) :: F.flatten) ++
          (xhi, ylo) :: (xhi, yhi) :: (C.flatten ++ [(xlo, yhi), (xlo, ylo)]) := by simp
    have e2 : (xhi, yhi) :: (C.flatten ++ [(xlo, yhi), (xlo, ylo)]) =
        ((xhi, yhi) :: C.flatten) ++ (xlo, yhi) :: [(xlo, ylo)] := by simp
    rw [e, chainSet_append_cons, chainSet_cons_cons, e2,
      chainSet_append_cons ((xhi, yhi) :: C.flatten) (xlo, yhi) [(xlo, ylo)]] at hb
    rcases hb with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (by simpa [hFC] using h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr (by simpa [hCC] using h))
    · exact Or.inr (by simpa using h)
  -- covering the boundary pieces
  have hFCU : FC ⊆ U := fun p hp => hsubf (hc_cover h1 hGf hOf (hFCsub hp))
  have hCCU : CC ⊆ U := by
    intro p hp
    refine hsubc ?_
    have := (hCCneg p).1 hp
    exact hc_cover hTc hGc hOc (comb_sub hGc hOc this)
  have hRWU : ∀ t, ylo ≤ t → t ≤ yhi → ((xhi, t) : Point) ∈ U := by
    intro t a b
    by_cases ht1 : t ≤ Tf
    · rcases eq_or_lt_of_le a with a | a
      · subst a
        refine hsubf (hc_cover h1 hGf hOf (Or.inl ⟨rfl, hx.le, le_rfl, fun Z hZ => Or.inr ?_⟩))
        have := hbf.2 Z hZ; have := (hGf Z hZ).lR; linarith
      · exact hsubf (hc_right (y₀ := ylo) (T := Tf) hOf t a ht1).1.mem
    by_cases ht2 : t ≤ Tc
    · exact hsubh ⟨hx.le, le_rfl, by linarith, ht2⟩
    push Not at ht1 ht2
    refine hsubc ?_
    show -((xhi, t) : Point) ∈ Uc
    have e : -((xhi, t) : Point) = (-xhi, -t) := rfl
    rw [e]
    rcases eq_or_lt_of_le b with b | b
    · subst b
      refine hc_cover hTc hGc hOc (Or.inl ⟨rfl, le_rfl, by linarith, fun Z hZ => Or.inl ?_⟩)
      have := hbc.2 Z hZ; have := (hGc Z hZ).Lf; linarith
    · exact (hc_left (y₀ := -yhi) (T := -Tc) hOc (-t) (by linarith) (by linarith)).1.mem
  have hLWU : ∀ t, ylo ≤ t → t ≤ yhi → ((xlo, t) : Point) ∈ U := by
    intro t a b
    by_cases ht1 : t ≤ Tf
    · rcases eq_or_lt_of_le a with a | a
      · subst a
        refine hsubf (hc_cover h1 hGf hOf (Or.inl ⟨rfl, le_rfl, hx.le, fun Z hZ => Or.inl ?_⟩))
        have := hbf.2 Z hZ; have := (hGf Z hZ).Lf; linarith
      · exact hsubf (hc_left (y₀ := ylo) (T := Tf) hOf t a ht1).1.mem
    by_cases ht2 : t ≤ Tc
    · exact hsubh ⟨le_rfl, hx.le, by linarith, ht2⟩
    push Not at ht1 ht2
    refine hsubc ?_
    show -((xlo, t) : Point) ∈ Uc
    have e : -((xlo, t) : Point) = (-xlo, -t) := rfl
    rw [e]
    rcases eq_or_lt_of_le b with b | b
    · subst b
      refine hc_cover hTc hGc hOc (Or.inl ⟨rfl, by linarith, le_rfl, fun Z hZ => Or.inr ?_⟩)
      have := hbc.2 Z hZ; have := (hGc Z hZ).lR; linarith
    · exact (hc_right (y₀ := -yhi) (T := -Tc) hOc (-t) (by linarith) (by linarith)).1.mem
  -- the hall's bottom and top
  have hallBot : ∀ x, xlo ≤ x → x ≤ xhi → ((x, Tf) : Point) ∈ P.boundary ∨
      ((x, Tf) : Point) ∈ interior U := by
    intro x a b
    rcases eq_or_lt_of_le a with a | a
    · subst a; exact Or.inl (wallL Tf h1.le (by linarith))
    rcases eq_or_lt_of_le b with b | b
    · subst b; exact Or.inl (wallR Tf h1.le (by linarith))
    refine Or.inr (interior_of_lr ?_ ?_ ?_ ?_)
    · exact ((hc_tiles h1 hGf hOf x a.le b.le).2 a).mono hsubf
    · refine (quadIn_rect (r := hall) ?_ ?_).mono hsubh
      · simp only [Bool.false_eq_true, ↓reduceIte, hhall]; exact ⟨a, b.le⟩
      · simp only [↓reduceIte, hhall]; exact ⟨le_rfl, h2⟩
    · exact ((hc_tiles h1 hGf hOf x a.le b.le).1 b).mono hsubf
    · refine (quadIn_rect (r := hall) ?_ ?_).mono hsubh
      · simp only [↓reduceIte, hhall]; exact ⟨a.le, b⟩
      · simp only [↓reduceIte, hhall]; exact ⟨le_rfl, h2⟩
  have hallTop : ∀ x, xlo ≤ x → x ≤ xhi → ((x, Tc) : Point) ∈ P.boundary ∨
      ((x, Tc) : Point) ∈ interior U := by
    intro x a b
    rcases eq_or_lt_of_le a with a | a
    · subst a; exact Or.inl (wallL Tc (by linarith) h3.le)
    rcases eq_or_lt_of_le b with b | b
    · subst b; exact Or.inl (wallR Tc (by linarith) h3.le)
    have ht := hc_tiles hTc hGc hOc (-x) (by linarith) (by linarith)
    refine Or.inr (interior_of_lr ?_ ?_ ?_ ?_)
    · refine (quadIn_rect (r := hall) ?_ ?_).mono hsubh
      · simp only [Bool.false_eq_true, ↓reduceIte, hhall]; exact ⟨a, b.le⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, hhall]; exact ⟨h2, le_rfl⟩
    · exact (QuadIn.neg (ht.1 (by linarith))).mono hsubc
    · refine (quadIn_rect (r := hall) ?_ ?_).mono hsubh
      · simp only [↓reduceIte, hhall]; exact ⟨a.le, b⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, hhall]; exact ⟨h2, le_rfl⟩
    · exact (QuadIn.neg (ht.2 (by linarith))).mono hsubc
  -- apply the region theorem
  rw [hU, ← pieceUnion_rects hpos]
  refine filled_eq_of_sides' hP _ ?_ ?_ ?_ ?_ ?_
  · intro K hK
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hK
    exact isPiece_rectP (hpos r hr).1 (hpos r hr).2
  · rw [pieceUnion_rects hpos]; exact isBoundedSet_RU _
  · rw [pieceUnion_rects hpos]
    intro p hp
    rcases hbdec hp with ((h | h) | h) | h
    · exact hFCU h
    · have := vseg_snd (by linarith) h
      rw [show p = (xhi, p.2) from Prod.ext (vseg_fst h) rfl]
      exact hRWU p.2 this.1 this.2
    · exact hCCU h
    · rw [Geometry.segment_comm] at h
      have := vseg_snd (by linarith) h
      rw [show p = (xlo, p.2) from Prod.ext (vseg_fst h) rfl]
      exact hLWU p.2 this.1 this.2
  · rw [pieceUnion_rects hpos]
    intro K hK j hj y hy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hK
    have hj4 : j < 4 := by simpa [Rect.poly, rectP_n] using hj
    have hside : RSide r y := ⟨j, hj4, hy⟩
    simp only [combRects, List.mem_cons, List.mem_append, List.mem_map] at hr
    rcases hr with rfl | hr | ⟨r', hr', rfl⟩
    · obtain ⟨⟨a1, a2, a3, a4⟩, hs⟩ := RSide.mem ⟨hx, h2⟩ hside
      simp only at a1 a2 a3 a4 hs
      rcases hs with hs | hs | hs | hs
      · left; rw [show y = (xlo, y.2) from Prod.ext hs rfl]
        exact wallL _ (by linarith) (by linarith)
      · left; rw [show y = (xhi, y.2) from Prod.ext hs rfl]
        exact wallR _ (by linarith) (by linarith)
      · rw [show y = (y.1, Tf) from Prod.ext rfl hs]; exact hallBot _ a1 a2
      · rw [show y = (y.1, Tc) from Prod.ext rfl hs]; exact hallTop _ a1 a2
    · rcases hc_side h1 hGf hOf r hr y hside with h | h | h | h
      · exact Or.inl (hFCbd (hFCsup h))
      · exact Or.inr (interior_mono hsubf h)
      · obtain ⟨hs, a1, a2⟩ := h
        rw [show y = (y.1, Tf) from Prod.ext rfl hs]; exact hallBot _ a1 a2
      · obtain ⟨hs | hs, a1, a2⟩ := h
        · left; rw [show y = (xlo, y.2) from Prod.ext hs rfl]; exact wallL _ a1 (by linarith)
        · left; rw [show y = (xhi, y.2) from Prod.ext hs rfl]; exact wallR _ a1 (by linarith)
    · have hside' := RSide.neg hside
      rcases hc_side hTc hGc hOc r' hr' (-y) hside' with h | h | h | h
      · refine Or.inl (hCCbd ((hCCneg y).2 ?_))
        have := comb_sup hGc hOc h
        exact this
      · exact Or.inr (interior_mono hsubc (interior_neg h))
      · obtain ⟨hs, a1, a2⟩ := h
        simp only [Prod.snd_neg, Prod.fst_neg, neg_inj] at hs a1 a2
        rw [show y = (y.1, Tc) from Prod.ext rfl hs]
        exact hallTop _ (by linarith) (by linarith)
      · obtain ⟨hs | hs, a1, a2⟩ := h
        · simp only [Prod.snd_neg, Prod.fst_neg, neg_inj] at hs a1 a2
          left; rw [show y = (xhi, y.2) from Prod.ext hs rfl]; exact wallR _ (by linarith) (by linarith)
        · simp only [Prod.snd_neg, Prod.fst_neg, neg_inj] at hs a1 a2
          left; rw [show y = (xlo, y.2) from Prod.ext hs rfl]; exact wallL _ (by linarith) (by linarith)
  · rw [pieceUnion_rects hpos]
    refine ⟨((xlo + xhi) / 2, (Tf + Tc) / 2),
      hsubh ⟨by simp only; linarith, by simp only; linarith, by simp only; linarith,
        by simp only; linarith⟩, fun hp => ?_⟩
    rcases hbdec hp with ((h | h) | h) | h
    · rcases hFCsub h with ⟨h, -⟩ | ⟨Z, hZ, hpZ⟩
      · simp only at h; linarith
      · obtain ⟨r, hr, hpr⟩ := (hGf Z hZ).chain hpZ
        have := ((hGf Z hZ).box r hr _ hpr).2.2
        simp only at this; linarith
    · have := vseg_fst h; simp only at this; linarith
    · rcases comb_sub hGc hOc ((hCCneg _).1 h) with ⟨h, -⟩ | ⟨Z, hZ, hpZ⟩
      · simp only [Prod.snd_neg] at h; linarith
      · obtain ⟨r, hr, hpr⟩ := (hGc Z hZ).chain hpZ
        have := ((hGc Z hZ).box r hr _ hpr).2.2
        simp only [Prod.snd_neg] at this; linarith
    · have := vseg_fst h; simp only at this; linarith

end

end ArtGallery.Orthogonal.Hard
