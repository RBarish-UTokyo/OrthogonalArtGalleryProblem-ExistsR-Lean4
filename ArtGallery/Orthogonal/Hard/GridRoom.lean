module

public import ArtGallery.Orthogonal.Hard.GCert
public import ArtGallery.Stade.Copy

/-!
# Rooms made of grid rectangles

A generic form of the room argument of `CopyRoom.lean`.  The region is covered by the realised
rectangles of a grid (`RR`: the room, `NR`: the rest of the zone) and by further closed sets
(`rest`) avoiding an open set `U` that contains the room rectangles.  If every room rectangle meets
every rectangle of `NR` only on a horizontal door row `j` between the columns `a` and `b`
(`gridRoomB`, decided on indices), then the room rectangles form a room whose door is the segment
`(φ a, ψ j) – (φ b, ψ j)` (`gridRoom`).  The vertical variant (`gridRoomVB`, `gridRoomV`) has a
door on a column.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade ArtGallery.Geometry Set

/-- The room check with a horizontal door: rectangles well formed, door on row `j` between the
columns `a ≤ b`, every contact of a room rectangle with a rectangle of `NR` on the door. -/
def gridRoomB (NX NY : ℕ) (RR NR : List GRect) (j a b : ℕ) : Bool :=
  (RR ++ NR).all (GRect.wf NX NY) && decide (a ≤ b ∧ b < NX ∧ j < NY) &&
  RR.all (fun r => NR.all fun s => match r.inter s with
    | none => true
    | some X => decide (X.2.2.1 = j ∧ X.2.2.2 = j ∧ a ≤ X.1 ∧ X.2.1 ≤ b))

/-- The room check with a vertical door on column `i` between the rows `a ≤ b`. -/
def gridRoomVB (NX NY : ℕ) (RR NR : List GRect) (i a b : ℕ) : Bool :=
  (RR ++ NR).all (GRect.wf NX NY) && decide (a ≤ b ∧ b < NY ∧ i < NX) &&
  RR.all (fun r => NR.all fun s => match r.inter s with
    | none => true
    | some X => decide (X.1 = i ∧ X.2.1 = i ∧ a ≤ X.2.2.1 ∧ X.2.2.2 ≤ b))

/-- The realised room. -/
def gridRoomSet (φ ψ : ℕ → ℝ) (RR : List GRect) : Set Point :=
  ⋃₀ {A | ∃ r ∈ RR, A = (realR φ ψ r).set}

variable {P : Polygon} {NX NY : ℕ} {φ ψ : ℕ → ℝ}

theorem mem_gridRoomSet {RR : List GRect} {z : Point} :
    z ∈ gridRoomSet φ ψ RR ↔ ∃ r ∈ RR, z ∈ (realR φ ψ r).set := by
  constructor
  · rintro ⟨A, ⟨r, hr, rfl⟩, hz⟩; exact ⟨r, hr, hz⟩
  · rintro ⟨r, hr, hz⟩; exact ⟨_, ⟨r, hr, rfl⟩, hz⟩

/-- The generic room argument: the door `D` contains every contact point. -/
theorem gridRoom_gen {RR NR : List GRect} {rest : List (Set Point)} {U D : Set Point}
    (hrc : ∀ A ∈ rest, IsClosed A)
    (hcov : ∀ z ∈ P.filled, (∃ r ∈ RR ++ NR, z ∈ (realR φ ψ r).set) ∨ ∃ A ∈ rest, z ∈ A)
    (hin : ∀ r ∈ RR, ∀ z ∈ (realR φ ψ r).set, z ∈ U) (hout : ∀ A ∈ rest, ∀ z ∈ A, z ∉ U)
    (hcon : ∀ r ∈ RR, ∀ s ∈ NR, ∀ z, z ∈ (realR φ ψ r).set → z ∈ (realR φ ψ s).set → z ∈ D) :
    P.IsRoom (gridRoomSet φ ψ RR) D := by
  let 𝒜 : Set (Set Point) := {A | (∃ r ∈ RR ++ NR, A = (realR φ ψ r).set) ∨ A ∈ rest}
  have hfin : 𝒜.Finite := by
    refine Set.Finite.union ?_ ?_
    · refine ((RR ++ NR).map fun r => (realR φ ψ r).set).finite_toSet.subset ?_
      rintro A ⟨r, hr, rfl⟩; exact List.mem_map.2 ⟨r, hr, rfl⟩
    · exact rest.finite_toSet
  refine isRoom_of_cover (𝒜 := 𝒜) hfin ?_ ?_ ?_ ?_
  · rintro A (⟨r, -, rfl⟩ | hA)
    · exact isClosed_rect_set _
    · exact hrc A hA
  · intro z hz
    rcases hcov z hz with ⟨r, hr, hzr⟩ | ⟨A, hA, hzA⟩
    · exact ⟨_, Or.inl ⟨r, hr, rfl⟩, hzr⟩
    · exact ⟨A, Or.inr hA, hzA⟩
  · rintro A ⟨r, hr, rfl⟩; exact Or.inl ⟨r, List.mem_append_left _ hr, rfl⟩
  · rintro y ⟨B, ⟨r, hr, rfl⟩, hyr⟩ hyD A hA hAB hyA
    rcases hA with ⟨s, hs, rfl⟩ | hA
    · rcases List.mem_append.1 hs with hs | hs
      · exact hAB ⟨s, hs, rfl⟩
      · exact hyD (hcon r hr s hs y hyr hyA)
    · exact hout A hA y hyA (hin r hr y hyr)

/-- **Rooms of grid rectangles with a horizontal door.** -/
theorem gridRoom (hφ : StrictMonoOn φ (Iio NX)) (hψ : StrictMonoOn ψ (Iio NY))
    {RR NR : List GRect} {j a b : ℕ} (h : gridRoomB NX NY RR NR j a b = true)
    {rest : List (Set Point)} {U : Set Point} (hrc : ∀ A ∈ rest, IsClosed A)
    (hcov : ∀ z ∈ P.filled, (∃ r ∈ RR ++ NR, z ∈ (realR φ ψ r).set) ∨ ∃ A ∈ rest, z ∈ A)
    (hin : ∀ r ∈ RR, ∀ z ∈ (realR φ ψ r).set, z ∈ U) (hout : ∀ A ∈ rest, ∀ z ∈ A, z ∉ U) :
    P.IsRoom (gridRoomSet φ ψ RR) (ArtGallery.segment (φ a, ψ j) (φ b, ψ j)) := by
  simp only [gridRoomB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hwf, hab, hbN, hj⟩, hc⟩ := h
  refine gridRoom_gen hrc hcov hin hout (fun r hr s hs y hyr hys => ?_)
  have hcrs := hc r hr s hs
  have hwr := hwf r (List.mem_append_left _ hr)
  have hws := hwf s (List.mem_append_right _ hs)
  split at hcrs
  · rename_i hi'; exact (GRect.inter_empty hφ hψ hwr hws hi' hyr hys).elim
  · rename_i X hX
    have hyX := GRect.inter_sub hX hyr hys
    simp only [decide_eq_true_eq] at hcrs
    obtain ⟨c1, c2, c3, c4⟩ := hcrs
    have hXw := GRect.inter_wf hwr hws hX
    simp only [GRect.wf, decide_eq_true_eq] at hXw
    obtain ⟨y1, y2, y3, y4⟩ := hyX
    simp only [realR] at y1 y2 y3 y4
    rw [c1] at y3; rw [c2] at y4
    have hy2 : y.2 = ψ j := le_antisymm y4 y3
    have e : y = (y.1, ψ j) := Prod.ext rfl hy2
    rw [e]
    refine (mem_segment_horiz_iff (hφ.monotoneOn (by simp; omega) (by simp; omega) hab)).2
      ⟨rfl, ?_, ?_⟩
    · exact le_trans (hφ.monotoneOn (by simp; omega) (by simp; omega) c3) y1
    · exact le_trans y2 (hφ.monotoneOn (by simp; omega) (by simp; omega) c4)

/-- **Rooms of grid rectangles with a vertical door.** -/
theorem gridRoomV (hφ : StrictMonoOn φ (Iio NX)) (hψ : StrictMonoOn ψ (Iio NY))
    {RR NR : List GRect} {i a b : ℕ} (h : gridRoomVB NX NY RR NR i a b = true)
    {rest : List (Set Point)} {U : Set Point} (hrc : ∀ A ∈ rest, IsClosed A)
    (hcov : ∀ z ∈ P.filled, (∃ r ∈ RR ++ NR, z ∈ (realR φ ψ r).set) ∨ ∃ A ∈ rest, z ∈ A)
    (hin : ∀ r ∈ RR, ∀ z ∈ (realR φ ψ r).set, z ∈ U) (hout : ∀ A ∈ rest, ∀ z ∈ A, z ∉ U) :
    P.IsRoom (gridRoomSet φ ψ RR) (ArtGallery.segment (φ i, ψ a) (φ i, ψ b)) := by
  simp only [gridRoomVB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hwf, hab, hbN, hi⟩, hc⟩ := h
  refine gridRoom_gen hrc hcov hin hout (fun r hr s hs y hyr hys => ?_)
  have hcrs := hc r hr s hs
  have hwr := hwf r (List.mem_append_left _ hr)
  have hws := hwf s (List.mem_append_right _ hs)
  split at hcrs
  · rename_i hi'; exact (GRect.inter_empty hφ hψ hwr hws hi' hyr hys).elim
  · rename_i X hX
    have hyX := GRect.inter_sub hX hyr hys
    simp only [decide_eq_true_eq] at hcrs
    obtain ⟨c1, c2, c3, c4⟩ := hcrs
    have hXw := GRect.inter_wf hwr hws hX
    simp only [GRect.wf, decide_eq_true_eq] at hXw
    obtain ⟨y1, y2, y3, y4⟩ := hyX
    simp only [realR] at y1 y2 y3 y4
    rw [c1] at y1; rw [c2] at y2
    have hy1 : y.1 = φ i := le_antisymm y2 y1
    have e : y = (φ i, y.2) := Prod.ext hy1 rfl
    rw [e]
    refine (mem_segment_vert_iff (hψ.monotoneOn (by simp; omega) (by simp; omega) hab)).2
      ⟨rfl, ?_, ?_⟩
    · exact le_trans (hψ.monotoneOn (by simp; omega) (by simp; omega) c3) y3
    · exact le_trans y4 (hψ.monotoneOn (by simp; omega) (by simp; omega) c4)

/-- Room rectangles inside a floor box: `L < x₀`, `x₁ < R`, `y₁ < T` on indices. -/
def inFloorBoxB (RR : List GRect) (L R T : ℕ) : Bool :=
  RR.all fun r => decide (L < r.1 ∧ r.2.1 < R ∧ r.2.2.2 < T)

theorem inFloorBox (hφ : StrictMonoOn φ (Iio NX)) (hψ : StrictMonoOn ψ (Iio NY))
    {RR : List GRect} {L R T : ℕ} (hRN : R < NX) (hTN : T < NY)
    (hwf : RR.all (GRect.wf NX NY) = true) (h : inFloorBoxB RR L R T = true) :
    ∀ r ∈ RR, ∀ z ∈ (realR φ ψ r).set, φ L < z.1 ∧ z.1 < φ R ∧ z.2 < ψ T := by
  intro r hr z hz
  have hb := List.all_eq_true.1 h r hr
  have hw := List.all_eq_true.1 hwf r hr
  simp only [decide_eq_true_eq] at hb
  simp only [GRect.wf, decide_eq_true_eq] at hw
  obtain ⟨y1, y2, -, y4⟩ := hz
  simp only [realR] at y1 y2 y4
  refine ⟨lt_of_lt_of_le (hφ (by simp; omega) (by simp; omega) hb.1) y1,
    lt_of_le_of_lt y2 (hφ (by simp; omega) (by simp; omega) hb.2.1),
    lt_of_le_of_lt y4 (hψ (by simp; omega) (by simp; omega) hb.2.2)⟩

/-- The rectangles lie in the index box `[i₀, i₁] × [j₀, j₁]`. -/
def inIdxBoxB (RR : List GRect) (i0 i1 j0 j1 : ℕ) : Bool :=
  RR.all fun r => decide (i0 ≤ r.1 ∧ r.2.1 ≤ i1 ∧ j0 ≤ r.2.2.1 ∧ r.2.2.2 ≤ j1 ∧ r.1 ≤ r.2.1 ∧
    r.2.2.1 ≤ r.2.2.2)

/-- **Bounds of a grid room** from an index box. -/
theorem gridRoom_bounds (hφ : StrictMonoOn φ (Iio NX)) (hψ : StrictMonoOn ψ (Iio NY))
    {RR : List GRect} {i0 i1 j0 j1 : ℕ} (hNX : i1 < NX) (hNY : j1 < NY)
    (h : inIdxBoxB RR i0 i1 j0 j1 = true) {z : Point} (hz : z ∈ gridRoomSet φ ψ RR) :
    φ i0 ≤ z.1 ∧ z.1 ≤ φ i1 ∧ ψ j0 ≤ z.2 ∧ z.2 ≤ ψ j1 := by
  obtain ⟨r, hr, hzr⟩ := mem_gridRoomSet.1 hz
  have hb := List.all_eq_true.1 h r hr
  simp only [decide_eq_true_eq] at hb
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  obtain ⟨y1, y2, y3, y4⟩ := hzr
  simp only [realR] at y1 y2 y3 y4
  refine ⟨le_trans (hφ.monotoneOn (by simp; omega) (by simp; omega) b1) y1,
    le_trans y2 (hφ.monotoneOn (by simp; omega) (by simp; omega) b2),
    le_trans (hψ.monotoneOn (by simp; omega) (by simp; omega) b3) y3,
    le_trans y4 (hψ.monotoneOn (by simp; omega) (by simp; omega) b4)⟩


/-- **A wall seen only from its right**: if the open box `(x₀, x₁) × (y₀, y₁)` contains no point of
the region, no point left of `x = x₁` sees a point of `x = x₁` at a height strictly inside. -/
theorem not_sees_of_empty_box {P : Polygon} {x0 x1 y0 y1 : ℝ} (hlt : x0 < x1)
    (hE : ∀ z : Point, x0 < z.1 → z.1 < x1 → y0 < z.2 → z.2 < y1 → z ∉ P.filled)
    {w z : Point} (hw1 : w.1 = x1) (hw2 : y0 < w.2) (hw3 : w.2 < y1) (hz : z.1 < x1)
    (hs : P.Sees z w) : False := by
  set d := w.1 - z.1 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set a := min ((x1 - x0) / (2 * d)) (1 / 2) with ha
  set b := min ((w.2 - y0) / (2 * (|z.2 - w.2| + 1))) ((y1 - w.2) / (2 * (|z.2 - w.2| + 1))) with hb
  set s := min a b with hs_def
  have ha0 : 0 < a := lt_min (div_pos (by linarith) (by linarith)) (by norm_num)
  have hb0 : 0 < b := lt_min (div_pos (by linarith) (by positivity))
    (div_pos (by linarith) (by positivity))
  have hs0 : 0 < s := lt_min ha0 hb0
  have hs1 : s ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hsa : s * d ≤ (x1 - x0) / 2 := by
    have : s ≤ (x1 - x0) / (2 * d) := (min_le_left _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hsb1 : s * |z.2 - w.2| < w.2 - y0 := by
    have h1 : s ≤ (w.2 - y0) / (2 * (|z.2 - w.2| + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg (z.2 - w.2)]
  have hsb2 : s * |z.2 - w.2| < y1 - w.2 := by
    have h1 : s ≤ (y1 - w.2) / (2 * (|z.2 - w.2| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg (z.2 - w.2)]
  set t := 1 - s
  have hm : lerp z w t ∈ ArtGallery.segment z w := ⟨t, by linarith, by linarith, rfl⟩
  refine hE (lerp z w t) ?_ ?_ ?_ ?_ (hs hm)
  · simp only [lerp, t]; nlinarith
  · simp only [lerp, t]; nlinarith
  · simp only [lerp, t]
    nlinarith [abs_nonneg (z.2 - w.2), mul_le_mul_of_nonneg_left (neg_abs_le (z.2 - w.2)) hs0.le]
  · simp only [lerp, t]
    nlinarith [abs_nonneg (z.2 - w.2), mul_le_mul_of_nonneg_left (le_abs_self (z.2 - w.2)) hs0.le]

/-! ### Walls seen from one side, and cut rooms -/

/-- **A floor seen only from above**: if the open box `(x₀, x₁) × (y₀, y₁)` contains no point of
the region, no point below `y = y₁` sees a point of `y = y₁` strictly between `x₀` and `x₁`. -/
theorem not_sees_of_empty_box_below {P : Polygon} {x0 x1 y0 y1 : ℝ} (hlt : y0 < y1)
    (hE : ∀ z : Point, x0 < z.1 → z.1 < x1 → y0 < z.2 → z.2 < y1 → z ∉ P.filled)
    {w z : Point} (hw1 : w.2 = y1) (hw2 : x0 < w.1) (hw3 : w.1 < x1) (hz : z.2 < y1)
    (hs : P.Sees z w) : False := by
  set d := w.2 - z.2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set a := min ((y1 - y0) / (2 * d)) (1 / 2) with ha
  set b := min ((w.1 - x0) / (2 * (|z.1 - w.1| + 1))) ((x1 - w.1) / (2 * (|z.1 - w.1| + 1))) with hb
  set s := min a b with hs_def
  have ha0 : 0 < a := lt_min (div_pos (by linarith) (by linarith)) (by norm_num)
  have hb0 : 0 < b := lt_min (div_pos (by linarith) (by positivity))
    (div_pos (by linarith) (by positivity))
  have hs0 : 0 < s := lt_min ha0 hb0
  have hs1 : s ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hsa : s * d ≤ (y1 - y0) / 2 := by
    have : s ≤ (y1 - y0) / (2 * d) := (min_le_left _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hsb1 : s * |z.1 - w.1| < w.1 - x0 := by
    have h1 : s ≤ (w.1 - x0) / (2 * (|z.1 - w.1| + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg (z.1 - w.1)]
  have hsb2 : s * |z.1 - w.1| < x1 - w.1 := by
    have h1 : s ≤ (x1 - w.1) / (2 * (|z.1 - w.1| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg (z.1 - w.1)]
  set t := 1 - s
  have hm : lerp z w t ∈ ArtGallery.segment z w := ⟨t, by linarith, by linarith, rfl⟩
  refine hE (lerp z w t) ?_ ?_ ?_ ?_ (hs hm)
  · simp only [lerp, t]
    nlinarith [abs_nonneg (z.1 - w.1), mul_le_mul_of_nonneg_left (neg_abs_le (z.1 - w.1)) hs0.le]
  · simp only [lerp, t]
    nlinarith [abs_nonneg (z.1 - w.1), mul_le_mul_of_nonneg_left (le_abs_self (z.1 - w.1)) hs0.le]
  · simp only [lerp, t]; nlinarith
  · simp only [lerp, t]; nlinarith

/-- **Cutting a room by a closed half-plane** `f ≤ 0` (`f` continuous): the cut is a room whose
door `D'` contains the door points of the cut and the points of the room on the line `f = 0`
that lie in the region. -/
theorem isRoom_cut {P : Polygon} {R D D' : Set Point} (hR : P.IsRoom R D) {f : Point → ℝ}
    (hf : Continuous f) (hD : ∀ y ∈ R, y ∈ D → f y ≤ 0 → y ∈ D')
    (hline : ∀ y ∈ R, y ∈ P.filled → f y = 0 → y ∈ D') :
    P.IsRoom (R ∩ {z | f z ≤ 0}) D' := by
  refine ⟨hR.1.inter (isClosed_le hf continuous_const), fun y hy hyP hyD => ?_⟩
  have hyD0 : y ∉ D := fun h => hyD (hD y hy.1 h hy.2)
  obtain ⟨ε₁, hε₁, h₁⟩ := hR.2 y hy.1 hyP hyD0
  have hfy : f y < 0 := lt_of_le_of_ne hy.2 (fun h => hyD (hline y hy.1 hyP h))
  have hopen : IsOpen {z : Point | f z < 0} := isOpen_lt hf continuous_const
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.isOpen_iff.1 hopen y hfy
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z hz hzy => ⟨h₁ z hz (lt_of_lt_of_le hzy (min_le_left _ _)),
    ?_⟩⟩
  have : f z < 0 := h₂ (Metric.mem_ball.2 (lt_of_lt_of_le hzy (min_le_right _ _)))
  exact le_of_lt this

end

end ArtGallery.Orthogonal.Hard
