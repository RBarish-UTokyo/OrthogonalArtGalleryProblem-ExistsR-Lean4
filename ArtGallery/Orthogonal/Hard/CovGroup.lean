module

public import ArtGallery.Orthogonal.Hard.CovCert

/-!
# Coverage certificates: covering the frame box of a group

A coverage certificate works in a frame box `F` of a template group.  `F` is covered by
* the *hall part* `[F.x₀, F.x₁] × [−1/4, 2H − 1/4]`;
* below `−1/4` (floor) and above `2H − 1/4` (ceiling): a partition of `[F.x₀, F.x₁]` into segments,
  each a *gap* (forbidden: the whole strip of the segment) or the abscissa range of a *zone*;
* a zone (in frame coordinates: increasing grid abscissae and ordinates, the index rectangles of
  the region and of its complement) is covered by its grid cells (each in a region or a complement
  rectangle) and the forbidden part of its column beyond the grid.

`GCovC.cover`: every point of `F` lies in the hall part, a region rectangle of a zone, or a
forbidden rectangle.  Everything is checked by `GCovC.ok` (`decide`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade Set

/-! ### Searching a sorted list of breakpoints -/

/-- A point between the entries `a` and `b` of a list lies between two consecutive entries. -/
theorem exists_step {f : ℕ → ℝ} {x : ℝ} :
    ∀ (k a : ℕ), f a ≤ x → x ≤ f (a + k + 1) → ∃ i, a ≤ i ∧ i ≤ a + k ∧ f i ≤ x ∧ x ≤ f (i + 1)
  | 0, a, h1, h2 => ⟨a, le_rfl, by omega, h1, by simpa using h2⟩
  | k + 1, a, h1, h2 => by
    by_cases hx : x ≤ f (a + 1)
    · exact ⟨a, le_rfl, by omega, h1, hx⟩
    · have e : a + 1 + k + 1 = a + (k + 1) + 1 := by omega
      have h2' : x ≤ f (a + 1 + k + 1) := by rw [e]; exact h2
      obtain ⟨i, hi1, hi2, hi3, hi4⟩ := exists_step k (a + 1) (le_of_lt (not_le.1 hx)) h2'
      exact ⟨i, by omega, by omega, hi3, hi4⟩

/-- Increasing rationals (as a `decide`-able check on consecutive entries). -/
def incQB (xs : List ℚ) : Bool :=
  (List.range (xs.length - 1)).all fun i => decide (xs.getD i 0 < xs.getD (i + 1) 0)

/-- Robustly increasing ordinates. -/
def incAHB (ys : List AH) : Bool :=
  (List.range (ys.length - 1)).all fun i => AH.lt (ys.getD i (0, 0)) (ys.getD (i + 1) (0, 0))

theorem incQB_mono {xs : List ℚ} (h : incQB xs = true) {i j : ℕ} (hij : i ≤ j)
    (hj : j < xs.length) : xs.getD i 0 ≤ xs.getD j 0 := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    have := List.all_eq_true.1 h k (List.mem_range.2 (by omega))
    have := of_decide_eq_true this
    exact (ih (by omega)).trans this.le

theorem incAHB_mono {ys : List AH} (h : incAHB ys = true) {H : ℝ} (hH : 1000 ≤ H) {i j : ℕ}
    (hij : i ≤ j) (hj : j < ys.length) : (ys.getD i (0, 0)).ev H ≤ (ys.getD j (0, 0)).ev H := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    have := List.all_eq_true.1 h k (List.mem_range.2 (by omega))
    exact (ih (by omega)).trans (AH.lt_sound this hH).le

/-! ### Zones in frame coordinates -/

/-- A zone of a group in frame coordinates. -/
structure FZoneC where
  xs : List ℚ
  ys : List AH
  rects : List GRect
  nr : List GRect
  iL : ℕ
  iR : ℕ
  jlo : ℕ
  jhi : ℕ

/-- The frame rectangle of an index rectangle. -/
def FZoneC.lr (zc : FZoneC) (r : GRect) : LR :=
  ⟨zc.xs.getD r.1 0, zc.xs.getD r.2.1 0, zc.ys.getD r.2.2.1 (0, 0), zc.ys.getD r.2.2.2 (0, 0)⟩

/-- Index containment of a cell in an index rectangle. -/
def cellInB (i j : ℕ) (r : GRect) : Bool := decide (r.1 ≤ i ∧ i < r.2.1 ∧ r.2.2.1 ≤ j ∧ j < r.2.2.2)

/-- The zone checks: increasing grid, indices in range, every cell of the box grid in a region or
a complement rectangle. -/
def FZoneC.ok (zc : FZoneC) : Bool :=
  incQB zc.xs && incAHB zc.ys &&
  decide (zc.iL < zc.iR ∧ zc.iR < zc.xs.length ∧ zc.jlo < zc.jhi ∧ zc.jhi < zc.ys.length) &&
  (zc.rects ++ zc.nr).all (fun r => decide (r.2.1 < zc.xs.length ∧ r.2.2.2 < zc.ys.length)) &&
  (List.range zc.iR).all fun i => decide (i < zc.iL) ||
    (List.range zc.jhi).all fun j => decide (j < zc.jlo) || (zc.rects ++ zc.nr).any (cellInB i j)

/-- A point of the grid box of a zone lies in a region or a complement rectangle. -/
theorem FZoneC.cover {zc : FZoneC} (h : zc.ok = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ) {z : Point}
    (hz1 : ox + zc.xs.getD zc.iL 0 ≤ z.1) (hz2 : z.1 ≤ ox + zc.xs.getD zc.iR 0)
    (hz3 : (zc.ys.getD zc.jlo (0, 0)).ev H ≤ z.2) (hz4 : z.2 ≤ (zc.ys.getD zc.jhi (0, 0)).ev H) :
    ∃ r ∈ zc.rects ++ zc.nr, z ∈ ((zc.lr r).real ox H).set := by
  simp only [FZoneC.ok, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hx, hy⟩, hdec⟩, hwf⟩, hc⟩ := h
  obtain ⟨hiL, hiR, hjl, hjh⟩ := of_decide_eq_true hdec
  simp only [List.all_eq_true, decide_eq_true_eq] at hwf
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true] at hc
  -- the column
  have ex : zc.iL + (zc.iR - zc.iL - 1) + 1 = zc.iR := by omega
  have ey : zc.jlo + (zc.jhi - zc.jlo - 1) + 1 = zc.jhi := by omega
  obtain ⟨i, hi1, hi2, hxi, hxi'⟩ := exists_step (f := fun i => ox + (zc.xs.getD i 0 : ℝ))
    (zc.iR - zc.iL - 1) zc.iL hz1 (by simp only [ex]; exact hz2)
  obtain ⟨j, hj1, hj2, hyj, hyj'⟩ := exists_step (f := fun j => (zc.ys.getD j (0, 0)).ev H)
    (zc.jhi - zc.jlo - 1) zc.jlo hz3 (by simp only [ey]; exact hz4)
  have hcij := hc i (by omega)
  rcases hcij with hi | hcij
  · omega
  have hcj := hcij j (by omega)
  rcases hcj with hj | ⟨r, hr, hcr⟩
  · omega
  refine ⟨r, hr, ?_⟩
  simp only [cellInB, decide_eq_true_eq] at hcr
  obtain ⟨c1, c2, c3, c4⟩ := hcr
  have hwr := hwf r hr
  have mx := fun a b (hab : a ≤ b) (hb : b < zc.xs.length) =>
    (show ((zc.xs.getD a 0 : ℚ) : ℝ) ≤ zc.xs.getD b 0 by exact_mod_cast incQB_mono hx hab hb)
  have my := fun a b (hab : a ≤ b) (hb : b < zc.ys.length) => incAHB_mono hy hH hab hb
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [FZoneC.lr, LR.real]
  · linarith [mx r.1 i c1 (by omega)]
  · linarith [mx (i + 1) r.2.1 (by omega) hwr.1]
  · linarith [my r.2.2.1 j c3 (by omega)]
  · linarith [my (j + 1) r.2.2.2 (by omega) hwr.2]

/-! ### The frame box of a group -/

/-- A segment of the floor or ceiling partition: a gap (`none`) or the range of zone `k`; an
*inner* gap (between two zones of the group) has its strip in the region. -/
structure SegC where
  a : ℚ
  b : ℚ
  lab : Option ℕ
  inner : Bool

/-- The coverage frame of a group. -/
structure GCovC where
  F : LR
  zones : List FZoneC
  fl : List SegC
  ce : List SegC

/-- The hall part of the frame. -/
def GCovC.hall (g : GCovC) : LR := ⟨g.F.x0, g.F.x1, (-1 / 4, 0), (-1 / 4, 2)⟩

def zoneD : FZoneC := ⟨[], [], [], [], 0, 0, 0, 0⟩

/-- The forbidden rectangles of a floor segment. -/
def GCovC.forbF (g : GCovC) (s : SegC) : List LR :=
  match s.lab with
  | none => [⟨s.a, s.b, g.F.y0, if s.inner then (-1, 0) else (-1 / 4, 0)⟩]
  | some k => let zc := g.zones.getD k zoneD
      ⟨s.a, s.b, g.F.y0, zc.ys.getD zc.jlo (0, 0)⟩ :: zc.nr.map zc.lr

/-- The forbidden rectangles of a ceiling segment. -/
def GCovC.forbC (g : GCovC) (s : SegC) : List LR :=
  match s.lab with
  | none => [⟨s.a, s.b, if s.inner then (0, 2) else (-1 / 4, 2), g.F.y1⟩]
  | some k => let zc := g.zones.getD k zoneD
      ⟨s.a, s.b, zc.ys.getD zc.jhi (0, 0), g.F.y1⟩ :: zc.nr.map zc.lr

/-- All forbidden rectangles. -/
def GCovC.forb (g : GCovC) : List LR := g.fl.flatMap g.forbF ++ g.ce.flatMap g.forbC

/-- The region rectangles of the zones. -/
def GCovC.good (g : GCovC) : List LR := g.zones.flatMap fun zc => zc.rects.map zc.lr

/-- The strips of the inner gaps (`[−1, −1/4]` on the floor, `[2H − 1/4, 2H]` on the ceiling). -/
def GCovC.strips (g : GCovC) : List LR :=
  (g.fl.filter fun s => s.lab.isNone && s.inner).map (fun s => ⟨s.a, s.b, (-1, 0), (-1 / 4, 0)⟩) ++
    (g.ce.filter fun s => s.lab.isNone && s.inner).map (fun s => ⟨s.a, s.b, (-1 / 4, 2), (0, 2)⟩)

/-- A partition of `[x₀, x₁]` into consecutive segments. -/
def partB (x0 x1 : ℚ) (ss : List SegC) : Bool :=
  decide (ss ≠ []) && decide ((ss.headD ⟨0, 0, none, false⟩).a = x0) &&
  decide ((ss.getLastD ⟨0, 0, none, false⟩).b = x1) &&
  (List.range (ss.length - 1)).all fun i =>
    decide ((ss.getD i ⟨0, 0, none, false⟩).b = (ss.getD (i + 1) ⟨0, 0, none, false⟩).a)

/-- The segment checks: a zone segment is the abscissa range of the zone, and its grid reaches
`−1/4` (floor) or starts at `2H − 1/4` (ceiling). -/
def GCovC.segB (g : GCovC) (floor : Bool) (s : SegC) : Bool :=
  decide (s.a ≤ s.b) &&
  match s.lab with
  | none => true
  | some k => let zc := g.zones.getD k zoneD
      decide (k < g.zones.length) && decide (zc.xs.getD zc.iL 0 = s.a) &&
        decide (zc.xs.getD zc.iR 0 = s.b) &&
        (if floor then decide (zc.ys.getD zc.jhi (0, 0) = (-1 / 4, 0))
          else decide (zc.ys.getD zc.jlo (0, 0) = (-1 / 4, 2))) &&
        (if floor then AH.le g.F.y0 (zc.ys.getD zc.jlo (0, 0))
          else AH.le (zc.ys.getD zc.jhi (0, 0)) g.F.y1)

/-- **The frame checks.** -/
def GCovC.ok (g : GCovC) : Bool :=
  g.zones.all FZoneC.ok && partB g.F.x0 g.F.x1 g.fl && partB g.F.x0 g.F.x1 g.ce &&
  g.fl.all (g.segB true) && g.ce.all (g.segB false)

theorem partB_find {x0 x1 : ℚ} {ss : List SegC} (h : partB x0 x1 ss = true) {x : ℝ} {ox : ℝ}
    (h1 : ox + x0 ≤ x) (h2 : x ≤ ox + x1) : ∃ s ∈ ss, ox + s.a ≤ x ∧ x ≤ ox + s.b := by
  simp only [partB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hne, ha⟩, hb⟩, hc⟩ := h
  have hlen : 0 < ss.length := List.length_pos_iff.2 hne
  set f : ℕ → ℝ := fun i => if i < ss.length then ox + (ss.getD i ⟨0, 0, none, false⟩).a
    else ox + x1 with hf
  have f0 : f 0 = ox + x0 := by
    simp only [hf, hlen, ↓reduceIte]
    rw [← ha, List.headD_eq_head?, List.getD_eq_getElem?_getD, List.head?_eq_getElem?]
  have flast : f ss.length = ox + x1 := by simp [hf]
  -- the end of segment i is the start of segment i + 1
  have hend : ∀ i < ss.length, ox + ((ss.getD i ⟨0, 0, none, false⟩).b : ℝ) = f (i + 1) := by
    intro i hi
    by_cases hi' : i + 1 < ss.length
    · simp only [hf, hi', ↓reduceIte]
      rw [hc i (by omega)]
    · have e : i = ss.length - 1 := by omega
      simp only [hf, hi', ↓reduceIte]
      rw [e, ← hb, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
        ← List.getD_eq_getElem?_getD]
  have el : 0 + (ss.length - 1) + 1 = ss.length := by omega
  obtain ⟨i, -, hi2, hxi, hxi'⟩ := exists_step (f := f) (x := x) (ss.length - 1) 0
    (by rw [f0]; exact h1) (by rw [el, flast]; exact h2)
  have hil : i < ss.length := by omega
  refine ⟨ss.getD i ⟨0, 0, none, false⟩, ?_, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem hil
  · have : f i = ox + (ss.getD i ⟨0, 0, none, false⟩).a := by simp [hf, hil]
    linarith
  · rw [hend i hil]; exact hxi'

/-- **Cover of the frame box.** -/
theorem GCovC.cover {g : GCovC} (h : g.ok = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ) {z : Point}
    (hz : z ∈ (g.F.real ox H).set) :
    z ∈ (g.hall.real ox H).set ∨ (∃ R ∈ g.good ++ g.strips, z ∈ (R.real ox H).set) ∨
      ∃ R ∈ g.forb, z ∈ (R.real ox H).set := by
  simp only [GCovC.ok, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hz0, hfl⟩, hce⟩, hsf⟩, hsc⟩ := h
  obtain ⟨z1, z2, z3, z4⟩ := hz
  simp only [LR.real] at z1 z2 z3 z4
  have hzone : ∀ (s : SegC) (k : ℕ), s.lab = some k → k < g.zones.length →
      ∀ (hzx : ox + s.a ≤ z.1 ∧ z.1 ≤ ox + s.b) (zc : FZoneC), zc = g.zones.getD k zoneD →
      zc.xs.getD zc.iL 0 = s.a → zc.xs.getD zc.iR 0 = s.b →
      (zc.ys.getD zc.jlo (0, 0)).ev H ≤ z.2 → z.2 ≤ (zc.ys.getD zc.jhi (0, 0)).ev H →
      (∃ R ∈ g.good ++ g.strips, z ∈ (R.real ox H).set) ∨
        ∃ R ∈ zc.nr.map zc.lr, z ∈ (R.real ox H).set := by
    intro s k hk hkl hzx zc hzc ha hb hy1 hy2
    have hzk : zc ∈ g.zones := by rw [hzc, List.getD_eq_getElem _ _ hkl]; exact List.getElem_mem hkl
    obtain ⟨r, hr, hzr⟩ := FZoneC.cover (hz0 zc hzk) hH ox (by rw [ha]; exact hzx.1)
      (by rw [hb]; exact hzx.2) hy1 hy2
    rcases List.mem_append.1 hr with hr | hr
    · left
      exact ⟨zc.lr r, List.mem_append_left _
        (List.mem_flatMap.2 ⟨zc, hzk, List.mem_map.2 ⟨r, hr, rfl⟩⟩), hzr⟩
    · right
      exact ⟨zc.lr r, List.mem_map.2 ⟨r, hr, rfl⟩, hzr⟩
  rcases lt_or_ge z.2 (-1 / 4) with hlo | hlo
  · -- below the floor
    right
    obtain ⟨s, hs, hsa, hsb⟩ := partB_find hfl z1 z2
    have hsB := hsf s hs
    simp only [GCovC.segB, Bool.and_eq_true, decide_eq_true_eq] at hsB
    have hsub : ∀ R ∈ g.forbF s, R ∈ g.forb := fun R hR =>
      List.mem_append_left _ (List.mem_flatMap.2 ⟨s, hs, hR⟩)
    cases hlab : s.lab with
    | none =>
      cases hin : s.inner
      · right
        refine ⟨⟨s.a, s.b, g.F.y0, (-1 / 4, 0)⟩, hsub _ (by simp [GCovC.forbF, hlab, hin]), ?_⟩
        refine ⟨hsa, hsb, z3, ?_⟩; simp only [LR.real, AH.ev]; push_cast; linarith
      · rcases le_or_gt z.2 (-1) with hm | hm
        · right
          refine ⟨⟨s.a, s.b, g.F.y0, (-1, 0)⟩, hsub _ (by simp [GCovC.forbF, hlab, hin]), ?_⟩
          refine ⟨hsa, hsb, z3, ?_⟩; simp only [LR.real, AH.ev]; push_cast; linarith
        · left
          refine ⟨⟨s.a, s.b, (-1, 0), (-1 / 4, 0)⟩, List.mem_append_right _ ?_, hsa, hsb, ?_, ?_⟩
          · exact List.mem_append_left _ (List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, by simp [hlab, hin]⟩, rfl⟩)
          · simp only [LR.real, AH.ev]; push_cast; linarith
          · simp only [LR.real, AH.ev]; push_cast; linarith
    | some k =>
      rw [hlab] at hsB
      simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hsB
      obtain ⟨-, ⟨⟨⟨⟨hkl, ha⟩, hb⟩, hT⟩, hF⟩⟩ := hsB
      set zc := g.zones.getD k zoneD with hzc
      rcases lt_or_ge z.2 ((zc.ys.getD zc.jlo (0, 0)).ev H) with hb0 | hb0
      · right
        refine ⟨⟨s.a, s.b, g.F.y0, zc.ys.getD zc.jlo (0, 0)⟩,
          hsub _ (by simp [GCovC.forbF, hlab, hzc]), hsa, hsb, z3, hb0.le⟩
      · have hT' : (zc.ys.getD zc.jhi (0, 0)).ev H = -1 / 4 := by
          rw [hT]; simp only [AH.ev]; push_cast; ring
        rcases hzone s k hlab hkl ⟨hsa, hsb⟩ zc hzc ha hb hb0 (by rw [hT']; exact hlo.le) with
          h | ⟨R, hR, hzR⟩
        · exact Or.inl h
        · right
          refine ⟨R, hsub _ ?_, hzR⟩
          simp only [GCovC.forbF, hlab]
          exact List.mem_cons_of_mem _ (by rw [← hzc]; exact hR)
  rcases le_or_gt z.2 (2 * H - 1 / 4) with hhi | hhi
  · left
    refine ⟨z1, z2, ?_, ?_⟩ <;> simp only [GCovC.hall, LR.real, AH.ev] <;> push_cast <;> linarith
  · -- above the ceiling
    right
    obtain ⟨s, hs, hsa, hsb⟩ := partB_find hce z1 z2
    have hsB := hsc s hs
    simp only [GCovC.segB, Bool.and_eq_true, decide_eq_true_eq] at hsB
    have hsub : ∀ R ∈ g.forbC s, R ∈ g.forb := fun R hR =>
      List.mem_append_right _ (List.mem_flatMap.2 ⟨s, hs, hR⟩)
    cases hlab : s.lab with
    | none =>
      cases hin : s.inner
      · right
        refine ⟨⟨s.a, s.b, (-1 / 4, 2), g.F.y1⟩, hsub _ (by simp [GCovC.forbC, hlab, hin]), ?_⟩
        refine ⟨hsa, hsb, ?_, z4⟩; simp only [LR.real, AH.ev]; push_cast; linarith
      · rcases le_or_gt (2 * H) z.2 with hm | hm
        · right
          refine ⟨⟨s.a, s.b, (0, 2), g.F.y1⟩, hsub _ (by simp [GCovC.forbC, hlab, hin]), ?_⟩
          refine ⟨hsa, hsb, ?_, z4⟩; simp only [LR.real, AH.ev]; push_cast; linarith
        · left
          refine ⟨⟨s.a, s.b, (-1 / 4, 2), (0, 2)⟩, List.mem_append_right _ ?_, hsa, hsb, ?_, ?_⟩
          · exact List.mem_append_right _ (List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, by simp [hlab, hin]⟩, rfl⟩)
          · simp only [LR.real, AH.ev]; push_cast; linarith
          · simp only [LR.real, AH.ev]; push_cast; linarith
    | some k =>
      rw [hlab] at hsB
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hsB
      obtain ⟨-, ⟨⟨⟨⟨hkl, ha⟩, hb⟩, hT⟩, hF⟩⟩ := hsB
      set zc := g.zones.getD k zoneD with hzc
      rcases le_or_gt z.2 ((zc.ys.getD zc.jhi (0, 0)).ev H) with hb0 | hb0
      · have hT' : (zc.ys.getD zc.jlo (0, 0)).ev H = 2 * H - 1 / 4 := by
          rw [hT]; simp only [AH.ev]; push_cast; ring
        rcases hzone s k hlab hkl ⟨hsa, hsb⟩ zc hzc ha hb (by rw [hT']; exact hhi.le) hb0 with
          h | ⟨R, hR, hzR⟩
        · exact Or.inl h
        · right
          refine ⟨R, hsub _ ?_, hzR⟩
          simp only [GCovC.forbC, hlab]
          exact List.mem_cons_of_mem _ (by rw [← hzc]; exact hR)
      · right
        refine ⟨⟨s.a, s.b, zc.ys.getD zc.jhi (0, 0), g.F.y1⟩,
          hsub _ (by simp [GCovC.forbC, hlab, hzc]), hsa, hsb, hb0.le, z4⟩


/-! ### Group coverage certificates -/

/-- The axis lines of a box (`x ≥ x₀`, `x ≤ x₁`, `y ≥ y₀`, `y ≤ y₁`). -/
def boxLines (b : LR) : List LLine :=
  [((b.x0, (0, 0)), (b.x0, (-1, 0))), ((b.x1, (0, 0)), (b.x1, (1, 0))),
    ((0, b.y0), (1, b.y0)), ((1, b.y1), (0, b.y1))]

theorem mem_boxLines_iff (ox H : ℝ) (b : LR) (z : Point) :
    z ∈ linesSet ox H (boxLines b) ↔ z ∈ (b.real ox H).set := by
  simp only [linesSet, boxLines, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, LLine.set, mem_ofPred_eq, det, LP.real, LR.real, Rect.set, AH.ev]
  push_cast
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h1, h2, h3, h4⟩; refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The item as a list of lines (its lines and the lines of its box). -/
def CItem.allLines (it : CItem) : List LLine := it.lines ++ boxLines it.box

theorem CItem.mem_set_iff (ox H : ℝ) (it : CItem) (z : Point) :
    z ∈ it.set ox H ↔ z ∈ linesSet ox H it.allLines := by
  simp only [CItem.set, CItem.allLines, linesSet, List.mem_append, mem_inter_iff]
  rw [← mem_boxLines_iff ox H it.box z]
  simp only [linesSet]
  constructor
  · rintro ⟨h1, h2⟩ l (hl | hl)
    · exact h1 l hl
    · exact h2 l hl
  · intro h; exact ⟨fun l hl => h l (Or.inl hl), fun l hl => h l (Or.inr hl)⟩

/-- How the region rectangle `R` is covered: `0`: entirely; `1`: its part below the floor `y ≤ −1`
(it lies below `−1/4`); `2`: its part above the ceiling `y ≥ 2H` (it lies above `2H − 1/4`); `3`:
not at all (it lies in the strips `−1 ≤ y ≤ 2H`, covered globally). -/
def clipLR (R : LR) : ℕ → Option LR
  | 0 => some R
  | 1 => some ⟨R.x0, R.x1, R.y0, (-1, 0)⟩
  | 2 => some ⟨R.x0, R.x1, (0, 2), R.y1⟩
  | _ => none

/-- The side condition of a covering kind. -/
def clipCondB (R : LR) : ℕ → Bool
  | 0 => true
  | 1 => AH.le R.y1 (-1 / 4, 0)
  | 2 => AH.le (-1 / 4, 2) R.y0
  | 3 => AH.le (-1, 0) R.y0 && AH.le R.y1 (0, 2)
  | _ => false

theorem clipLR_cover {R : LR} {k : ℕ} (hk : clipCondB R k = true) {H : ℝ} (hH : 1000 ≤ H)
    (ox : ℝ) {z : Point} (hz : z ∈ (R.real ox H).set) (hy : z.2 < -1 ∨ 2 * H < z.2) :
    ∃ r', clipLR R k = some r' ∧ z ∈ (r'.real ox H).set := by
  obtain ⟨z1, z2, z3, z4⟩ := hz
  simp only [LR.real] at z1 z2 z3 z4
  match k, hk with
  | 0, _ => exact ⟨R, rfl, z1, z2, z3, z4⟩
  | 1, hk =>
    have := AH.le_sound hk hH
    simp only [AH.ev] at this z4 ⊢
    push_cast at this
    rcases hy with hy | hy
    · refine ⟨_, rfl, z1, z2, z3, ?_⟩; simp only [LR.real, AH.ev]; push_cast; linarith
    · exfalso; linarith
  | 2, hk =>
    have := AH.le_sound hk hH
    simp only [AH.ev] at this z3 ⊢
    push_cast at this
    rcases hy with hy | hy
    · exfalso; linarith
    · refine ⟨_, rfl, z1, z2, ?_, z4⟩; simp only [LR.real, AH.ev]; push_cast; linarith
  | 3, hk =>
    simp only [clipCondB, Bool.and_eq_true] at hk
    have h1 := AH.le_sound hk.1 hH
    have h2 := AH.le_sound hk.2 hH
    simp only [AH.ev] at h1 h2 z3 z4
    push_cast at h1 h2
    exfalso
    rcases hy with hy | hy <;> linarith
  | n + 4, hk => simp [clipCondB] at hk

/-- A coverage certificate of a group: the frame, the items with the range points of their
guards, and for every region rectangle its covering kind and a cut tree. -/
structure GroupCov where
  frame : GCovC
  items : List CItem
  rngs : List (List LP)
  trees : List (ℕ × CTree)

def CItem.dflt : CItem := ⟨[], ⟨0, 0, (0, 0), (0, 0)⟩, (0, (0, 0))⟩

def LR.dflt0 : LR := ⟨0, 0, (0, 0), (0, 0)⟩

/-- `p k` for `a ≤ k < b`. -/
def idxAll (p : ℕ → Bool) (a b : ℕ) : Bool := (List.range' a (b - a)).all p

theorem idxAll_join {p : ℕ → Bool} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : idxAll p a b = true) (h2 : idxAll p b c = true) : idxAll p a c = true := by
  unfold idxAll at *
  rw [List.all_eq_true] at *
  intro k hk
  rw [List.mem_range'_1] at hk
  by_cases hkb : k < b
  · exact h1 k (List.mem_range'_1.2 ⟨hk.1, by omega⟩)
  · exact h2 k (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem idxAll_sound {p : ℕ → Bool} {n : ℕ} (h : idxAll p 0 n = true) {k : ℕ} (hk : k < n) :
    p k = true :=
  List.all_eq_true.1 h k (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)

/-- The checks of item `k`: strict inner point, box in the frame, misses every forbidden
rectangle. -/
def GroupCov.itemB (c : GroupCov) (k : ℕ) : Bool :=
  let it := c.items.getD k CItem.dflt
  it.innerB &&
    (AH.le c.frame.F.y0 it.box.y0 && AH.le it.box.y1 c.frame.F.y1 &&
      decide (c.frame.F.x0 ≤ it.box.x0) && decide (it.box.x1 ≤ c.frame.F.x1)) &&
    c.frame.forb.all it.offB

/-- The range points of item `k` lie in it. -/
def GroupCov.rngB (c : GroupCov) (k : ℕ) : Bool :=
  (c.rngs.getD k []).all (inLinesB (c.items.getD k CItem.dflt).allLines)

/-- The covering kind and the tree of the region rectangle `i`. -/
def GroupCov.treeIB (c : GroupCov) (i : ℕ) : Bool :=
  let R := c.frame.good.getD i LR.dflt0
  let kt := c.trees.getD i (3, .leaf 0)
  clipCondB R kt.1 &&
    match clipLR R kt.1 with
    | none => true
    | some r => treeB (c.items.map CItem.allLines) r kt.2

/-- **The group coverage check.** -/
def GroupCov.ok (c : GroupCov) : Bool :=
  c.frame.ok && decide (c.rngs.length = c.items.length) &&
  decide (c.trees.length = c.frame.good.length) &&
  idxAll c.itemB 0 c.items.length && idxAll c.rngB 0 c.items.length &&
  idxAll c.treeIB 0 c.frame.good.length

theorem getD_map_allLines {items : List CItem} {k : ℕ} (hk : k < items.length) :
    (items.map CItem.allLines).getD k [] = (items.getD k CItem.dflt).allLines := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk,
    List.getElem_map]

/-- **Soundness of a group coverage certificate.**  Let `S` contain the region rectangles of
the zones, the strips of the inner gaps and the hall part of the frame.  Every point of a region rectangle strictly below the
floor or above the ceiling lies in an item that is contained in `S` and contains the range points
of its guard. -/
theorem GroupCov.sound {c : GroupCov} (h : c.ok = true) {H : ℝ} (hH : 1000 ≤ H) (ox : ℝ)
    {S : Set Point} (hgood : ∀ R ∈ c.frame.good ++ c.frame.strips, (R.real ox H).set ⊆ S)
    (hhall : (c.frame.hall.real ox H).set ⊆ S) {R : LR} (hR : R ∈ c.frame.good) {z : Point}
    (hz : z ∈ (R.real ox H).set) (hy : z.2 < -1 ∨ 2 * H < z.2) :
    ∃ k < c.items.length, z ∈ (c.items.getD k CItem.dflt).set ox H ∧
      (c.items.getD k CItem.dflt).set ox H ⊆ S ∧
      ∀ p ∈ c.rngs.getD k [], p.real ox H ∈ (c.items.getD k CItem.dflt).set ox H := by
  simp only [GroupCov.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hfr, hlen⟩, htl⟩, hit⟩, hrng⟩, htr⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hR
  have hRi : c.frame.good.getD i LR.dflt0 = c.frame.good[i] := List.getD_eq_getElem _ _ hi
  have ht := idxAll_sound htr hi
  simp only [GroupCov.treeIB, hRi, Bool.and_eq_true] at ht
  obtain ⟨hcond, htree⟩ := ht
  obtain ⟨r, hr, hzr⟩ := clipLR_cover hcond hH ox hz hy
  rw [hr] at htree
  obtain ⟨k, hk, hzk⟩ := treeB_sound hH ox _ r htree z hzr
  have hk' : k < c.items.length := by simpa using hk
  rw [getD_map_allLines hk'] at hzk
  refine ⟨k, hk', (CItem.mem_set_iff ox H _ z).2 hzk, ?_, fun p hp => ?_⟩
  · have hitk := idxAll_sound hit hk'
    simp only [GroupCov.itemB, Bool.and_eq_true, List.all_eq_true] at hitk
    obtain ⟨⟨hin, hbox⟩, hoff⟩ := hitk
    have hsub := CItem.subset_good (it := c.items.getD k CItem.dflt) hin hH ox (F := c.frame.F)
      (by simp only [Bool.and_eq_true]; exact hbox)
      (good := (c.frame.hall.real ox H) :: (c.frame.good ++ c.frame.strips).map (LR.real ox H))
      (forb := c.frame.forb)
      (fun z hz => by
        rcases GCovC.cover hfr hH ox hz with h | ⟨R', hR', hzR'⟩ | h
        · exact Or.inl ⟨_, List.mem_cons_self, h⟩
        · exact Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨R', hR', rfl⟩), hzR'⟩
        · exact Or.inr h)
      (List.all_eq_true.2 hoff)
    intro w hw
    obtain ⟨A, ⟨R', hR', rfl⟩, hwA⟩ := hsub hw
    rcases List.mem_cons.1 hR' with rfl | hR'
    · exact hhall hwA
    · obtain ⟨R'', hR'', rfl⟩ := List.mem_map.1 hR'
      exact hgood R'' hR'' hwA
  · have := List.all_eq_true.1 (idxAll_sound hrng hk') p hp
    exact (CItem.mem_set_iff ox H _ _).2 (inLinesB_sound this hH ox)

/-- **The group check from its parts** (proved as separate declarations). -/
theorem GroupCov.ok_of_parts {c : GroupCov} {n m : ℕ} (h0 : c.frame.ok = true)
    (hn : c.items.length = n) (hm : c.frame.good.length = m) (h1 : c.rngs.length = n)
    (h2 : c.trees.length = m) (hi : idxAll c.itemB 0 n = true) (hr : idxAll c.rngB 0 n = true)
    (ht : idxAll c.treeIB 0 m = true) : c.ok = true := by
  subst hn hm
  simp only [GroupCov.ok, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, hi⟩, hr⟩, ht⟩

end

end ArtGallery.Orthogonal.Hard
