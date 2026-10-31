module

public import ArtGallery.Orthogonal.Hard.NookPin
public import ArtGallery.Stade.Copy
public import ArtGallery.Orthogonal.Hard.GridRoom

/-!
# The room of a copy nook

In the grid of a copy nook (`nookφ`, `nookψ`), the nook segment is the edge `x = x_N` (grid column
`15`) from row `12` (`N_top`) down to row `6`, facing east; the mouth is `[L_m, R_m]` on the
ceiling (columns `16`, `17`, row `3`).

* `nook_room`: the rectangles of the nook zone above row `2` and the upper part of the mouth
  column form a room of the polygon whose door is the mouth (`isRoom_of_cover`), containing
  Stade's nook segment `[N_bot, N_top]`;
* `nook_ext`, `nook_wall`: the open box `(φ₁₄, φ₁₅) × (ψ₆, ψ₁₂)` left of the nook segment contains
  no point of the region, so no point left of `x_N` sees an interior point of the nook edge;
* the mouth corners and the ends of the nook segment are Stade's copy points (`gpt_mouthL`, …).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

/-! ### Index data -/

/-- The rectangles of the room: the zone rectangles from row `2` up, and the upper part of the
mouth column. -/
def roomRR : List GRect := (cnRR.filter fun r => decide (2 ≤ r.2.2.1)) ++ [(16, 17, 3, 15)]

/-- The other rectangles of the zone: the strip below the ceiling, and the lower part of the
mouth column. -/
def nonRR : List GRect :=
  (cnRR.filter fun r => decide (r.2.2.1 < 2) && decide (r ≠ (16, 17, 0, 15))) ++ [(16, 17, 0, 3)]

theorem room_contact : roomRR.all (fun r => nonRR.all fun s => match r.inter s with
    | none => true
    | some X => decide (16 ≤ X.1 ∧ X.2.1 ≤ 17 ∧ X.2.2.1 = 3 ∧ X.2.2.2 = 3)) = true := by decide

theorem room_wf : (roomRR ++ nonRR).all (GRect.wf 20 19) = true := by decide

theorem room_inbox : roomRR.all (fun r => decide (1 ≤ r.1 ∧ r.2.1 ≤ 18 ∧ 2 ≤ r.2.2.1)) = true := by
  decide

theorem cnRR_split : ∀ r ∈ cnRR, r ∈ roomRR ∨ r ∈ nonRR ∨ r = (16, 17, 0, 15) := by decide

theorem ext_avoid : cnRR.all (fun r => decide (r.2.1 ≤ 14 ∨ 15 ≤ r.1 ∨ r.2.2.2 ≤ 6 ∨ 12 ≤ r.2.2.1)) =
    true := by decide

theorem seg_rect_mem : ((15, 16, 3, 15) : GRect) ∈ roomRR := by decide

theorem cnRR_wf : cnRR.all (GRect.wf 20 19) = true := by decide

variable {n : ℕ} {Φ : List Constraint}

/-! ### The copy nook of an input -/

section Nook

variable {k : ℕ} (hk : k < n) {i : InputSeg} (hi : i ∈ inputsO n Φ) (hik : i.var = k)
include hk hi hik

/-- The grid maps of the nook are strictly increasing and its oracle is sound. -/
theorem nook_grid :
    StrictMonoOn (iφ Φ (paramH n Φ) k i) (Iio 20) ∧ StrictMonoOn (iψ Φ (paramH n Φ) k i) (Iio 19) ∧
      nookOr.Sound (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) := by
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  have hH := paramH_ge_q n Φ
  subst hik
  exact ⟨nookφ_mono hH d1 d2 i.ge, nookψ_mono hH d1 d2 i.ge, nook_sound hH d1 d2 i.ge⟩

/-- A point of a rectangle of the room lies in the open nook box. -/
theorem room_in_box {r : GRect} (hr : r ∈ roomRR) {y : Point}
    (hy : y ∈ (realR (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) r).set) :
    y ∈ nookBox.set (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) := by
  obtain ⟨hφ, hψ, -⟩ := nook_grid hk hi hik
  have hb := List.all_eq_true.1 room_inbox r hr
  have hw := List.all_eq_true.1 room_wf r (List.mem_append_left _ hr)
  simp only [decide_eq_true_eq] at hb
  simp only [GRect.wf, decide_eq_true_eq] at hw
  obtain ⟨y1, y2, y3, -⟩ := hy
  simp only [realR] at y1 y2 y3
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · simp only [nookBox, Option.some.injEq] at ha; subst ha
    exact lt_of_lt_of_le (hφ (by simp) (by simp; omega) (by omega)) y1
  · simp only [nookBox, Option.some.injEq] at ha; subst ha
    exact lt_of_le_of_lt y2 (hφ (by simp; omega) (by simp) (by omega))
  · simp only [nookBox, Option.some.injEq] at ha; subst ha
    exact lt_of_lt_of_le (hψ (by simp) (by simp; omega) (by omega)) y3
  · simp [nookBox] at ha

/-- The rectangles of the region outside the nook zone avoid the open nook box. -/
theorem rest_out {r : Rect} (hr : r ∈ regionRectsO n Φ)
    (hrZ : r ∉ (nzone (varA Φ k) i.b i.ge (paramH n Φ)).rs.map Rect.neg) {y : Point}
    (hy : y ∈ r.set) (hyB : y ∈ nookBox.set (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i)) :
    False := by
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  have hH := paramH_ge_q n Φ
  have hZ := nzone_mem hk hi hik
  rcases region_rect_ceil hZ r hr with h | h
  · exact hrZ h
  · subst hik
    have := (nookBox_set (ge := i.ge)).1 hyB
    simp only [Hr] at h
    exact h y hy (by push_cast at this ⊢; exact this)

/-- The nook zone rectangles are the realised `cnRR`. -/
theorem nook_rs :
    (nzone (varA Φ k) i.b i.ge (paramH n Φ)).rs.map Rect.neg =
      cnRR.map (realR (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i)) := by
  obtain ⟨d1, d2⟩ := inputO_delta hi hk
  have hH := paramH_ge_q n Φ
  subst hik
  exact nzone_rs i.ge

/-- **The exterior box left of the nook segment.** -/
theorem nook_ext {z : Point}
    (h1 : iφ Φ (paramH n Φ) k i 14 < z.1) (h2 : z.1 < iφ Φ (paramH n Φ) k i 15)
    (h3 : iψ Φ (paramH n Φ) k i 6 < z.2) (h4 : z.2 < iψ Φ (paramH n Φ) k i 12) :
    z ∉ (Polygon.mk ((polyO n Φ).map ratPoint)).filled := by
  obtain ⟨hφ, hψ, -⟩ := nook_grid hk hi hik
  intro hz
  rw [filledO] at hz
  obtain ⟨r, hr, hzr⟩ := hz
  by_cases hrZ : r ∈ (nzone (varA Φ k) i.b i.ge (paramH n Φ)).rs.map Rect.neg
  · rw [nook_rs hk hi hik] at hrZ
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hrZ
    have hav := List.all_eq_true.1 ext_avoid s hs
    have hw := List.all_eq_true.1 cnRR_wf s hs
    simp only [decide_eq_true_eq] at hav
    simp only [GRect.wf, decide_eq_true_eq] at hw
    obtain ⟨y1, y2, y3, y4⟩ := hzr
    simp only [realR] at y1 y2 y3 y4
    rcases hav with h | h | h | h
    · have := hφ.monotoneOn (by simp; omega) (by simp) h; linarith
    · have := hφ.monotoneOn (by simp) (by simp; omega) h; linarith
    · have := hψ.monotoneOn (by simp; omega) (by simp) h; linarith
    · have := hψ.monotoneOn (by simp) (by simp; omega) h; linarith
  · refine rest_out hk hi hik hr hrZ hzr ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
    · simp only [nookBox, Option.some.injEq] at ha; subst ha
      exact lt_trans (hφ (by simp) (by simp) (by norm_num)) h1
    · simp only [nookBox, Option.some.injEq] at ha; subst ha
      exact lt_trans h2 (hφ (by simp) (by simp) (by norm_num))
    · simp only [nookBox, Option.some.injEq] at ha; subst ha
      exact lt_trans (hψ (by simp) (by simp) (by norm_num)) h3
    · simp [nookBox] at ha

/-- **No point left of `x_N` sees an interior point of the nook edge.** -/
theorem nook_wall {w z : Point} (hw1 : w.1 = iφ Φ (paramH n Φ) k i 15)
    (hw2 : iψ Φ (paramH n Φ) k i 6 < w.2) (hw3 : w.2 < iψ Φ (paramH n Φ) k i 12)
    (hz : z.1 < iφ Φ (paramH n Φ) k i 15)
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees z w) : False := by
  obtain ⟨hφ, -, -⟩ := nook_grid hk hi hik
  exact not_sees_of_empty_box (hφ (by simp) (by simp) (by norm_num))
    (fun z h1 h2 h3 h4 => nook_ext hk hi hik h1 h2 h3 h4) hw1 hw2 hw3 hz hs

/-- The room of the nook. -/
noncomputable def nookRoom (n : ℕ) (Φ : List Constraint) (k : ℕ) (i : InputSeg) : Set Point :=
  ⋃₀ {A | ∃ r ∈ roomRR, A = (realR (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) r).set}

/-- **The room of a copy nook**, with door the mouth (grid row `3`, columns `16`–`17`). -/
theorem nook_room :
    (Polygon.mk ((polyO n Φ).map ratPoint)).IsRoom (nookRoom n Φ k i)
      (ArtGallery.segment (gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) (16, 3))
        (gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) (17, 3))) := by
  obtain ⟨hφ, hψ, -⟩ := nook_grid hk hi hik
  set φ := iφ Φ (paramH n Φ) k i
  set ψ := iψ Φ (paramH n Φ) k i
  set Z := nzone (varA Φ k) i.b i.ge (paramH n Φ)
  let 𝒜 : Set (Set Point) := {A | (∃ r ∈ roomRR ++ nonRR, A = (realR φ ψ r).set) ∨
    ∃ r ∈ regionRectsO n Φ, r ∉ Z.rs.map Rect.neg ∧ A = r.set}
  have hfin : 𝒜.Finite := by
    refine Set.Finite.union ?_ ?_
    · refine ((roomRR ++ nonRR).map fun r => (realR φ ψ r).set).finite_toSet.subset ?_
      rintro A ⟨r, hr, rfl⟩; exact List.mem_map.2 ⟨r, hr, rfl⟩
    · refine ((regionRectsO n Φ).map Rect.set).finite_toSet.subset ?_
      rintro A ⟨r, hr, -, rfl⟩; exact List.mem_map.2 ⟨r, hr, rfl⟩
  refine isRoom_of_cover hfin ?_ ?_ ?_ ?_
  · rintro A (⟨r, -, rfl⟩ | ⟨r, -, -, rfl⟩) <;> exact isClosed_rect_set _
  · intro z hz
    rw [filledO] at hz
    obtain ⟨r, hr, hzr⟩ := hz
    by_cases hrZ : r ∈ Z.rs.map Rect.neg
    · rw [nook_rs hk hi hik] at hrZ
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hrZ
      rcases cnRR_split s hs with h | h | rfl
      · exact ⟨_, Or.inl ⟨s, List.mem_append_left _ h, rfl⟩, hzr⟩
      · exact ⟨_, Or.inl ⟨s, List.mem_append_right _ h, rfl⟩, hzr⟩
      · obtain ⟨y1, y2, y3, y4⟩ := hzr
        by_cases hz3 : z.2 ≤ ψ 3
        · exact ⟨_, Or.inl ⟨(16, 17, 0, 3), List.mem_append_right _ (by decide), rfl⟩,
            ⟨y1, y2, y3, hz3⟩⟩
        · exact ⟨_, Or.inl ⟨(16, 17, 3, 15), List.mem_append_left _ (by decide), rfl⟩,
            ⟨y1, y2, (not_le.1 hz3).le, y4⟩⟩
    · exact ⟨_, Or.inr ⟨r, hr, hrZ, rfl⟩, hzr⟩
  · rintro A ⟨r, hr, rfl⟩; exact Or.inl ⟨r, List.mem_append_left _ hr, rfl⟩
  · rintro y ⟨B, ⟨r, hr, rfl⟩, hyr⟩ hyD A hA hAB hyA
    rcases hA with ⟨s, hs, rfl⟩ | ⟨s, hs, hsZ, rfl⟩
    · rcases List.mem_append.1 hs with hs | hs
      · exact hAB ⟨s, hs, rfl⟩
      have hc := List.all_eq_true.1 (List.all_eq_true.1 room_contact r hr) s hs
      have hwr := List.all_eq_true.1 room_wf r (List.mem_append_left _ hr)
      have hws := List.all_eq_true.1 room_wf s (List.mem_append_right _ hs)
      split at hc
      · rename_i hi'; exact GRect.inter_empty hφ hψ hwr hws hi' hyr hyA
      · rename_i X hX
        have hyX := GRect.inter_sub hX hyr hyA
        simp only [decide_eq_true_eq] at hc
        obtain ⟨c1, c2, c3, c4⟩ := hc
        obtain ⟨y1, y2, y3, y4⟩ := hyX
        simp only [realR] at y1 y2 y3 y4
        rw [c3] at y3; rw [c4] at y4
        apply hyD
        have hy2 : y.2 = ψ 3 := le_antisymm y4 y3
        have hXw := GRect.inter_wf hwr hws hX
        simp only [GRect.wf, decide_eq_true_eq] at hXw
        have e : y = (y.1, ψ 3) := Prod.ext rfl hy2
        rw [e]
        refine (mem_segment_horiz_iff (hφ.monotoneOn (by simp) (by simp) (by norm_num))).2
          ⟨rfl, ?_, ?_⟩
        · exact le_trans (hφ.monotoneOn (by simp) (by simp; omega) c1) y1
        · exact le_trans y2 (hφ.monotoneOn (by simp; omega) (by simp) c2)
    · exact rest_out hk hi hik hs hsZ hyA (room_in_box hk hi hik hr hyr)

/-- The points of the nook edge are boundary points. -/
theorem nook_edge_bd {h : ℝ} (h1 : iψ Φ (paramH n Φ) k i 6 ≤ h) (h2 : h ≤ iψ Φ (paramH n Φ) k i 12) :
    ((iφ Φ (paramH n Φ) k i 15, h) : Point) ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  set M := (copyNookO (varA Φ k) i.b i.ge (paramH n Φ)).map ratPoint with hM
  have hML : M.length = 46 := by rw [hM, List.length_map, copyNookO_eq]; rfl
  have hseg := seg_subset_boundary (nook_infix hk hi hik) (j := 20) (by rw [hML]; norm_num)
  have e20 : M[20]'(by rw [hML]; norm_num) =
      gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) (15, 12) := by
    rw [← List.getD_eq_getElem _ 0, nook_vtx hk hi hik (by norm_num)]; rfl
  have e21 : M[20 + 1]'(by rw [hML]; norm_num) =
      gpt (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) (15, 6) := by
    rw [← List.getD_eq_getElem _ 0, nook_vtx hk hi hik (by norm_num)]; rfl
  rw [e20, e21] at hseg
  apply hseg
  rw [ArtGallery.Geometry.segment_comm]
  exact (mem_segment_vert_iff (h1.trans h2)).2 ⟨rfl, h1, h2⟩

/-- The column above the mouth, between rows `3` and `15` on the line `x_N`, lies in the room. -/
theorem nook_col_room {h : ℝ} (h1 : iψ Φ (paramH n Φ) k i 3 ≤ h) (h2 : h ≤ iψ Φ (paramH n Φ) k i 15) :
    ((iφ Φ (paramH n Φ) k i 15, h) : Point) ∈ nookRoom n Φ k i := by
  obtain ⟨hφ, -, -⟩ := nook_grid hk hi hik
  refine ⟨_, ⟨(15, 16, 3, 15), seg_rect_mem, rfl⟩, le_rfl, ?_, h1, h2⟩
  exact hφ.monotoneOn (by simp) (by simp) (by norm_num)

/-- The room lies in the open nook box. -/
theorem nookRoom_box {y : Point} (hy : y ∈ nookRoom n Φ k i) :
    y ∈ nookBox.set (iφ Φ (paramH n Φ) k i) (iψ Φ (paramH n Φ) k i) := by
  obtain ⟨B, ⟨r, hr, rfl⟩, hyr⟩ := hy
  exact room_in_box hk hi hik hr hyr

end Nook

end

end ArtGallery.Orthogonal.Hard
