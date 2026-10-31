module

public import ArtGallery.Orthogonal.Hard.AddExclO
public import ArtGallery.Orthogonal.Hard.AddRoomO
public import ArtGallery.Orthogonal.Hard.AddAlgO

/-!
# The `addLe` gadget of the orthogonal construction

In a slot of kind `addLe` (origin `g`), each nook line `x = g + 30` has a pocket room whose door
is the vertical segment of `x = g + 50` between its two openings (`AddRoomO.lean`).

* `alO_excl_x`, `alO_excl_y`, `alO_excl_z`: a guard seeing an interior point of a nook segment is
  the aux guard or the designated input (`addO_excl`, with the partial-visibility region of the
  door: the room and the cone beyond the door);
* `addLeO_rel`: `w_x + w_y ≤ w_z` for the values of the three input guards, by the door bounds
  (`door_lower_col`, `door_upper_col`) and `alO_rel_of_cover_alg`.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Data of the `addLe` slot -/

/-- The witnesses of an `addLe` slot: inputs, helpers, the aux guard (`15`), the wall helpers
`W`, `W2` (`16`, `17`). -/
theorem addLe_class : ∀ i < (slotD .addLe).Ws.length,
    (i % 2 = 0 ∧ i / 2 < (oTmplInputs .addLe).length) ∨ (∃ p ∈ slotSCs .addLe, p.1 = i) ∨
      i = 15 ∨ i ∈ [16, 17] := by
  decide

theorem addLe_spots : (slotD .addLe).sps.getD 15 LR.dflt = ⟨901 / 4, 252, (-237 / 4, 0), (-89 / 2, 0)⟩ ∧
    (slotD .addLe).sps.getD 16 LR.dflt = ⟨6145 / 128, 6657 / 128, (-447 / 4, 0), (-431 / 4, 0)⟩ ∧
    (slotD .addLe).sps.getD 17 LR.dflt = ⟨6145 / 128, 6657 / 128, (-539 / 4, 0), (-523 / 4, 0)⟩ := by
  decide +kernel

theorem addLe_exempt : ∀ p ∈ slotSCs .addLe, ∀ j, (p.1, j) ∈ nookExempt .addLe →
    ((slotD .addLe).sps.getD p.1 LR.dflt).x1 < 30 := by
  have h : ∀ p ∈ slotSCs .addLe, ∀ q ∈ nookExempt .addLe, q.1 = p.1 →
      ((slotD .addLe).sps.getD p.1 LR.dflt).x1 < 30 := by decide +kernel
  exact fun p hp j hj => h p hp _ hj rfl

theorem addLe_lx (m : ℕ) (hm : m < (oTmplInputs .addLe).length) :
    ((oTmplInputs .addLe)[m].lx = 210 ∧ m = 0) ∨ ((oTmplInputs .addLe)[m].lx = 370 ∧ m = 1) ∨
      ((oTmplInputs .addLe)[m].lx = 530 ∧ m = 2) := by
  have : m < 3 := hm
  interval_cases m <;> simp [oTmplInputs]

/-- The spot of a wall helper of an `addLe` slot, as bounds. -/
theorem addLe_W_pos {g : ℝ} {i : ℕ} (hi : i ∈ [16, 17]) {z : Point}
    (hz : z ∈ (((slotD .addLe).sps.getD i LR.dflt).real g (Hr n Φ)).set) :
    g + 48 ≤ z.1 ∧ z.1 ≤ g + 6657 / 128 ∧
      ((-447 / 4 ≤ z.2 ∧ z.2 ≤ -431 / 4) ∨ (-539 / 4 ≤ z.2 ∧ z.2 ≤ -523 / 4)) := by
  obtain ⟨-, e16, e17⟩ := addLe_spots
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · rw [e16] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    simp only [LR.real, AH.ev] at h1 h2 h3 h4
    norm_num at h1 h2 h3 h4
    exact ⟨by linarith, by linarith, Or.inl ⟨by linarith, by linarith⟩⟩
  · rw [e17] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    simp only [LR.real, AH.ev] at h1 h2 h3 h4
    norm_num at h1 h2 h3 h4
    exact ⟨by linarith, by linarith, Or.inr ⟨by linarith, by linarith⟩⟩

/-- The partial-visibility region of a door `x = g + 50`, `y ∈ [lo, hi]`, for a nook point of
height `h`: the room, the door, and the cone beyond the door. -/
def doorPV (R : Set Point) (g lo hi h : ℝ) (z : Point) : Prop :=
  z ∈ R ∨ z ∈ segment (g + 50, lo) (g + 50, hi) ∨
    (g + 50 < z.1 ∧ ∃ y, lo ≤ y ∧ y ≤ hi ∧ (y - h) * (z.1 - (g + 30)) = (z.2 - h) * 20)

theorem doorPV_of_sees {P : Polygon} {R : Set Point} {g lo hi : ℝ} (hlo : lo ≤ hi)
    (hR : P.IsRoom R (segment (g + 50, lo) (g + 50, hi))) {s : Point} (hsR : s ∈ R)
    (hs1 : s.1 = g + 30) {z : Point} (hz : P.Sees z s) : doorPV R g lo hi s.2 z := by
  by_cases hzR : z ∈ R
  · exact Or.inl hzR
  right
  rcases door_viewer hR hlo (by linarith) hsR hs1 hzR hz with h | ⟨h1, y, hy1, hy2, heq⟩
  · exact Or.inl h
  · right
    refine ⟨h1, y, hy1, hy2, ?_⟩
    rw [heq]; ring

section Slot

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n) {G : Finset Point} (A : AssignO n Φ G)
  {c : Fin (paramC Φ)} (hk : cKind (gadAt Φ c) = .addLe)

include hk in
theorem al_ia : 15 < (slotWs (cKind (gadAt Φ c))).length := by rw [hk]; decide

include hk in
theorem al_hm (m : ℕ) (hm : m < 3) : m < (oTmplInputs (cKind (gadAt Φ c))).length := by
  rw [hk]; exact hm

/-- The aux guard of an `addLe` slot. -/
def alAux (hk : cKind (gadAt Φ c) = .addLe) : CIdx n Φ := .inl (.inr (.inl ⟨c, ⟨15, al_ia hk⟩⟩))

include hk in
theorem AssignO.alAux_pos : (slotG n Φ c : ℝ) + 901 / 4 ≤ (A.γ (alAux hk)).1 ∧
    (A.γ (alAux hk)).1 ≤ (slotG n Φ c : ℝ) + 252 ∧ -237 / 4 ≤ (A.γ (alAux hk)).2 ∧
    (A.γ (alAux hk)).2 ≤ -89 / 2 := by
  have hsp := A.tspot (t := .inr (.inl ⟨c, ⟨15, al_ia hk⟩⟩)) (by simp [tgrp])
  simp only [tinst] at hsp
  have e : (slotD (cKind (gadAt Φ c))).sps.getD 15 LR.dflt = ⟨901 / 4, 252, (-237 / 4, 0), (-89 / 2, 0)⟩ := by
    rw [hk]; exact addLe_spots.1
  rw [e] at hsp
  obtain ⟨h1, h2, h3, h4⟩ := hsp
  simp only [LR.real, AH.ev] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  simp only [alAux]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

include hΦ in
/-- **Exclusion for an `addLe` nook** (generic in the nook): the aux guard or input `m0`. -/
theorem alO_excl_gen {R : Set Point} {lo hi bot top ry1 : ℝ} {j m0 : ℕ} (hlo : lo ≤ hi)
    (hR : (Polygon.mk ((polyO n Φ).map ratPoint)).IsRoom R
      (segment ((slotG n Φ c : ℝ) + 50, lo) ((slotG n Φ c : ℝ) + 50, hi)))
    {ry0 : ℝ} (hRb : ∀ z ∈ R, z.1 ≤ (slotG n Φ c : ℝ) + 52 ∧ ry0 ≤ z.2 ∧ z.2 ≤ ry1) (hry : ry1 < 0)
    (hj : j < (oNooks .addLe).length)
    (hjN : ∀ z : Point, z ∈ (((oNooks .addLe).getD j LR.dflt).real (slotG n Φ c : ℚ) (Hr n Φ)).set ↔
      z.1 = (slotG n Φ c : ℝ) + 30 ∧ bot ≤ z.2 ∧ z.2 ≤ top)
    (hbot : -400 ≤ bot) (htop : top ≤ 0)
    (hsR : ∀ h, bot ≤ h → h ≤ top → ((slotG n Φ c : ℝ) + 30, h) ∈ R)
    (hwall : ∀ w z : Point, w.1 = (slotG n Φ c : ℝ) + 30 → bot < w.2 → w.2 < top →
      z.1 < (slotG n Φ c : ℝ) + 30 → (Polygon.mk ((polyO n Φ).map ratPoint)).Sees z w → False)
    (hin : ∀ m (hm : m < (oTmplInputs .addLe).length), m ≠ m0 → ∀ y d h : ℝ, 0 ≤ y → y ≤ 6 →
      lo ≤ d → d ≤ hi → bot < h → h < top →
      (d - h) * (((oTmplInputs .addLe)[m].lx : ℝ) - 30) ≠ (y - h) * 20)
    (hfar : ∀ x y d h : ℝ, 1070 ≤ x → -140 ≤ y → y ≤ 6 → lo ≤ d → d ≤ hi → bot < h → h < top →
      (d - h) * x ≠ (y - h) * 20)
    (hWR : ∀ y : ℝ, ry0 ≤ y → y ≤ ry1 →
      ¬ ((-447 / 4 ≤ y ∧ y ≤ -431 / 4) ∨ (-539 / 4 ≤ y ∧ y ≤ -523 / 4)))
    (hWd : ∀ y : ℝ, lo ≤ y → y ≤ hi → ¬ ((-447 / 4 ≤ y ∧ y ≤ -431 / 4) ∨ (-539 / 4 ≤ y ∧ y ≤ -523 / 4)))
    (hWc : ∀ x y d h : ℝ, 20 < x → x ≤ 2817 / 128 → lo ≤ d → d ≤ hi → bot < h → h < top →
      (d - h) * x = (y - h) * 20 → ¬ ((-447 / 4 ≤ y ∧ y ≤ -431 / 4) ∨ (-539 / 4 ≤ y ∧ y ≤ -523 / 4)))
    {s : Point} (hs1 : s.1 = (slotG n Φ c : ℝ) + 30) (hs2 : bot < s.2) (hs3 : s.2 < top)
    {X : CIdx n Φ} (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    X = alAux hk ∨ ∃ hm : m0 < (oTmplInputs (cKind (gadAt Φ c))).length, X = inIdx c hm := by
  set g : ℝ := (slotG n Φ c : ℝ) with hg
  have hsR' : s ∈ R := by
    have e : s = (g + 30, s.2) := Prod.ext hs1 rfl
    rw [e]; exact hsR _ hs2.le hs3.le
  have hpvs := fun z (hz : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees z s) =>
    doorPV_of_sees hlo hR hsR' hs1 hz
  have key := addO_excl hΦ A hk (ia := 15) (iW := [16, 17]) (j := j) (m0 := m0) addLe_class hs1
    (by linarith) (by linarith) hj ((hjN s).2 ⟨hs1, hs2.le, hs3.le⟩)
    (fun z hz hs => hwall s z hs1 hs2 hs3 hz hs)
    (fun p hp hex => addLe_exempt p hp j hex)
    (doorPV R g lo hi s.2) (fun z hz _ => hpvs z hz) ?_ ?_ ?_ ?_ hX
  · rcases key with ⟨hi, hXe⟩ | h
    · left; rw [hXe]; rfl
    · right; exact h
  · -- the other inputs of the slot
    intro m hm hm0 y hy0 hy6 hpv
    rcases hpv with hzR | hzD | ⟨hx, d, hd1, hd2, heq⟩
    · have := (hRb _ hzR).2.2; simp only at this; linarith
    · obtain ⟨h1, -, -⟩ := (mem_segment_vert_iff hlo).1 hzD
      simp only at h1
      have := (slotIn_lx c (by rw [hk]; exact hm)).1
      rcases addLe_lx m hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at h1 <;> norm_num at h1 <;>
        linarith
    · simp only at heq
      exact hin m hm hm0 y d s.2 hy0 hy6 hd1 hd2 hs2 hs3 (by rw [← heq]; ring)
  · -- inputs of the slots to the right
    intro z hx hy0 hy6 hpv
    rcases hpv with hzR | hzD | ⟨hx', d, hd1, hd2, heq⟩
    · have := (hRb _ hzR).1; linarith
    · obtain ⟨h1, -, -⟩ := (mem_segment_vert_iff hlo).1 hzD; linarith
    · exact hfar (z.1 - (g + 30)) z.2 d s.2 (by linarith) (by linarith) hy6 hd1 hd2 hs2 hs3 heq
  · -- boxes of the slots to the right
    intro z hx hy0 hy6 hpv
    rcases hpv with hzR | hzD | ⟨hx', d, hd1, hd2, heq⟩
    · have := (hRb _ hzR).1; linarith
    · obtain ⟨h1, -, -⟩ := (mem_segment_vert_iff hlo).1 hzD; linarith
    · exact hfar (z.1 - (g + 30)) z.2 d s.2 (by linarith) hy0 (by linarith) hd1 hd2 hs2 hs3 heq
  · -- the wall helpers of the slot
    intro i hi hiL hs
    have hsp := A.tspot (t := .inr (.inl ⟨c, ⟨i, hiL⟩⟩)) (by simp [tgrp])
    simp only [tinst] at hsp
    set z := A.γ (.inl (.inr (.inl ⟨c, ⟨i, hiL⟩⟩))) with hz
    rw [hk] at hsp
    obtain ⟨hx1, hx2, hy⟩ := addLe_W_pos (n := n) (Φ := Φ) hi hsp
    have e : ((slotG n Φ c : ℚ) : ℝ) = g := by simp only [hg]; push_cast; rfl
    rw [e] at hx1 hx2
    rcases hpvs z hs with hzR | hzD | ⟨hx', d, hd1, hd2, heq⟩
    · exact hWR z.2 (hRb _ hzR).2.1 (hRb _ hzR).2.2 hy
    · obtain ⟨-, h2, h3⟩ := (mem_segment_vert_iff hlo).1 hzD
      exact hWd z.2 h2 h3 hy
    · exact hWc (z.1 - (g + 30)) z.2 d s.2 (by linarith) (by linarith) hd1 hd2 hs2 hs3 heq hy

include hΦ in
/-- **Exclusion for the x-nook of `addLe`.** -/
theorem alO_excl_x {s : Point} (hs1 : s.1 = (slotG n Φ c : ℝ) + 30) (hs2 : -3327 / 32 < s.2)
    (hs3 : s.2 < -6627 / 64) {X : CIdx n Φ}
    (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    X = alAux hk ∨ ∃ hm : 1 < (oTmplInputs (cKind (gadAt Φ c))).length, X = inIdx c hm := by
  refine alO_excl_gen hΦ A hk (R := alOXRoom n Φ c) (j := 0) (by norm_num) (alOX_room c.isLt hk)
    (ry0 := -27411 / 256) (ry1 := -97) (fun z hz => ?_) (by norm_num) (by simp [oNooks])
    (fun z => ?_) (by norm_num) (by norm_num) (fun h h1 h2 => alOX_nookX h1 h2)
    (fun w z h1 h2 h3 h4 h5 => alOX_wall c.isLt hk h1 h2 h3 h4 h5) ?_ ?_ ?_ ?_ ?_ hs1 hs2 hs3 hX
  · have := alOX_bounds hz; norm_num at this ⊢; exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩
  · simp only [oNooks, List.getD_cons_zero, LR.real, AH.ev, Rect.set, mem_ofPred_eq]
    push_cast
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨le_antisymm h2 h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1.ge, h1.le, by linarith, by linarith⟩
  · intro m hm hm0 y d h hy0 hy6 hd1 hd2 hh1 hh2 heq
    rcases addLe_lx m hm with ⟨hl, -⟩ | ⟨-, rfl⟩ | ⟨hl, -⟩
    · rw [hl] at heq; push_cast at heq; linarith
    · exact hm0 rfl
    · rw [hl] at heq; push_cast at heq; linarith
  · intro x y d h hx hy1 hy2 hd1 hd2 hh1 hh2 heq
    nlinarith [mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ d - h)]
  · intro y hy1 hy2 hy; rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  · intro y hy1 hy2 hy; rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  · intro x y d h hx1 hx2 hd1 hd2 hh1 hh2 heq hy
    have : (d - h) * 20 < (y - h) * 20 := by
      rw [← heq]; exact mul_lt_mul_of_pos_left hx1 (by linarith)
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

include hΦ in
/-- **Exclusion for the y-nook of `addLe`.** -/
theorem alO_excl_y {s : Point} (hs1 : s.1 = (slotG n Φ c : ℝ) + 30) (hs2 : -174 < s.2)
    (hs3 : s.2 < -11085 / 64) {X : CIdx n Φ}
    (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    X = alAux hk ∨ ∃ hm : 0 < (oTmplInputs (cKind (gadAt Φ c))).length, X = inIdx c hm := by
  refine alO_excl_gen hΦ A hk (R := alOYRoom n Φ c) (j := 1) (by norm_num) (alOY_room c.isLt hk)
    (ry0 := -363 / 2) (ry1 := -307 / 2) (fun z hz => ?_) (by norm_num) (by simp [oNooks])
    (fun z => ?_) (by norm_num) (by norm_num) (fun h h1 h2 => alOY_nookY h1 h2)
    (fun w z h1 h2 h3 h4 h5 => alOY_wall c.isLt hk h1 h2 h3 h4 h5) ?_ ?_ ?_ ?_ ?_ hs1 hs2 hs3 hX
  · have := alOY_bounds hz; norm_num at this ⊢; exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩
  · simp only [oNooks, List.getD_cons_succ, List.getD_cons_zero, LR.real, AH.ev, Rect.set,
      mem_ofPred_eq]
    push_cast
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨le_antisymm h2 h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1.ge, h1.le, by linarith, by linarith⟩
  · intro m hm hm0 y d h hy0 hy6 hd1 hd2 hh1 hh2 heq
    rcases addLe_lx m hm with ⟨-, rfl⟩ | ⟨hl, -⟩ | ⟨hl, -⟩
    · exact hm0 rfl
    · rw [hl] at heq; push_cast at heq; linarith
    · rw [hl] at heq; push_cast at heq; linarith
  · intro x y d h hx hy1 hy2 hd1 hd2 hh1 hh2 heq
    nlinarith [mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ d - h)]
  · intro y hy1 hy2 hy; rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  · intro y hy1 hy2 hy; rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  · intro x y d h hx1 hx2 hd1 hd2 hh1 hh2 heq hy
    have : (y - h) * 20 ≤ (d - h) * (2817 / 128) := by
      rw [← heq]; exact mul_le_mul_of_nonneg_left hx2 (by linarith)
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

include hΦ in
/-- **Exclusion for the z-nook of `addLe`.** -/
theorem alO_excl_z {s : Point} (hs1 : s.1 = (slotG n Φ c : ℝ) + 30) (hs2 : -3049 / 24 < s.2)
    (hs3 : s.2 < -24335 / 192) {X : CIdx n Φ}
    (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    X = alAux hk ∨ ∃ hm : 2 < (oTmplInputs (cKind (gadAt Φ c))).length, X = inIdx c hm := by
  refine alO_excl_gen hΦ A hk (R := alOZRoom n Φ c) (j := 2) (by norm_num) (alOZ_room c.isLt hk)
    (ry0 := -125189 / 960) (ry1 := -239 / 2) (fun z hz => ?_) (by norm_num) (by simp [oNooks])
    (fun z => ?_) (by norm_num) (by norm_num) (fun h h1 h2 => alOZ_nookZ h1 h2)
    (fun w z h1 h2 h3 h4 h5 => alOZ_wall c.isLt hk h1 h2 h3 h4 h5) ?_ ?_ ?_ ?_ ?_ hs1 hs2 hs3 hX
  · have := alOZ_bounds hz; norm_num at this ⊢; exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩
  · simp only [oNooks, List.getD_cons_succ, List.getD_cons_zero, LR.real, AH.ev, Rect.set,
      mem_ofPred_eq]
    push_cast
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨le_antisymm h2 h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1.ge, h1.le, by linarith, by linarith⟩
  · intro m hm hm0 y d h hy0 hy6 hd1 hd2 hh1 hh2 heq
    rcases addLe_lx m hm with ⟨hl, -⟩ | ⟨hl, -⟩ | ⟨-, rfl⟩
    · rw [hl] at heq; push_cast at heq; linarith
    · rw [hl] at heq; push_cast at heq; linarith
    · exact hm0 rfl
  · intro x y d h hx hy1 hy2 hd1 hd2 hh1 hh2 heq
    nlinarith [mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ d - h)]
  · intro y hy1 hy2 hy; rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  · intro y hy1 hy2 hy; rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  · intro x y d h hx1 hx2 hd1 hd2 hh1 hh2 heq hy
    have hl : (d - h) * 20 < (y - h) * 20 := by
      rw [← heq]; exact mul_lt_mul_of_pos_left hx1 (by linarith)
    have hu : (y - h) * 20 ≤ (d - h) * (2817 / 128) := by
      rw [← heq]; exact mul_le_mul_of_nonneg_left hx2 (by linarith)
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

include hΦ in
/-- **`addLe`: `w_x + w_y ≤ w_z`** for the values of the three input guards of the slot. -/
theorem addLeO_rel
    (hG : (Polygon.mk ((polyO n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point)) :
    A.ival c (al_hm hk 1 (by norm_num)) + A.ival c (al_hm hk 0 (by norm_num)) ≤
      A.ival c (al_hm hk 2 (by norm_num)) := by
  set g : ℝ := (slotG n Φ c : ℝ) with hg
  set a := A.γ (alAux hk)
  obtain ⟨ax1, ax2, ay1, ay2⟩ := A.alAux_pos hk
  have pos : ∀ (m : ℕ) (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length) (lx : ℝ),
      ((oTmplInputs (cKind (gadAt Φ c)))[m].lx : ℝ) = lx →
      inPt (g + lx) (A.ival c hm) = A.γ (inIdx c hm) := by
    intro m hm lx hlx
    have hp := A.inPos c hm
    refine Prod.ext ?_ ?_
    · rw [hp.1, hlx]; simp [hg]
    · simp only [inPt_snd, AssignO.ival]; ring
  have hlx : ∀ (m : ℕ) (hm : m < (oTmplInputs (cKind (gadAt Φ c))).length),
      ((oTmplInputs (cKind (gadAt Φ c)))[m].lx : ℝ) =
        (((oTmplInputs .addLe)[m]'(by rw [← hk]; exact hm)).lx : ℝ) := by
    intro m hm
    have : ∀ (l : List TInput) (hl : l = oTmplInputs .addLe) (h1 : m < l.length),
        (l[m].lx : ℝ) = ((oTmplInputs .addLe)[m]'(hl ▸ h1)).lx := by
      rintro _ rfl _; rfl
    exact this _ (by rw [hk]) hm
  have e1 : inPt (g + 370) (A.ival c (al_hm hk 1 (by norm_num))) = A.γ (inIdx c (al_hm hk 1 (by norm_num))) :=
    pos 1 _ 370 (by rw [hlx]; simp [oTmplInputs])
  have e0 : inPt (g + 210) (A.ival c (al_hm hk 0 (by norm_num))) = A.γ (inIdx c (al_hm hk 0 (by norm_num))) :=
    pos 0 _ 210 (by rw [hlx]; simp [oTmplInputs])
  have e2 : inPt (g + 530) (A.ival c (al_hm hk 2 (by norm_num))) = A.γ (inIdx c (al_hm hk 2 (by norm_num))) :=
    pos 2 _ 530 (by rw [hlx]; simp [oTmplInputs])
  obtain ⟨hx1, hx2⟩ := A.ival_mem c (al_hm hk 1 (by norm_num))
  obtain ⟨hy1, hy2⟩ := A.ival_mem c (al_hm hk 0 (by norm_num))
  obtain ⟨hz1, hz2⟩ := A.ival_mem c (al_hm hk 2 (by norm_num))
  have hbd : ∀ {bot top : ℝ}, bot ≤ top →
      segment ((slotG n Φ c : ℝ) + 30, top) ((slotG n Φ c : ℝ) + 30, bot) ⊆
        (Polygon.mk ((polyO n Φ).map ratPoint)).boundary →
      ∀ h, bot ≤ h → h ≤ top → ((g + 30, h) : Point) ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
    intro bot top hle hseg h h1 h2
    apply hseg
    rw [segment_comm]
    exact (mem_segment_vert_iff hle).2 ⟨rfl, h1, h2⟩
  have guard : ∀ h, ((g + 30, h) : Point) ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).boundary →
      ∃ X : CIdx n Φ, (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) (g + 30, h) := by
    intro h hb
    obtain ⟨q, hqG, hqs⟩ := hG.2 _ hb
    obtain ⟨X, rfl⟩ := A.onto q hqG
    exact ⟨X, hqs⟩
  have hin_out : ∀ (R : Set Point) (ry1 : ℝ), ry1 < 0 → (∀ z ∈ R, z.2 ≤ ry1) →
      ∀ (b v : ℝ), 1 / 2 ≤ v → inPt b v ∉ R := by
    intro R ry1 hry hR b v hv hz
    have := hR _ hz
    simp only [inPt_snd] at this
    linarith
  -- the x-nook
  have cx : ∀ h, -3327 / 32 < h → h < -6627 / 64 →
      vproj a (alOP g) (g + 30) ≤ h ∨ h ≤ alOSx (A.ival c (al_hm hk 1 (by norm_num))) := by
    intro h h1 h2
    obtain ⟨X, hX⟩ := guard h (hbd (by norm_num) (alOX_nook_bd c.isLt hk) h h1.le h2.le)
    have hsR := alOX_nookX (n := n) (Φ := Φ) (c := c.1) h1.le h2.le
    have hRb : ∀ z ∈ alOXRoom n Φ c, z.2 ≤ -97 := fun z hz => (alOX_bounds hz).2.2.2
    rcases alO_excl_x hΦ A hk (s := (g + 30, h)) rfl h1 h2 hX with rfl | ⟨hm, rfl⟩
    · left
      have haR : a ∉ alOXRoom n Φ c := fun haR => by have := hRb _ haR; linarith
      exact (door_bounds_of_sees (by norm_num) (by linarith) (alOX_room c.isLt hk) hsR rfl haR (by linarith) hX).1
    · right
      have hX' : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees
          (inPt (g + 370) (A.ival c (al_hm hk 1 (by norm_num)))) (g + 30, h) := by rw [e1]; exact hX
      have := (door_bounds_of_sees (by norm_num) (by linarith) (alOX_room c.isLt hk) hsR rfl
        (hin_out _ _ (by norm_num) hRb _ _ hx1) (by simp only [inPt_fst]; linarith) hX').2
      rwa [show (((g + 50 : ℝ), (-195 / 2 : ℝ)) : Point) = alON1 g from rfl, alO_shadow_x] at this
  -- the y-nook
  have cy : ∀ h, -174 < h → h < -11085 / 64 →
      vproj a (alOR g) (g + 30) ≤ h ∨ h ≤ alOSy (A.ival c (al_hm hk 0 (by norm_num))) := by
    intro h h1 h2
    obtain ⟨X, hX⟩ := guard h (hbd (by norm_num) (alOY_nook_bd c.isLt hk) h h1.le h2.le)
    have hsR := alOY_nookY (n := n) (Φ := Φ) (c := c.1) h1.le h2.le
    have hRb : ∀ z ∈ alOYRoom n Φ c, z.2 ≤ -307 / 2 := fun z hz => (alOY_bounds hz).2.2.2
    rcases alO_excl_y hΦ A hk (s := (g + 30, h)) rfl h1 h2 hX with rfl | ⟨hm, rfl⟩
    · left
      have haR : a ∉ alOYRoom n Φ c := fun haR => by have := hRb _ haR; linarith
      exact (door_bounds_of_sees (by norm_num) (by linarith) (alOY_room c.isLt hk) hsR rfl haR (by linarith) hX).1
    · right
      have hX' : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees
          (inPt (g + 210) (A.ival c (al_hm hk 0 (by norm_num)))) (g + 30, h) := by rw [e0]; exact hX
      have := (door_bounds_of_sees (by norm_num) (by linarith) (alOY_room c.isLt hk) hsR rfl
        (hin_out _ _ (by norm_num) hRb _ _ hy1) (by simp only [inPt_fst]; linarith) hX').2
      rwa [show (((g + 50 : ℝ), (-154 : ℝ)) : Point) = alON3 g from rfl, alO_shadow_y] at this
  -- the z-nook
  have cz : ∀ h, -3049 / 24 < h → h < -24335 / 192 →
      alOSz (A.ival c (al_hm hk 2 (by norm_num))) ≤ h ∨ h ≤ vproj a (alOQ g) (g + 30) := by
    intro h h1 h2
    obtain ⟨X, hX⟩ := guard h (hbd (by norm_num) (alOZ_nook_bd c.isLt hk) h h1.le h2.le)
    have hsR := alOZ_nookZ (n := n) (Φ := Φ) (c := c.1) h1.le h2.le
    have hRb : ∀ z ∈ alOZRoom n Φ c, z.2 ≤ -239 / 2 := fun z hz => (alOZ_bounds hz).2.2.2
    rcases alO_excl_z hΦ A hk (s := (g + 30, h)) rfl h1 h2 hX with rfl | ⟨hm, rfl⟩
    · right
      have haR : a ∉ alOZRoom n Φ c := fun haR => by have := hRb _ haR; linarith
      exact (door_bounds_of_sees (by norm_num) (by linarith) (alOZ_room c.isLt hk) hsR rfl haR (by linarith) hX).2
    · left
      have hX' : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees
          (inPt (g + 530) (A.ival c (al_hm hk 2 (by norm_num)))) (g + 30, h) := by rw [e2]; exact hX
      have := (door_bounds_of_sees (by norm_num) (by linarith) (alOZ_room c.isLt hk) hsR rfl
        (hin_out _ _ (by norm_num) hRb _ _ hz1) (by simp only [inPt_fst]; linarith) hX').1
      rwa [show (((g + 50 : ℝ), (-6083 / 50 : ℝ)) : Point) = alON2 g from rfl, alO_shadow_z] at this
  refine alO_rel_of_cover_alg (G := g) a hx1 hx2 hy1 hy2 hz1 hz2
    (cover_closed (by norm_num) cx) (cover_closed (by norm_num) cy) (fun h h1 h2 => ?_)
  exact (cover_closed (by norm_num) cz h h1 h2).symm


end Slot

end

end ArtGallery.Orthogonal.Hard
