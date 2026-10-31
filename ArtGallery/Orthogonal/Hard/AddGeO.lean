module

public import ArtGallery.Orthogonal.Hard.AddLeO

/-!
# The `addGe` gadget of the orthogonal construction

In a slot of kind `addGe` (origin `g`), the openings of the nooks are not all on one line:
`N1 = (g + 47, −153/4)` is recessed and `N2 = (g + 65/2, −5977/100)` opens into the bay.  The
rooms (`AddRoomO.lean`): `Y` (door `x = g + 50` between `N3` and `R`), `X` (door `x = g + 47`
from `N1` up), `Z` (door `x = g + 65/2` up to `N2`), and the big room `B` containing the x- and
z-pockets and the bay (door `x = g + 50` between `Q` and `P`).

* `agO_excl_x`, `agO_excl_y`, `agO_excl_z`: a guard seeing an interior point of a nook segment
  is the aux guard or the designated input (for the x- and z-nooks the partial-visibility region
  is cut out by two doors);
* `addGeO_rel`: `w_z ≤ w_x + w_y`.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

variable {n : ℕ} {Φ : List Constraint}

/-! ### Data of the `addGe` slot -/

/-- The witnesses of an `addGe` slot: inputs, helpers, the aux guard (`15`), the wall helpers
`W`, `W2` (`16`, `17`). -/
theorem addGe_class : ∀ i < (slotD .addGe).Ws.length,
    (i % 2 = 0 ∧ i / 2 < (oTmplInputs .addGe).length) ∨ (∃ p ∈ slotSCs .addGe, p.1 = i) ∨
      i = 15 ∨ i ∈ [16, 17] := by
  decide

theorem addGe_spots : (slotD .addGe).sps.getD 15 LR.dflt = ⟨80, 341 / 4, (-129 / 4, 0), (-59 / 4, 0)⟩ ∧
    (slotD .addGe).sps.getD 16 LR.dflt = ⟨6273 / 128, 6529 / 128, (-295 / 4, 0), (-287 / 4, 0)⟩ ∧
    (slotD .addGe).sps.getD 17 LR.dflt =
      ⟨16385 / 512, 16897 / 512, (-4391453 / 102400, 0), (-4289053 / 102400, 0)⟩ := by
  decide +kernel

theorem addGe_exempt : ∀ p ∈ slotSCs .addGe, ∀ j, (p.1, j) ∈ nookExempt .addGe →
    ((slotD .addGe).sps.getD p.1 LR.dflt).x1 < 30 := by
  have h : ∀ p ∈ slotSCs .addGe, ∀ q ∈ nookExempt .addGe, q.1 = p.1 →
      ((slotD .addGe).sps.getD p.1 LR.dflt).x1 < 30 := by decide +kernel
  exact fun p hp j hj => h p hp _ hj rfl

theorem addGe_lx (m : ℕ) (hm : m < (oTmplInputs .addGe).length) :
    ((oTmplInputs .addGe)[m].lx = 185 / 2 ∧ m = 0) ∨ ((oTmplInputs .addGe)[m].lx = 210 ∧ m = 1) ∨
      ((oTmplInputs .addGe)[m].lx = 319 ∧ m = 2) := by
  have : m < 3 := hm
  interval_cases m <;> simp [oTmplInputs]

/-- The partial-visibility region cut out by two vertical doors `x = g + e₁` (inner room `R₁`)
and `x = g + e₂` (outer room `R₂`), for a nook point of height `h` on `x = g + 30`. -/
def door2PV (R₁ R₂ : Set Point) (g e₁ lo₁ hi₁ e₂ lo₂ hi₂ h : ℝ) (z : Point) : Prop :=
  z ∈ R₁ ∨ z ∈ segment (g + e₁, lo₁) (g + e₁, hi₁) ∨
    (g + e₁ < z.1 ∧ (∃ y, lo₁ ≤ y ∧ y ≤ hi₁ ∧ (y - h) * (z.1 - (g + 30)) = (z.2 - h) * (e₁ - 30)) ∧
      (z ∈ R₂ ∨ z ∈ segment (g + e₂, lo₂) (g + e₂, hi₂) ∨
        (g + e₂ < z.1 ∧ ∃ y, lo₂ ≤ y ∧ y ≤ hi₂ ∧ (y - h) * (z.1 - (g + 30)) = (z.2 - h) * (e₂ - 30))))

theorem door2PV_of_sees {P : Polygon} {R₁ R₂ : Set Point} {g e₁ lo₁ hi₁ e₂ lo₂ hi₂ : ℝ}
    (he₁ : 30 < e₁) (he₂ : 30 < e₂) (hlo₁ : lo₁ ≤ hi₁) (hlo₂ : lo₂ ≤ hi₂)
    (hR₁ : P.IsRoom R₁ (segment (g + e₁, lo₁) (g + e₁, hi₁)))
    (hR₂ : P.IsRoom R₂ (segment (g + e₂, lo₂) (g + e₂, hi₂))) {s : Point} (hs₁ : s ∈ R₁)
    (hs₂ : s ∈ R₂) (hs1 : s.1 = g + 30) {z : Point} (hz : P.Sees z s) :
    door2PV R₁ R₂ g e₁ lo₁ hi₁ e₂ lo₂ hi₂ s.2 z := by
  by_cases hz₁ : z ∈ R₁
  · exact Or.inl hz₁
  right
  rcases door_viewer hR₁ hlo₁ (by linarith) hs₁ hs1 hz₁ hz with h | ⟨h1, y, hy1, hy2, heq⟩
  · exact Or.inl h
  right
  refine ⟨h1, ⟨y, hy1, hy2, by rw [heq]; ring⟩, ?_⟩
  by_cases hz₂ : z ∈ R₂
  · exact Or.inl hz₂
  right
  rcases door_viewer hR₂ hlo₂ (by linarith) hs₂ hs1 hz₂ hz with h | ⟨h2, y', hy1', hy2', heq'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h2, y', hy1', hy2', by rw [heq']; ring⟩

section Slot

variable (hΦ : ∀ c ∈ Φ, c.VarsLt n) {G : Finset Point} (A : AssignO n Φ G)
  {c : Fin (paramC Φ)} (hk : cKind (gadAt Φ c) = .addGe)

include hk in
theorem ag_ia : 15 < (slotWs (cKind (gadAt Φ c))).length := by rw [hk]; decide

include hk in
theorem ag_hm (m : ℕ) (hm : m < 3) : m < (oTmplInputs (cKind (gadAt Φ c))).length := by
  rw [hk]; exact hm

/-- The aux guard of an `addGe` slot. -/
def agAux (hk : cKind (gadAt Φ c) = .addGe) : CIdx n Φ := .inl (.inr (.inl ⟨c, ⟨15, ag_ia hk⟩⟩))

include hk in
theorem AssignO.agAux_pos : (slotG n Φ c : ℝ) + 80 ≤ (A.γ (agAux hk)).1 ∧
    (A.γ (agAux hk)).1 ≤ (slotG n Φ c : ℝ) + 341 / 4 ∧ -129 / 4 ≤ (A.γ (agAux hk)).2 ∧
    (A.γ (agAux hk)).2 ≤ -59 / 4 := by
  have hsp := A.tspot (t := .inr (.inl ⟨c, ⟨15, ag_ia hk⟩⟩)) (by simp [tgrp])
  simp only [tinst] at hsp
  have e : (slotD (cKind (gadAt Φ c))).sps.getD 15 LR.dflt = ⟨80, 341 / 4, (-129 / 4, 0), (-59 / 4, 0)⟩ := by
    rw [hk]; exact addGe_spots.1
  rw [e] at hsp
  obtain ⟨h1, h2, h3, h4⟩ := hsp
  simp only [LR.real, AH.ev] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  simp only [agAux]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

include hk in
/-- The spots of the wall helpers of an `addGe` slot, as bounds. -/
theorem AssignO.agW_pos (i : ℕ) (hi : i ∈ [16, 17]) (hiL : i < (slotWs (cKind (gadAt Φ c))).length) :
    let z := A.γ (.inl (.inr (.inl ⟨c, ⟨i, hiL⟩⟩)))
    ((slotG n Φ c : ℝ) + 6273 / 128 ≤ z.1 ∧ z.1 ≤ (slotG n Φ c : ℝ) + 6529 / 128 ∧ -295 / 4 ≤ z.2 ∧ z.2 ≤ -287 / 4) ∨
      ((slotG n Φ c : ℝ) + 32 ≤ z.1 ∧ z.1 ≤ (slotG n Φ c : ℝ) + 16897 / 512 ∧
        -4391453 / 102400 ≤ z.2 ∧ z.2 ≤ -4289053 / 102400) := by
  intro z
  have hsp := A.tspot (t := .inr (.inl ⟨c, ⟨i, hiL⟩⟩)) (by simp [tgrp])
  simp only [tinst] at hsp
  have hz : z ∈ (((slotD .addGe).sps.getD i LR.dflt).real (slotG n Φ c : ℚ) (Hr n Φ)).set := by
    have e2 : (slotD (cKind (gadAt Φ c))).sps.getD i LR.dflt = (slotD .addGe).sps.getD i LR.dflt := by
      rw [hk]
    rw [e2] at hsp; exact hsp
  obtain ⟨-, e16, e17⟩ := addGe_spots
  have e : ((slotG n Φ c : ℚ) : ℝ) = (slotG n Φ c : ℝ) := by push_cast; rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · rw [e16] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    simp only [LR.real, AH.ev, e] at h1 h2 h3 h4
    norm_num at h1 h2 h3 h4
    left; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [e17] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    simp only [LR.real, AH.ev, e] at h1 h2 h3 h4
    norm_num at h1 h2 h3 h4
    right; exact ⟨by linarith, by linarith, by linarith, by linarith⟩

include hΦ in
/-- **Exclusion for an `addGe` nook** (generic, two doors). -/
theorem agO_excl_gen {R₁ R₂ : Set Point} {e₁ lo₁ hi₁ e₂ lo₂ hi₂ bot top : ℝ} {j m0 : ℕ}
    (he₁ : 30 < e₁) (he₂ : e₁ ≤ e₂) (he₃ : e₂ < 185 / 2) (hlo₁ : lo₁ ≤ hi₁) (hlo₂ : lo₂ ≤ hi₂)
    (hR₁ : (Polygon.mk ((polyO n Φ).map ratPoint)).IsRoom R₁
      (segment ((slotG n Φ c : ℝ) + e₁, lo₁) ((slotG n Φ c : ℝ) + e₁, hi₁)))
    (hR₂ : (Polygon.mk ((polyO n Φ).map ratPoint)).IsRoom R₂
      (segment ((slotG n Φ c : ℝ) + e₂, lo₂) ((slotG n Φ c : ℝ) + e₂, hi₂)))
    (hRb₁ : ∀ z ∈ R₁, z.1 ≤ (slotG n Φ c : ℝ) + 52 ∧ z.2 ≤ -73 / 2)
    (hRb₂ : ∀ z ∈ R₂, z.1 ≤ (slotG n Φ c : ℝ) + 52 ∧ z.2 ≤ -73 / 2)
    (hj : j < (oNooks .addGe).length)
    (hjN : ∀ z : Point, z ∈ (((oNooks .addGe).getD j LR.dflt).real (slotG n Φ c : ℚ) (Hr n Φ)).set ↔
      z.1 = (slotG n Φ c : ℝ) + 30 ∧ bot ≤ z.2 ∧ z.2 ≤ top)
    (hbot : -400 ≤ bot) (htop : top ≤ 0)
    (hsR₁ : ∀ h, bot ≤ h → h ≤ top → ((slotG n Φ c : ℝ) + 30, h) ∈ R₁)
    (hsR₂ : ∀ h, bot ≤ h → h ≤ top → ((slotG n Φ c : ℝ) + 30, h) ∈ R₂)
    (hwall : ∀ w z : Point, w.1 = (slotG n Φ c : ℝ) + 30 → bot < w.2 → w.2 < top →
      z.1 < (slotG n Φ c : ℝ) + 30 → (Polygon.mk ((polyO n Φ).map ratPoint)).Sees z w → False)
    (hin : ∀ m (hm : m < (oTmplInputs .addGe).length), m ≠ m0 → ∀ y d₁ d₂ h : ℝ, 0 ≤ y → y ≤ 6 →
      lo₁ ≤ d₁ → d₁ ≤ hi₁ → lo₂ ≤ d₂ → d₂ ≤ hi₂ → bot < h → h < top →
      (d₁ - h) * (((oTmplInputs .addGe)[m].lx : ℝ) - 30) = (y - h) * (e₁ - 30) →
      (d₂ - h) * (((oTmplInputs .addGe)[m].lx : ℝ) - 30) = (y - h) * (e₂ - 30) → False)
    (hfar : ∀ x y d₁ d₂ h : ℝ, 1070 ≤ x → -140 ≤ y → y ≤ 6 → lo₁ ≤ d₁ → d₁ ≤ hi₁ → lo₂ ≤ d₂ →
      d₂ ≤ hi₂ → bot < h → h < top → (d₁ - h) * x = (y - h) * (e₁ - 30) →
      (d₂ - h) * x = (y - h) * (e₂ - 30) → False)
    (hW : ∀ h, bot < h → h < top → ∀ z : Point,
      (((slotG n Φ c : ℝ) + 6273 / 128 ≤ z.1 ∧ z.1 ≤ (slotG n Φ c : ℝ) + 6529 / 128 ∧ -295 / 4 ≤ z.2 ∧ z.2 ≤ -287 / 4) ∨
        ((slotG n Φ c : ℝ) + 32 ≤ z.1 ∧ z.1 ≤ (slotG n Φ c : ℝ) + 16897 / 512 ∧
          -4391453 / 102400 ≤ z.2 ∧ z.2 ≤ -4289053 / 102400)) →
      ¬ door2PV R₁ R₂ (slotG n Φ c : ℝ) e₁ lo₁ hi₁ e₂ lo₂ hi₂ h z)
    {s : Point} (hs1 : s.1 = (slotG n Φ c : ℝ) + 30) (hs2 : bot < s.2) (hs3 : s.2 < top)
    {X : CIdx n Φ} (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    X = agAux hk ∨ ∃ hm : m0 < (oTmplInputs (cKind (gadAt Φ c))).length, X = inIdx c hm := by
  set g : ℝ := (slotG n Φ c : ℝ) with hg
  have hs₁ : s ∈ R₁ := by
    have e : s = (g + 30, s.2) := Prod.ext hs1 rfl
    rw [e]; exact hsR₁ _ hs2.le hs3.le
  have hs₂ : s ∈ R₂ := by
    have e : s = (g + 30, s.2) := Prod.ext hs1 rfl
    rw [e]; exact hsR₂ _ hs2.le hs3.le
  have hpvs := fun z (hz : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees z s) =>
    door2PV_of_sees he₁ (by linarith) hlo₁ hlo₂ hR₁ hR₂ hs₁ hs₂ hs1 hz
  -- a point far right, or an input, beyond both doors
  have beyond : ∀ z : Point, g + e₂ < z.1 → -36 ≤ z.2 ∨ g + 52 < z.1 →
      door2PV R₁ R₂ g e₁ lo₁ hi₁ e₂ lo₂ hi₂ s.2 z →
      (∃ y, lo₁ ≤ y ∧ y ≤ hi₁ ∧ (y - s.2) * (z.1 - (g + 30)) = (z.2 - s.2) * (e₁ - 30)) ∧
        ∃ y, lo₂ ≤ y ∧ y ≤ hi₂ ∧ (y - s.2) * (z.1 - (g + 30)) = (z.2 - s.2) * (e₂ - 30) := by
    intro z hz1 hz2 hpv
    have nR : ∀ R : Set Point, (∀ z ∈ R, z.1 ≤ g + 52 ∧ z.2 ≤ -73 / 2) → z ∉ R := by
      intro R hRb hzR
      have := hRb _ hzR
      rcases hz2 with h | h <;> linarith [this.1, this.2]
    rcases hpv with h1 | h1 | ⟨-, hc1, h2⟩
    · exact absurd h1 (nR _ hRb₁)
    · obtain ⟨h, -, -⟩ := (mem_segment_vert_iff hlo₁).1 h1; linarith
    rcases h2 with h2 | h2 | ⟨-, hc2⟩
    · exact absurd h2 (nR _ hRb₂)
    · obtain ⟨h, -, -⟩ := (mem_segment_vert_iff hlo₂).1 h2; linarith
    · exact ⟨hc1, hc2⟩
  have key := addO_excl hΦ A hk (ia := 15) (iW := [16, 17]) (j := j) (m0 := m0) addGe_class hs1
    (by linarith) (by linarith) hj ((hjN s).2 ⟨hs1, hs2.le, hs3.le⟩)
    (fun z hz hs => hwall s z hs1 hs2 hs3 hz hs)
    (fun p hp hex => addGe_exempt p hp j hex)
    (door2PV R₁ R₂ g e₁ lo₁ hi₁ e₂ lo₂ hi₂ s.2) (fun z hz _ => hpvs z hz) ?_ ?_ ?_ ?_ hX
  · rcases key with ⟨hi, hXe⟩ | h
    · left; rw [hXe]; rfl
    · right; exact h
  · -- the other inputs of the slot
    intro m hm hm0 y hy0 hy6 hpv
    have hl : (185 / 2 : ℝ) ≤ ((oTmplInputs .addGe)[m].lx : ℝ) := by
      rcases addGe_lx m hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> norm_num
    obtain ⟨⟨d₁, hd1, hd2, hq1⟩, ⟨d₂, hd3, hd4, hq2⟩⟩ := beyond _ (by simp only; linarith)
      (Or.inl (by simp only; linarith)) hpv
    simp only at hq1 hq2
    exact hin m hm hm0 y d₁ d₂ s.2 hy0 hy6 hd1 hd2 hd3 hd4 hs2 hs3
      (by linear_combination hq1 + (d₁ - s.2) * hg) (by linear_combination hq2 + (d₂ - s.2) * hg)
  · -- inputs of the slots to the right
    intro z hx hy0 hy6 hpv
    obtain ⟨⟨d₁, hd1, hd2, hq1⟩, ⟨d₂, hd3, hd4, hq2⟩⟩ := beyond z (by linarith) (Or.inr (by linarith)) hpv
    exact hfar (z.1 - (g + 30)) z.2 d₁ d₂ s.2 (by linarith) (by linarith) hy6 hd1 hd2 hd3 hd4 hs2 hs3
      hq1 hq2
  · -- boxes of the slots to the right
    intro z hx hy0 hy6 hpv
    obtain ⟨⟨d₁, hd1, hd2, hq1⟩, ⟨d₂, hd3, hd4, hq2⟩⟩ := beyond z (by linarith) (Or.inr (by linarith)) hpv
    exact hfar (z.1 - (g + 30)) z.2 d₁ d₂ s.2 (by linarith) hy0 (by linarith) hd1 hd2 hd3 hd4 hs2 hs3
      hq1 hq2
  · -- the wall helpers of the slot
    intro i hi hiL hs
    exact hW s.2 hs2 hs3 _ (A.agW_pos hk i hi hiL) (hpvs _ hs)

include hΦ in
/-- **Exclusion for the x-nook of `addGe`.** -/
theorem agO_excl_x {s : Point} (hs1 : s.1 = (slotG n Φ c : ℝ) + 30) (hs2 : -2649 / 64 < s.2)
    (hs3 : s.2 < -2595 / 64) {X : CIdx n Φ}
    (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    X = agAux hk ∨ ∃ hm : 2 < (oTmplInputs (cKind (gadAt Φ c))).length, X = inIdx c hm := by
  refine agO_excl_gen hΦ A hk (R₁ := agOXRoom n Φ c) (R₂ := agOBRoom n Φ c) (j := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (agOX_room c.isLt hk) (agOB_room c.isLt hk)
    (fun z hz => by obtain ⟨-, h2, -, h4⟩ := agOX_bounds hz; exact ⟨by linarith, by linarith⟩)
    (fun z hz => by obtain ⟨-, h2, -, h4⟩ := agOB_bounds hz; exact ⟨by linarith, by linarith⟩)
    (by simp [oNooks]) (fun z => ?_) (by norm_num) (by norm_num)
    (fun h h1 h2 => agOX_nookX h1 h2) (fun h h1 h2 => agOB_nookX h1 h2)
    (fun w z h1 h2 h3 h4 h5 => agOX_wall c.isLt hk h1 h2 h3 h4 h5) ?_ ?_ ?_ hs1 hs2 hs3 hX
  · simp only [oNooks, List.getD_cons_zero, LR.real, AH.ev, Rect.set, mem_ofPred_eq]
    push_cast
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨le_antisymm h2 h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1.ge, h1.le, by linarith, by linarith⟩
  · intro m hm hm0 y d₁ d₂ h hy0 hy6 hd1 hd2 hd3 hd4 hh1 hh2 hq1 hq2
    rcases addGe_lx m hm with ⟨hl, -⟩ | ⟨hl, -⟩ | ⟨-, rfl⟩
    · rw [hl] at hq2; push_cast at hq2; linarith
    · rw [hl] at hq2; push_cast at hq2; linarith
    · exact hm0 rfl
  · intro x y d₁ d₂ h hx hy1 hy2 hd1 hd2 hd3 hd4 hh1 hh2 hq1 hq2
    nlinarith [mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ d₁ - h)]
  · intro h hh1 hh2 z hz hpv
    rcases hpv with hR | hD | ⟨hb, ⟨d₁, hd1, hd2, hq1⟩, -⟩
    · obtain ⟨-, b2, b3, b4⟩ := agOX_bounds hR
      rcases hz with ⟨-, -, -, h4⟩ | ⟨-, -, -, h4⟩ <;> linarith
    · obtain ⟨h1, -, -⟩ := (mem_segment_vert_iff (by norm_num)).1 hD
      rcases hz with ⟨h5, -, -, -⟩ | ⟨-, h5, -, -⟩ <;> linarith
    · rcases hz with ⟨h5, h6, h7, h8⟩ | ⟨-, h6, -, -⟩
      · have : 0 < (d₁ - h) * (z.1 - ((slotG n Φ c : ℝ) + 30)) :=
          mul_pos (by linarith) (by linarith)
        linarith
      · linarith

include hΦ in
/-- **Exclusion for the y-nook of `addGe`.** -/
theorem agO_excl_y {s : Point} (hs1 : s.1 = (slotG n Φ c : ℝ) + 30) (hs2 : -855 / 8 < s.2)
    (hs3 : s.2 < -3381 / 32) {X : CIdx n Φ}
    (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    X = agAux hk ∨ ∃ hm : 1 < (oTmplInputs (cKind (gadAt Φ c))).length, X = inIdx c hm := by
  refine agO_excl_gen hΦ A hk (R₁ := agOYRoom n Φ c) (R₂ := agOYRoom n Φ c) (j := 1)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
    (agOY_room c.isLt hk) (agOY_room c.isLt hk)
    (fun z hz => by obtain ⟨-, h2, -, h4⟩ := agOY_bounds hz; exact ⟨by linarith, by linarith⟩)
    (fun z hz => by obtain ⟨-, h2, -, h4⟩ := agOY_bounds hz; exact ⟨by linarith, by linarith⟩)
    (by simp [oNooks]) (fun z => ?_) (by norm_num) (by norm_num)
    (fun h h1 h2 => agOY_nookY h1 h2) (fun h h1 h2 => agOY_nookY h1 h2)
    (fun w z h1 h2 h3 h4 h5 => agOY_wall c.isLt hk h1 h2 h3 h4 h5) ?_ ?_ ?_ hs1 hs2 hs3 hX
  · simp only [oNooks, List.getD_cons_succ, List.getD_cons_zero, LR.real, AH.ev, Rect.set,
      mem_ofPred_eq]
    push_cast
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨le_antisymm h2 h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1.ge, h1.le, by linarith, by linarith⟩
  · intro m hm hm0 y d₁ d₂ h hy0 hy6 hd1 hd2 hd3 hd4 hh1 hh2 hq1 hq2
    rcases addGe_lx m hm with ⟨hl, -⟩ | ⟨-, rfl⟩ | ⟨hl, -⟩
    · rw [hl] at hq1; push_cast at hq1; linarith
    · exact hm0 rfl
    · rw [hl] at hq1; push_cast at hq1; linarith
  · intro x y d₁ d₂ h hx hy1 hy2 hd1 hd2 hd3 hd4 hh1 hh2 hq1 hq2
    nlinarith [mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ d₁ - h)]
  · intro h hh1 hh2 z hz hpv
    rcases hpv with hR | hD | ⟨hb, ⟨d₁, hd1, hd2, hq1⟩, -⟩
    · obtain ⟨-, b2, b3, b4⟩ := agOY_bounds hR
      rcases hz with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ <;> linarith
    · obtain ⟨-, h2, h3⟩ := (mem_segment_vert_iff (by norm_num)).1 hD
      rcases hz with ⟨-, -, h7, -⟩ | ⟨-, -, h7, -⟩ <;> linarith
    · rcases hz with ⟨h5, h6, h7, h8⟩ | ⟨-, h6, -, -⟩
      · have hu : (d₁ - h) * (z.1 - ((slotG n Φ c : ℝ) + 30)) ≤ (d₁ - h) * (6529 / 128 - 30) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
      · linarith

include hΦ in
/-- **Exclusion for the z-nook of `addGe`.** -/
theorem agO_excl_z {s : Point} (hs1 : s.1 = (slotG n Φ c : ℝ) + 30) (hs2 : -6001 / 96 < s.2)
    (hs3 : s.2 < -2975 / 48) {X : CIdx n Φ}
    (hX : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (A.γ X) s) :
    X = agAux hk ∨ ∃ hm : 0 < (oTmplInputs (cKind (gadAt Φ c))).length, X = inIdx c hm := by
  refine agO_excl_gen hΦ A hk (R₁ := agOZRoom n Φ c) (R₂ := agOBRoom n Φ c) (j := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (agOZ_room c.isLt hk) (agOB_room c.isLt hk)
    (fun z hz => by obtain ⟨-, h2, -, h4⟩ := agOZ_bounds hz; exact ⟨by linarith, by linarith⟩)
    (fun z hz => by obtain ⟨-, h2, -, h4⟩ := agOB_bounds hz; exact ⟨by linarith, by linarith⟩)
    (by simp [oNooks]) (fun z => ?_) (by norm_num) (by norm_num)
    (fun h h1 h2 => agOZ_nookZ h1 h2) (fun h h1 h2 => agOB_nookZ h1 h2)
    (fun w z h1 h2 h3 h4 h5 => agOZ_wall c.isLt hk h1 h2 h3 h4 h5) ?_ ?_ ?_ hs1 hs2 hs3 hX
  · simp only [oNooks, List.getD_cons_succ, List.getD_cons_zero, LR.real, AH.ev, Rect.set,
      mem_ofPred_eq]
    push_cast
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨le_antisymm h2 h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1.ge, h1.le, by linarith, by linarith⟩
  · intro m hm hm0 y d₁ d₂ h hy0 hy6 hd1 hd2 hd3 hd4 hh1 hh2 hq1 hq2
    rcases addGe_lx m hm with ⟨-, rfl⟩ | ⟨hl, -⟩ | ⟨hl, -⟩
    · exact hm0 rfl
    · rw [hl] at hq2; push_cast at hq2; linarith
    · rw [hl] at hq2; push_cast at hq2; linarith
  · intro x y d₁ d₂ h hx hy1 hy2 hd1 hd2 hd3 hd4 hh1 hh2 hq1 hq2
    nlinarith [mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ d₂ - h)]
  · intro h hh1 hh2 z hz hpv
    rcases hpv with hR | hD | ⟨hb, ⟨d₁, hd1, hd2, hq1⟩, hpv2⟩
    · obtain ⟨-, b2, b3, b4⟩ := agOZ_bounds hR
      rcases hz with ⟨h5, -, -, -⟩ | ⟨-, -, h7, -⟩ <;> linarith
    · obtain ⟨h1, h2, h3⟩ := (mem_segment_vert_iff (by norm_num)).1 hD
      rcases hz with ⟨h5, -, -, -⟩ | ⟨-, -, h7, -⟩ <;> linarith
    · rcases hz with ⟨h5, h6, h7, h8⟩ | ⟨h5, h6, h7, h8⟩
      · rcases hpv2 with hR | hD | ⟨-, d₂, hd3, hd4, hq2⟩
        · obtain ⟨-, -, b3, -⟩ := agOB_bounds hR; linarith
        · obtain ⟨-, h2, h3⟩ := (mem_segment_vert_iff (by norm_num)).1 hD; linarith
        · have : 0 < (d₂ - h) * (z.1 - ((slotG n Φ c : ℝ) + 30)) :=
            mul_pos (by linarith) (by linarith)
          linarith
      · have u1 : (d₁ - h) * (z.1 - ((slotG n Φ c : ℝ) + 30)) ≤
            (-5977 / 100 - h) * (z.1 - ((slotG n Φ c : ℝ) + 30)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have u2 : (-5977 / 100 - h) * (z.1 - ((slotG n Φ c : ℝ) + 30)) ≤
            (-5977 / 100 - h) * (16897 / 512 - 30) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith

include hΦ in
/-- **`addGe`: `w_z ≤ w_x + w_y`** for the values of the three input guards of the slot. -/
theorem addGeO_rel
    (hG : (Polygon.mk ((polyO n Φ).map ratPoint)).IsBoundaryGuardSet (G : Set Point)) :
    A.ival c (ag_hm hk 0 (by norm_num)) ≤
      A.ival c (ag_hm hk 2 (by norm_num)) + A.ival c (ag_hm hk 1 (by norm_num)) := by
  set g : ℝ := (slotG n Φ c : ℝ) with hg
  set a := A.γ (agAux hk)
  obtain ⟨ax1, ax2, ay1, ay2⟩ := A.agAux_pos hk
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
        (((oTmplInputs .addGe)[m]'(by rw [← hk]; exact hm)).lx : ℝ) := by
    intro m hm
    have : ∀ (l : List TInput) (hl : l = oTmplInputs .addGe) (h1 : m < l.length),
        (l[m].lx : ℝ) = ((oTmplInputs .addGe)[m]'(hl ▸ h1)).lx := by
      rintro _ rfl _; rfl
    exact this _ (by rw [hk]) hm
  have e0 : inPt (g + 185 / 2) (A.ival c (ag_hm hk 0 (by norm_num))) =
      A.γ (inIdx c (ag_hm hk 0 (by norm_num))) := pos 0 _ (185 / 2) (by rw [hlx]; simp [oTmplInputs])
  have e1 : inPt (g + 210) (A.ival c (ag_hm hk 1 (by norm_num))) =
      A.γ (inIdx c (ag_hm hk 1 (by norm_num))) := pos 1 _ 210 (by rw [hlx]; simp [oTmplInputs])
  have e2 : inPt (g + 319) (A.ival c (ag_hm hk 2 (by norm_num))) =
      A.γ (inIdx c (ag_hm hk 2 (by norm_num))) := pos 2 _ 319 (by rw [hlx]; simp [oTmplInputs])
  obtain ⟨hz1, hz2⟩ := A.ival_mem c (ag_hm hk 0 (by norm_num))
  obtain ⟨hy1, hy2⟩ := A.ival_mem c (ag_hm hk 1 (by norm_num))
  obtain ⟨hx1, hx2⟩ := A.ival_mem c (ag_hm hk 2 (by norm_num))
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
  have out : ∀ (R : Set Point), (∀ z ∈ R, z.2 ≤ -73 / 2) → ∀ z : Point, -36 ≤ z.2 → z ∉ R := by
    intro R hR z hz hzR; have := hR _ hzR; linarith
  have hinY : ∀ (b v : ℝ), 1 / 2 ≤ v → -36 ≤ (inPt b v).2 := by
    intro b v hv; simp only [inPt_snd]; linarith
  -- the x-nook
  have cx : ∀ h, -2649 / 64 < h → h < -2595 / 64 →
      agOSx (A.ival c (ag_hm hk 2 (by norm_num))) ≤ h ∨ h ≤ vproj a (agOP g) (g + 30) := by
    intro h h1 h2
    obtain ⟨X, hX⟩ := guard h (hbd (by norm_num) (agOX_nook_bd c.isLt hk) h h1.le h2.le)
    rcases agO_excl_x hΦ A hk (s := (g + 30, h)) rfl h1 h2 hX with rfl | ⟨hm, rfl⟩
    · right
      have hR := fun (z : Point) (hz : z ∈ agOBRoom n Φ c.1) =>
        (agOB_bounds (n := n) (Φ := Φ) (c := c.1) hz).2.2.2
      exact (door_bounds_of_sees (by norm_num) (by linarith) (agOB_room c.isLt hk)
        (agOB_nookX h1.le h2.le) rfl (out _ hR a (by linarith)) (by linarith) hX).2
    · left
      have hX' : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees
          (inPt (g + 319) (A.ival c (ag_hm hk 2 (by norm_num)))) (g + 30, h) := by rw [e2]; exact hX
      have hR := fun (z : Point) (hz : z ∈ agOXRoom n Φ c.1) =>
        (agOX_bounds (n := n) (Φ := Φ) (c := c.1) hz).2.2.2
      have := (door_bounds_of_sees (by norm_num) (by linarith) (agOX_room c.isLt hk)
        (agOX_nookX h1.le h2.le) rfl (out _ hR _ (hinY _ _ hx1)) (by simp only [inPt_fst]; linarith) hX').1
      rwa [show (((g + 47 : ℝ), (-153 / 4 : ℝ)) : Point) = agON1 g from rfl, agO_shadow_x] at this
  -- the y-nook
  have cy : ∀ h, -855 / 8 < h → h < -3381 / 32 →
      agOSy (A.ival c (ag_hm hk 1 (by norm_num))) ≤ h ∨ h ≤ vproj a (agOR g) (g + 30) := by
    intro h h1 h2
    obtain ⟨X, hX⟩ := guard h (hbd (by norm_num) (agOY_nook_bd c.isLt hk) h h1.le h2.le)
    have hR := fun (z : Point) (hz : z ∈ agOYRoom n Φ c.1) =>
        (agOY_bounds (n := n) (Φ := Φ) (c := c.1) hz).2.2.2
    rcases agO_excl_y hΦ A hk (s := (g + 30, h)) rfl h1 h2 hX with rfl | ⟨hm, rfl⟩
    · right
      exact (door_bounds_of_sees (by norm_num) (by linarith) (agOY_room c.isLt hk)
        (agOY_nookY h1.le h2.le) rfl (out _ (fun z hz => by linarith [hR z hz]) a (by linarith))
        (by linarith) hX).2
    · left
      have hX' : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees
          (inPt (g + 210) (A.ival c (ag_hm hk 1 (by norm_num)))) (g + 30, h) := by rw [e1]; exact hX
      have := (door_bounds_of_sees (by norm_num) (by linarith) (agOY_room c.isLt hk)
        (agOY_nookY h1.le h2.le) rfl (out _ (fun z hz => by linarith [hR z hz]) _ (hinY _ _ hy1))
        (by simp only [inPt_fst]; linarith) hX').1
      rwa [show (((g + 50 : ℝ), (-94 : ℝ)) : Point) = agON3 g from rfl, agO_shadow_y] at this
  -- the z-nook
  have cz : ∀ h, -6001 / 96 < h → h < -2975 / 48 →
      vproj a (agOQ g) (g + 30) ≤ h ∨ h ≤ agOSz (A.ival c (ag_hm hk 0 (by norm_num))) := by
    intro h h1 h2
    obtain ⟨X, hX⟩ := guard h (hbd (by norm_num) (agOZ_nook_bd c.isLt hk) h h1.le h2.le)
    rcases agO_excl_z hΦ A hk (s := (g + 30, h)) rfl h1 h2 hX with rfl | ⟨hm, rfl⟩
    · left
      have hR := fun (z : Point) (hz : z ∈ agOBRoom n Φ c.1) =>
        (agOB_bounds (n := n) (Φ := Φ) (c := c.1) hz).2.2.2
      exact (door_bounds_of_sees (by norm_num) (by linarith) (agOB_room c.isLt hk)
        (agOB_nookZ h1.le h2.le) rfl (out _ hR a (by linarith)) (by linarith) hX).1
    · right
      have hX' : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees
          (inPt (g + 185 / 2) (A.ival c (ag_hm hk 0 (by norm_num)))) (g + 30, h) := by rw [e0]; exact hX
      have hR := fun (z : Point) (hz : z ∈ agOZRoom n Φ c.1) =>
        (agOZ_bounds (n := n) (Φ := Φ) (c := c.1) hz).2.2.2
      have := (door_bounds_of_sees (by norm_num) (by linarith) (agOZ_room c.isLt hk)
        (agOZ_nookZ h1.le h2.le) rfl (out _ (fun z hz => by linarith [hR z hz]) _ (hinY _ _ hz1))
        (by simp only [inPt_fst]; linarith) hX').2
      rwa [show (((g + 65 / 2 : ℝ), (-5977 / 100 : ℝ)) : Point) = agON2 g from rfl, agO_shadow_z] at this
  refine agO_rel_of_cover_alg (G := g) a hx1 hx2 hy1 hy2 hz1 hz2 (fun h h1 h2 => ?_)
    (fun h h1 h2 => ?_) (cover_closed (by norm_num) cz)
  · exact (cover_closed (by norm_num) cx h h1 h2).symm
  · exact (cover_closed (by norm_num) cy h h1 h2).symm

end Slot

end

end ArtGallery.Orthogonal.Hard
