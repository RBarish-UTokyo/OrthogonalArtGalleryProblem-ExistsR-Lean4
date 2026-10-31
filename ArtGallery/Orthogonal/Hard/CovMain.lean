module

public import ArtGallery.Orthogonal.Hard.CovVarO
public import ArtGallery.Orthogonal.Hard.CovBasinO
public import ArtGallery.Orthogonal.Hard.CovAddO
public import ArtGallery.Orthogonal.Hard.CovNookO

/-!
# Completeness (b): a solution gives a guard set of `guardsO n Φ` points

The canonical guards `canonO v` (one per counting index) see the whole region: every point is in
a zone of a group (variable, basin, slot), in a copy nook, or in the band, and each case is
covered (`var_cover`, `basin_cover`, `slot_cover`, `nookI_cover`, `band_seen`).  The canonical
guards in the region, padded with further points of the region, form a guard set of exactly
`guardsO n Φ` points.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

/-- The certificate and pockets of a slot kind. -/
def slotCov : TKind → GroupCov × List PocketD
  | .invGe => (gCovInvGe, invGePockets)
  | .invRevLe => (gCovInvRevLe, invRevLePockets)
  | .addLe => (gCovAddLe, addLePockets)
  | .addGe => (gCovAddGe, addGePockets)

theorem slotCov_facts (k : TKind) : SlotFacts k (slotCov k).1 (slotCov k).2 := by
  cases k
  · exact invGe_facts
  · exact invRevLe_facts
  · exact addLe_facts
  · exact addGe_facts

theorem slotCov_spec {v : ℕ → ℝ} (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v)
    (c : Fin (paramC Φ)) :
    ∀ p ∈ (slotCov (cKind (gadAt Φ c))).2, p.Spec ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ)
      (canonSlot (n := n) v c p.a) (canonSlot (n := n) v c p.b) := by
  generalize hk : cKind (gadAt Φ c) = k
  cases k
  · exact invGe_spec hv hsol c hk
  · exact invRevLe_spec hv hsol c hk
  · exact addLe_spec hv hsol c hk
  · exact addGe_spec hv hsol c hk

/-- A slot group with its own certificate. -/
theorem slot_cover' (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {v : ℕ → ℝ}
    (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v) (c : Fin (paramC Φ))
    {g : GZ} (hg : g ∈ slotZ (cKind (gadAt Φ c))) {l : LR} (hl : l ∈ g.rects) {z : Point}
    (hz : z ∈ (l.real ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ)).set) :
    (∃ i < (slotWs (cKind (gadAt Φ c))).length,
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (canonSlot (n := n) v c i) z) ∨
      BandOK n Φ z :=
  slot_cover hΦ hn hv hsol c (slotCov_facts _) (slotCov_spec hv hsol c) hg hl hz

theorem gBasinWs_pos : 0 < gBasinWs.length := by decide +kernel

/-- The index of the basin helper. -/
def basinIdx : CIdx n Φ := .inl (.inr (.inr ⟨0, gBasinWs_pos⟩))

/-- An input of the construction is the input `m` of its slot. -/
theorem input_slot {i : InputSeg} (hi : i ∈ inputsO n Φ) :
    ∃ c : Fin (paramC Φ), ∃ m, ∃ hm : m < (oTmplInputs (cKind (gadAt Φ c))).length,
      i.b = (slotG n Φ c : ℚ) + (tIn (cKind (gadAt Φ c)) m).lx ∧
      i.var = (cVars (gadAt Φ c)).getD (tIn (cKind (gadAt Φ c)) m).role 0 := by
  simp only [inputsO, slotInputsO, List.mem_flatMap, List.mem_range, List.mem_map] at hi
  obtain ⟨c, hc, inp, hinp, rfl⟩ := hi
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hinp
  refine ⟨⟨c, hc⟩, m, hm, ?_, ?_⟩ <;> simp [tIn, List.getElem?_eq_getElem hm]

/-- **The canonical guards see the whole region.** -/
theorem cover_canon (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {v : ℕ → ℝ}
    (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v) :
    ∀ z ∈ PO n Φ, ∃ X : CIdx n Φ,
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (canonO (n := n) v X) z := by
  have e0 : gZero n Φ (v 0) = canonO (n := n) (Φ := Φ) v (varIdx (Φ := Φ) ⟨0, hn⟩) := by
    simp [canonO, varIdx, canonVar, gZero, varA]
  have eL : hL n Φ = canonO (n := n) v (basinIdx (n := n) (Φ := Φ)) := rfl
  have key := cover_of_zones hΦ (hv 0).1 (hv 0).2 (Gs := Set.range (canonO (n := n) v))
    ⟨_, e0.symm⟩ ⟨_, eL.symm⟩ ?_ ?_
  · intro z hz
    obtain ⟨g, ⟨X, rfl⟩, h⟩ := key z hz
    exact ⟨X, h⟩
  · -- floor zones
    intro Z hZ r hr z hz hzP
    rcases zfO_cases hZ with ⟨g, hg, hc, rfl⟩ | ⟨k, hk, g, hg, hc, rfl⟩ | ⟨c, g, hg, hc, rfl⟩
    · obtain ⟨l, hl, rfl⟩ := fzone_rect_group hc hr
      rcases basin_cover hΦ hg hl hz with h | h
      · exact Or.inl ⟨_, ⟨_, eL.symm⟩, h⟩
      · exact Or.inr h
    · obtain ⟨l, hl, rfl⟩ := fzone_rect_group hc hr
      rcases var_cover hΦ hv ⟨k, hk⟩ hg hl hz with ⟨i, hi, h⟩ | h
      · exact Or.inl ⟨_, ⟨.inl (.inl (⟨k, hk⟩, ⟨i, hi⟩)), rfl⟩, h⟩
      · exact Or.inr h
    · obtain ⟨l, hl, rfl⟩ := fzone_rect_group hc hr
      rcases slot_cover' hΦ hn hv hsol c hg hl hz with ⟨i, hi, h⟩ | h
      · exact Or.inl ⟨_, ⟨.inl (.inr (.inl ⟨c, ⟨i, hi⟩⟩)), rfl⟩, h⟩
      · exact Or.inr h
  · -- ceiling zones
    intro Z hZ r hr z hz hzP
    rcases zcO_cases hZ with ⟨c, g, hg, hc, rfl⟩ | ⟨k, hk, g, hg, hc, rfl⟩ | ⟨i, hi, rfl⟩
    · obtain ⟨l, hl, he⟩ := czone_rect_group hc hr
      rw [he] at hz
      rcases slot_cover' hΦ hn hv hsol c hg hl hz with ⟨i, hi, h⟩ | h
      · exact Or.inl ⟨_, ⟨.inl (.inr (.inl ⟨c, ⟨i, hi⟩⟩)), rfl⟩, h⟩
      · exact Or.inr h
    · obtain ⟨l, hl, he⟩ := czone_rect_group hc hr
      rw [he] at hz
      rcases var_cover hΦ hv ⟨k, hk⟩ hg hl hz with ⟨i, hi, h⟩ | h
      · exact Or.inl ⟨_, ⟨.inl (.inl (⟨k, hk⟩, ⟨i, hi⟩)), rfl⟩, h⟩
      · exact Or.inr h
    · -- a copy nook
      have hk := inputsO_var hΦ hi
      have hm : r.neg ∈ cnRR.map (realR (iφ Φ (paramH n Φ) i.var i) (iψ Φ (paramH n Φ) i.var i)) := by
        simp only [iφ, iψ]
        rw [← nzone_rs]; exact List.mem_map.2 ⟨r, hr, rfl⟩
      obtain ⟨R, hR, he⟩ := List.mem_map.1 hm
      rw [← he] at hz
      rcases nookI_cover hΦ hi (hv i.var).1 (hv i.var).2 hR hz with ⟨kk, hkk, h⟩ | h | h | h
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
        refine Or.inl ⟨_, ⟨.inr (⟨j, hj⟩, kk == 0), rfl⟩, ?_⟩
        convert h using 2
        simp only [canonO]
        have : nookQ (kk == 0) = nGuardIdx kk := by
          rcases Nat.lt_or_ge kk 1 with h0 | h0
          · obtain rfl : kk = 0 := by omega
            rfl
          · obtain rfl : kk = 1 := by omega
            rfl
        rw [this]
        rfl
      · refine Or.inl ⟨_, ⟨varIdx ⟨_, hk⟩, rfl⟩, ?_⟩
        convert h using 2
        simp [canonO, varIdx, canonVar, varPt]
      · obtain ⟨c, m, hm, hb, hvar⟩ := input_slot hi
        refine Or.inl ⟨_, ⟨inIdx c hm, rfl⟩, ?_⟩
        convert h using 2
        simp only [canonO, inIdx]
        rw [canonSlot_in c hm]
        simp only [inPt, roleVal, hb, ← hvar]
        push_cast
        ring_nf
      · exact Or.inr h

/-- The region is infinite. -/
theorem PO_infinite : (PO n Φ).Infinite := by
  have hH := Hr_ge' (n := n) (Φ := Φ)
  have hxL : (xL n Φ : ℝ) ≤ -3000 := by exact_mod_cast xL_neg n Φ
  have hxR : (100 : ℝ) ≤ xR n Φ := by exact_mod_cast xR_pos n Φ
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((0 : ℝ), 1 / ((k : ℝ) + 1)))
    (fun a b h => ?_) (fun k => ?_)
  · simp only [Prod.mk.injEq, true_and] at h
    simp only [one_div, inv_inj] at h
    exact_mod_cast (by linarith : (a : ℝ) = b)
  · have h1 : 0 < 1 / ((k : ℝ) + 1) := by positivity
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
    exact hall_filled (by show (xL n Φ : ℝ) ≤ 0; linarith) (by show (0 : ℝ) ≤ xR n Φ; linarith)
      (by show (-1 / 4 : ℝ) ≤ 1 / ((k : ℝ) + 1); linarith)
      (by show 1 / ((k : ℝ) + 1) ≤ 2 * Hr n Φ - 1 / 4; linarith)

/-- **Completeness (b)**: a solution gives a guard set of `guardsO n Φ` points. -/
theorem guardSetO_of_sat (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {v : ℕ → ℝ}
    (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v) :
    ∃ G : Finset Point, G.card = guardsO n Φ ∧
      (Polygon.mk ((polyO n Φ).map ratPoint)).IsGuardSet (G : Set Point) := by
  classical
  set C : Finset Point := (Finset.univ.image (canonO (n := n) v)).filter (· ∈ PO n Φ)
  have hC : C.card ≤ guardsO n Φ := by
    rw [← card_CIdx]
    exact (Finset.card_filter_le _ _).trans Finset.card_image_le
  have hinf : (PO n Φ \ (C : Set Point)).Infinite := PO_infinite.diff C.finite_toSet
  obtain ⟨T, hT, hTc⟩ := hinf.exists_subset_card_eq (guardsO n Φ - C.card)
  refine ⟨C ∪ T, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint, hTc]
    · omega
    · rw [Finset.disjoint_left]
      intro x hx hxT
      exact (hT hxT).2 hx
  · intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact (Finset.mem_filter.1 hx).2
    · exact (hT hx).1
  · intro z hz
    obtain ⟨X, hX⟩ := cover_canon hΦ hn hv hsol z hz
    refine ⟨canonO v X, Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _
      (Finset.mem_univ _), hX (left_mem_segment _ _)⟩), hX⟩

end

end ArtGallery.Orthogonal.Hard
