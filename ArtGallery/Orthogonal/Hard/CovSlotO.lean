module

public import ArtGallery.Orthogonal.Hard.CovCanon
public import ArtGallery.Orthogonal.Hard.CovPocket
public import ArtGallery.Orthogonal.Hard.CovRegion

/-!
# Completeness: the slot groups (generic part)

For a slot of kind `k` with a valid coverage certificate (`SlotFacts`) whose pockets satisfy their
geometric conditions for the canonical guards, every point of a rectangle of the slot group is
seen by a canonical guard of the slot or is a band point.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade Set

variable {n : ℕ} {Φ : List Constraint}

/-- The data checks of a slot certificate. -/
def slotFactsB (k : TKind) (c : GroupCov) (Ps : List PocketD) : Bool :=
  decide (c.frame.good = (groupLR (slotZ k)).map Prod.fst) &&
  guardB (slotRange k) (slotWs k).length c &&
  pockItemB c Ps && pockMouthB c (slotRange k) (slotWs k).length Ps &&
  decide (-460 ≤ c.frame.F.x0) && decide (c.frame.F.x1 ≤ 560) &&
  c.frame.good.all (fun R => decide (-460 ≤ R.x0) && decide (R.x1 ≤ 560)) &&
  c.frame.strips.all (fun R => decide (-460 ≤ R.x0) && decide (R.x1 ≤ 560) &&
    (k != .invRevLe || decide (R.y0 = (-1 / 4, 2)) || decide (R.x1 < 31) || decide (59 < R.x0))) &&
  (k != .invRevLe || c.patchB 31 61)

/-- The facts of a slot certificate. -/
structure SlotFacts (k : TKind) (c : GroupCov) (Ps : List PocketD) : Prop where
  ok : c.ok = true
  facts : slotFactsB k c Ps = true

section Slot

variable {k : TKind} {cert : GroupCov} {Ps : List PocketD} (hF : SlotFacts k cert Ps)
include hF

theorem SlotFacts.good : cert.frame.good = (groupLR (slotZ k)).map Prod.fst := by
  have h := hF.facts
  simp only [slotFactsB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1

theorem SlotFacts.parts : guardB (slotRange k) (slotWs k).length cert = true ∧
    pockItemB cert Ps = true ∧ pockMouthB cert (slotRange k) (slotWs k).length Ps = true ∧
    -460 ≤ cert.frame.F.x0 ∧ cert.frame.F.x1 ≤ 560 ∧
    (∀ R ∈ cert.frame.good, -460 ≤ R.x0 ∧ R.x1 ≤ 560) ∧
    (∀ R ∈ cert.frame.strips, -460 ≤ R.x0 ∧ R.x1 ≤ 560 ∧
      (k = .invRevLe → R.y0 = (-1 / 4, 2) ∨ R.x1 < 31 ∨ 59 < R.x0)) ∧
    (k = .invRevLe → cert.patchB 31 61 = true) := by
  have h := hF.facts
  simp only [slotFactsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun R hR => ?_, fun hk => ?_⟩
  · obtain ⟨⟨a, b⟩, c⟩ := h7 R hR
    exact ⟨a, b, by tauto⟩
  rcases h8 with h | h
  · exact absurd hk h
  · exact h

end Slot

/-- `g_c ≥ 1000` (there is a variable). -/
theorem slotG_ge_cov {c : ℕ} (hn : 0 < n) : (1000 : ℝ) ≤ slotG n Φ c := by
  have := var_slot_sep (n := n) (Φ := Φ) (k := 0) (c := c) hn
  have h0 : ((varA Φ 0 : ℕ) : ℝ) = 0 := by simp [varA]
  linarith

/-- The strips of a slot frame are in the region. -/
theorem slot_strips (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {c : Fin (paramC Φ)} {cert : GroupCov}
    (hst : ∀ R ∈ cert.frame.strips, -460 ≤ R.x0 ∧ R.x1 ≤ 560 ∧
      (cKind (gadAt Φ c) = .invRevLe → R.y0 = (-1 / 4, 2) ∨ R.x1 < 31 ∨ 59 < R.x0)) :
    ∀ R ∈ cert.frame.strips, ((R.real ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ)).set) ⊆ PO n Φ := by
  have hH := Hr_ge' (n := n) (Φ := Φ)
  have hG := slotG_ge_cov (n := n) (Φ := Φ) (c := c) hn
  have hxR : (slotG n Φ c : ℝ) + 1300 ≤ (xR n Φ : ℝ) := by
    have := slot_lt_xR (n := n) (Φ := Φ) c.isLt
    have h' : ((slotG n Φ c : ℚ) : ℝ) + 1300 ≤ (xR n Φ : ℝ) := by exact_mod_cast this
    push_cast at h'; exact h'
  have hxL : (xL n Φ : ℝ) ≤ -3000 := by exact_mod_cast xL_neg n Φ
  intro R hR p hp
  obtain ⟨hx0, hx1, hy⟩ := hst R hR
  have hx0' : (-460 : ℝ) ≤ R.x0 := by exact_mod_cast hx0
  have hx1' : (R.x1 : ℝ) ≤ 560 := by exact_mod_cast hx1
  simp only [GCovC.strips, List.mem_append, List.mem_map, List.mem_filter] at hR
  rcases hR with ⟨s, -, rfl⟩ | ⟨s, -, rfl⟩
  · -- floor strip
    simp only [LR.real, Rect.set, mem_ofPred_eq, AH.ev] at hp hx0' hx1'
    push_cast at hp
    obtain ⟨p1, p2, p3, p4⟩ := hp
    rcases floor_band (p := p) (by linarith) (by linarith) (by linarith) (by linarith) with h |
      ⟨c', -, hk', w1, w2, -⟩
    · exact h
    · exfalso
      rcases lt_trichotomy c.1 c' with h | h | h
      · have := slotG_sep (n := n) (Φ := Φ) h; linarith
      · subst h
        simp only [Prod.mk.injEq] at hy
        rcases hy hk' with ⟨h1, -⟩ | h | h
        · norm_num at h1
        · have : (s.b : ℝ) < 31 := by exact_mod_cast h
          linarith
        · have : (59 : ℝ) < s.a := by exact_mod_cast h
          linarith
      · have := slotG_sep (n := n) (Φ := Φ) h; linarith
  · -- ceiling strip
    simp only [LR.real, Rect.set, mem_ofPred_eq, AH.ev] at hp hx0' hx1'
    push_cast at hp
    obtain ⟨p1, p2, p3, p4⟩ := hp
    have eH : Hr n Φ = (paramH n Φ : ℝ) := by simp [Hr]
    rcases ceil_band (n := n) (Φ := Φ) (p := p) (by linarith) (by linarith) (by linarith)
      (by linarith) with h | ⟨i, hi, -, w2, -⟩
    · exact h
    · obtain ⟨-, e16, -, e0⟩ := nook_window hΦ hi
      linarith

/-- The hall of a slot frame is in the region. -/
theorem slot_hall (hn : 0 < n) {c : Fin (paramC Φ)} {cert : GroupCov}
    (h0 : -460 ≤ cert.frame.F.x0) (h1 : cert.frame.F.x1 ≤ 560) :
    ((cert.frame.hall.real ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ)).set) ⊆ PO n Φ := by
  have hG := slotG_ge_cov (n := n) (Φ := Φ) (c := c) hn
  have hxR : (slotG n Φ c : ℝ) + 1300 ≤ (xR n Φ : ℝ) := by
    have := slot_lt_xR (n := n) (Φ := Φ) c.isLt
    have h' : ((slotG n Φ c : ℚ) : ℝ) + 1300 ≤ (xR n Φ : ℝ) := by exact_mod_cast this
    push_cast at h'; exact h'
  have hxL : (xL n Φ : ℝ) ≤ -3000 := by exact_mod_cast xL_neg n Φ
  have h0' : (-460 : ℝ) ≤ cert.frame.F.x0 := by exact_mod_cast h0
  have h1' : (cert.frame.F.x1 : ℝ) ≤ 560 := by exact_mod_cast h1
  intro p hp
  simp only [GCovC.hall, LR.real, Rect.set, mem_ofPred_eq, AH.ev] at hp
  push_cast at hp
  obtain ⟨p1, p2, p3, p4⟩ := hp
  have eH : Hr n Φ = (paramH n Φ : ℝ) := by simp [Hr]
  exact hall_filled (by linarith) (by linarith) (by linarith) (by linarith)

/-- **A slot group.** -/
theorem slot_cover (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hn : 0 < n) {v : ℕ → ℝ}
    (hv : ∀ i, 1 / 2 ≤ v i ∧ v i ≤ 2) (hsol : ∀ c ∈ Φ, c.Holds v) (c : Fin (paramC Φ))
    {cert : GroupCov} {Ps : List PocketD} (hF : SlotFacts (cKind (gadAt Φ c)) cert Ps)
    (hspec : ∀ p ∈ Ps, p.Spec ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ) (canonSlot (n := n) v c p.a)
      (canonSlot (n := n) v c p.b))
    {g : GZ} (hg : g ∈ slotZ (cKind (gadAt Φ c))) {l : LR} (hl : l ∈ g.rects) {z : Point}
    (hz : z ∈ (l.real ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ)).set) :
    (∃ i < (slotWs (cKind (gadAt Φ c))).length,
      (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (canonSlot (n := n) v c i) z) ∨
      BandOK n Φ z := by
  obtain ⟨hG, hpi, hpm, hF0, hF1, hgx, hst, hpat⟩ := hF.parts
  have hgs := slotZ_in (n := n) (Φ := Φ) c.isLt
  have hstr := slot_strips hΦ hn (c := c) hst
  have hhall := slot_hall hn (c := c) hF0 hF1
  have hγ : ∀ i < (slotWs (cKind (gadAt Φ c))).length, ∀ S : Set Point, Convex ℝ S →
      (∀ p ∈ slotRange (cKind (gadAt Φ c)) i, p.real ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ) ∈ S) →
      canonSlot (n := n) v c i ∈ S :=
    fun i _ S hS hR => canonSlot_mem hv hsol c i hS hR
  rcases groupCov_canon_rect hgs hF.ok hF.good hstr hhall hG hγ hg hl hz with
    h | ⟨j, hj, hemp, hzj⟩ | ⟨i, hi, hzi, hk0, h1, h2⟩
  · exact Or.inl h
  · left
    have hS : ∀ R ∈ cert.frame.good ++ cert.frame.strips,
        (R.real ((slotG n Φ c : ℚ) : ℝ) (Hr n Φ)).set ⊆ (Polygon.mk ((polyO n Φ).map ratPoint)).filled := by
      intro R hR
      rcases List.mem_append.1 hR with hR | hR
      · rw [hF.good] at hR; exact groupLR_filled hgs hR
      · exact hstr R hR
    exact pocket_seen hF.ok (Hr_ge n Φ) _ hS hhall hpi hpm hγ hspec hj hemp hzj
  · right
    obtain ⟨hx0, hx1⟩ := hgx _ (List.getElem_mem hi)
    have hx0' : (-460 : ℝ) ≤ (cert.frame.good[i]).x0 := by exact_mod_cast hx0
    have hx1' : ((cert.frame.good[i]).x1 : ℝ) ≤ 560 := by exact_mod_cast hx1
    have hzi' := hzi
    obtain ⟨z1, z2, -, -⟩ := hzi'
    simp only [LR.real] at z1 z2
    push_cast at z1 z2
    have hGc := slotG_ge_cov (n := n) (Φ := Φ) (c := c) hn
    refine ⟨h1, h2, fun c' hc' hk' hw => ?_, right_noE hΦ (by linarith)⟩
    by_cases hcc : c' = c.1
    · subst hcc
      have hp := hpat hk'
      obtain ⟨w1, w2, w3⟩ := hw
      exact hk0 (GroupCov.patch_kind hp (Hr_ge n Φ) _ hi hzi (by push_cast; linarith)
        (by push_cast; linarith) w3)
    · exact slot_noW (c := c.1) (by linarith) (by linarith) c' hc' hcc hk' hw

end

end ArtGallery.Orthogonal.Hard
