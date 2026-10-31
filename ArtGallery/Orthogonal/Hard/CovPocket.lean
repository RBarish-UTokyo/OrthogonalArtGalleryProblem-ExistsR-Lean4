module

public import ArtGallery.Orthogonal.Hard.CovCanonBase
public import ArtGallery.Orthogonal.Hard.AddPocketO
public import ArtGallery.Stade.GuardInv

/-!
# Completeness: the pockets of the gadgets

A pocket item of a coverage certificate (an item without range, whose lines are the sides of a
pocket quadrilateral) is seen by two canonical guards: both see the mouth (through mouth items
of the certificate) and every point of the nook segment is reached through the mouth by one of
them (the nook lemmas below: the inversion algebra of Stade, the addition rooms of
`AddPocketO`).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry ArtGallery.ETRINVREV ArtGallery.Stade Set

/-- **A pocket item seen by two guards.** -/
theorem pocket_items {P : Polygon} {it itA itB : CItem} {ox H : ℝ} (hH : 1000 ≤ H)
    {lo dn up hi : LP} (hS : it.set ox H ⊆ P.filled) (hSA : itA.set ox H ⊆ P.filled)
    (hSB : itB.set ox H ⊆ P.filled)
    (e1 : (lo, dn) ∈ it.lines) (e2 : (dn, up) ∈ it.lines) (e3 : (up, hi) ∈ it.lines)
    (e4 : (hi, lo) ∈ it.lines)
    (v1 : inLinesB it.allLines lo = true) (v2 : inLinesB it.allLines dn = true)
    (v3 : inLinesB it.allLines up = true) (v4 : inLinesB it.allLines hi = true)
    (h1 : 0 < det (lo.real ox H) (dn.real ox H) (up.real ox H))
    (h2 : 0 < det (dn.real ox H) (up.real ox H) (hi.real ox H))
    (h3 : 0 < det (up.real ox H) (hi.real ox H) (lo.real ox H))
    (h4 : 0 < det (hi.real ox H) (lo.real ox H) (dn.real ox H))
    {ga gb : Point} (hga : ga ∈ itA.set ox H) (hda : inLinesB itA.allLines dn = true)
    (hua : inLinesB itA.allLines up = true) (hgb : gb ∈ itB.set ox H)
    (hdb : inLinesB itB.allLines dn = true) (hub : inLinesB itB.allLines up = true)
    (hnook : ∀ s ∈ segment (lo.real ox H) (hi.real ox H),
      (∃ q ∈ segment (dn.real ox H) (up.real ox H), q ∈ segment ga s) ∨
      ∃ q ∈ segment (dn.real ox H) (up.real ox H), q ∈ segment gb s) :
    ∀ z ∈ it.set ox H, P.Sees ga z ∨ P.Sees gb z := by
  intro z hz
  have hK : piece (quad (lo.real ox H) (dn.real ox H) (up.real ox H) (hi.real ox H)) ⊆ P.filled :=
    (quad_subset_convex (CItem.convex ox H it) h1 h2 h3 h4 (CItem.mem_of_inLinesB v1 hH ox)
      (CItem.mem_of_inLinesB v2 hH ox) (CItem.mem_of_inLinesB v3 hH ox)
      (CItem.mem_of_inLinesB v4 hH ox)).trans hS
  exact pocket_cover_two h1 h2 h3 h4 hK
    (CItem.sees_mouth hSA hga (CItem.mem_of_inLinesB hda hH ox) (CItem.mem_of_inLinesB hua hH ox))
    (CItem.sees_mouth hSB hgb (CItem.mem_of_inLinesB hdb hH ox) (CItem.mem_of_inLinesB hub hH ox))
    hnook z (CItem.mem_quad e1 e2 e3 e4 hz)

/-! ### The nooks of the inversion gadgets -/

/-- **`invGe` nook**: if `1 ≤ v w`, every point of the nook segment `I J` is reached through the
mouth `Q P` by the x-guard or the y-guard. -/
theorem ig_nook {G v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hrel : 1 ≤ v * w) :
    ∀ s ∈ segment (igI G) (igJ G),
      (∃ q ∈ segment (igQ G) (igP G), q ∈ segment (inPt (G + 40) v) s) ∨
      ∃ q ∈ segment (igQ G) (igP G), q ∈ segment (inPt (G + 100) w) s := by
  intro s hs
  rw [Geometry.segment_comm] at hs
  obtain ⟨e1, e2, e3⟩ := ig_nook_iff.1 hs
  have e : s = (s.1, -78) := Prod.ext rfl e1
  by_cases hsh : igShX G v ≤ s.1
  · obtain ⟨q, hq, hqs⟩ := ig_x_cross (g := G) hv1 hsh e3
    rw [Geometry.segment_comm] at hq
    exact Or.inl ⟨q, hq, by rw [e]; exact hqs⟩
  · push Not at hsh
    have hle := (igSh_le_iff (g := G) (by linarith) (by linarith)).2 hrel
    obtain ⟨q, hq, hqs⟩ := ig_y_cross (g := G) hw1 e2 (by linarith)
    rw [Geometry.segment_comm] at hq
    exact Or.inr ⟨q, hq, by rw [e]; exact hqs⟩

/-- **`invRevLe` nook**: if `v (5/2 − w) ≤ 1`, every point of the nook segment `I J` is reached
through the mouth `Q P` by the x-guard or the y-guard. -/
theorem ir_nook {G v w : ℝ} (hv1 : 1 / 2 ≤ v) (hv2 : v ≤ 2) (hw1 : 1 / 2 ≤ w) (hw2 : w ≤ 2)
    (hrel : v * (5 / 2 - w) ≤ 1) :
    ∀ s ∈ segment (irI G) (irJ G),
      (∃ q ∈ segment (irQ G) (irP G), q ∈ segment (inPt (G + 60) v) s) ∨
      ∃ q ∈ segment (irQ G) (irP G), q ∈ segment (inPt (G + 104) w) s := by
  intro s hs
  rw [Geometry.segment_comm] at hs
  obtain ⟨e1, e2, e3⟩ := ir_nook_iff.1 hs
  have e : s = (s.1, -22) := Prod.ext rfl e1
  by_cases hsh : irShX G v ≤ s.1
  · obtain ⟨q, hq, hqs⟩ := ir_x_cross (g := G) hv1 hsh e3
    rw [Geometry.segment_comm] at hq
    exact Or.inl ⟨q, hq, by rw [e]; exact hqs⟩
  · push Not at hsh
    have hle := (irSh_le_iff (g := G) hv1 (by linarith)).2 hrel
    obtain ⟨q, hq, hqs⟩ := ir_y_cross (g := G) hw1 hw2 e2 (by linarith)
    rw [Geometry.segment_comm] at hq
    exact Or.inr ⟨q, hq, by rw [e]; exact hqs⟩

/-! ### Pocket data of a certificate -/

/-- A pocket of a gadget: the counter-clockwise quadrilateral `lo dn up hi` (nook side `lo hi`,
mouth `dn up`, frame coordinates) and the witnesses `a`, `b` of its two guards. -/
structure PocketD where
  lo : LP
  dn : LP
  up : LP
  hi : LP
  a : ℕ
  b : ℕ

/-- The item `j` is the item of pocket `p`: its lines contain the four sides, its set the four
vertices. -/
def PocketD.itemB (p : PocketD) (it : CItem) : Bool :=
  decide ((p.lo, p.dn) ∈ it.lines) && decide ((p.dn, p.up) ∈ it.lines) &&
    decide ((p.up, p.hi) ∈ it.lines) && decide ((p.hi, p.lo) ∈ it.lines) &&
    inLinesB it.allLines p.lo && inLinesB it.allLines p.dn && inLinesB it.allLines p.up &&
    inLinesB it.allLines p.hi

/-- Every item without range is the item of a pocket. -/
def pockItemB (c : GroupCov) (Ps : List PocketD) : Bool :=
  (List.range c.items.length).all fun j =>
    !(c.rngs.getD j []).isEmpty || Ps.any fun p => p.itemB (c.items.getD j CItem.dflt)

/-- Some item contains the range of witness `a` and both ends of the mouth of `p`. -/
def mouthB (c : GroupCov) (R : ℕ → List LP) (p : PocketD) (a : ℕ) : Bool :=
  (List.range c.items.length).any fun k =>
    (R a).all (· ∈ c.rngs.getD k []) && inLinesB (c.items.getD k CItem.dflt).allLines p.dn &&
      inLinesB (c.items.getD k CItem.dflt).allLines p.up

/-- The mouth items of all pockets. -/
def pockMouthB (c : GroupCov) (R : ℕ → List LP) (m : ℕ) (Ps : List PocketD) : Bool :=
  Ps.all fun p => decide (p.a < m) && decide (p.b < m) && mouthB c R p p.a && mouthB c R p p.b

/-- The geometric conditions of a pocket for two guards: strictly convex and counter-clockwise,
and the nook side is reached through the mouth. -/
def PocketD.Spec (p : PocketD) (ox H : ℝ) (ga gb : Point) : Prop :=
  0 < det (p.lo.real ox H) (p.dn.real ox H) (p.up.real ox H) ∧
  0 < det (p.dn.real ox H) (p.up.real ox H) (p.hi.real ox H) ∧
  0 < det (p.up.real ox H) (p.hi.real ox H) (p.lo.real ox H) ∧
  0 < det (p.hi.real ox H) (p.lo.real ox H) (p.dn.real ox H) ∧
  ∀ s ∈ segment (p.lo.real ox H) (p.hi.real ox H),
    (∃ q ∈ segment (p.dn.real ox H) (p.up.real ox H), q ∈ segment ga s) ∨
    ∃ q ∈ segment (p.dn.real ox H) (p.up.real ox H), q ∈ segment gb s

theorem mouthB_sound {P : Polygon} {c : GroupCov} (h : c.ok = true) {H : ℝ} (hH : 1000 ≤ H)
    (ox : ℝ) (hgood : ∀ R ∈ c.frame.good ++ c.frame.strips, (R.real ox H).set ⊆ P.filled)
    (hhall : (c.frame.hall.real ox H).set ⊆ P.filled) {R : ℕ → List LP} {p : PocketD} {a : ℕ}
    (hm : mouthB c R p a = true) {γ : Point}
    (hγ : ∀ S : Set Point, Convex ℝ S → (∀ q ∈ R a, q.real ox H ∈ S) → γ ∈ S) :
    ∃ it : CItem, it.set ox H ⊆ P.filled ∧ γ ∈ it.set ox H ∧ inLinesB it.allLines p.dn = true ∧
      inLinesB it.allLines p.up = true := by
  obtain ⟨k, hk, hb⟩ := List.any_eq_true.1 hm
  simp only [Bool.and_eq_true, List.all_eq_true] at hb
  obtain ⟨⟨hR, hd⟩, hu⟩ := hb
  have hk' := List.mem_range.1 hk
  have hok := h
  simp only [GroupCov.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hrng⟩, -⟩ := hok
  refine ⟨_, GroupCov.item_subset h hH ox hgood hhall hk', hγ _ (CItem.convex _ _ _) fun q hq => ?_,
    hd, hu⟩
  have := List.all_eq_true.1 (idxAll_sound hrng hk') q (by simpa using hR q hq)
  exact CItem.mem_of_inLinesB this hH ox

/-- **The pocket items of a certificate are seen by the guards of their pockets.** -/
theorem pocket_seen {P : Polygon} {c : GroupCov} (h : c.ok = true) {H : ℝ} (hH : 1000 ≤ H)
    (ox : ℝ) (hgood : ∀ R ∈ c.frame.good ++ c.frame.strips, (R.real ox H).set ⊆ P.filled)
    (hhall : (c.frame.hall.real ox H).set ⊆ P.filled) {R : ℕ → List LP} {m : ℕ}
    {Ps : List PocketD} (hpi : pockItemB c Ps = true) (hpm : pockMouthB c R m Ps = true)
    {γ : ℕ → Point}
    (hγ : ∀ i < m, ∀ S : Set Point, Convex ℝ S → (∀ q ∈ R i, q.real ox H ∈ S) → γ i ∈ S)
    (hspec : ∀ p ∈ Ps, p.Spec ox H (γ p.a) (γ p.b)) {j : ℕ} (hj : j < c.items.length)
    (hemp : c.rngs.getD j [] = []) {z : Point} (hz : z ∈ (c.items.getD j CItem.dflt).set ox H) :
    ∃ i < m, P.Sees (γ i) z := by
  have hpj := List.all_eq_true.1 hpi j (List.mem_range.2 hj)
  simp only [hemp, List.isEmpty_nil, Bool.not_true, Bool.false_or, List.any_eq_true] at hpj
  obtain ⟨p, hp, hpit⟩ := hpj
  simp only [PocketD.itemB, Bool.and_eq_true, decide_eq_true_eq] at hpit
  obtain ⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, v1⟩, v2⟩, v3⟩, v4⟩ := hpit
  have hpm' := List.all_eq_true.1 hpm p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpm'
  obtain ⟨⟨⟨ha, hb⟩, hma⟩, hmb⟩ := hpm'
  obtain ⟨itA, hSA, hgA, hdA, huA⟩ := mouthB_sound h hH ox hgood hhall hma (hγ p.a ha)
  obtain ⟨itB, hSB, hgB, hdB, huB⟩ := mouthB_sound h hH ox hgood hhall hmb (hγ p.b hb)
  obtain ⟨h1, h2, h3, h4, hn⟩ := hspec p hp
  rcases pocket_items hH (GroupCov.item_subset h hH ox hgood hhall hj) hSA hSB e1 e2 e3 e4
    v1 v2 v3 v4 h1 h2 h3 h4 hgA hdA huA hgB hdB huB hn z hz with hs | hs
  · exact ⟨p.a, ha, hs⟩
  · exact ⟨p.b, hb, hs⟩

end

end ArtGallery.Orthogonal.Hard
