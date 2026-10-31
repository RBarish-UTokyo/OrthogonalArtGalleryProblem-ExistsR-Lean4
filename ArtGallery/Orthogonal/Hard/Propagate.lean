module

public import ArtGallery.Orthogonal.Hard.RatEq
public import ArtGallery.Geometry.Basic

/-!
# Propagation of visibility cones through a cover by convex sets

The generic tool behind every statement "the points that see the target `w` lie in `S`" of the
orthogonal construction.  Let the segment `w p` be covered by finitely many closed convex sets
`r i` (convexity is not needed), and attach to every `r i` a set `F i` that is *star-closed from `w`* (with a point `z` it
contains every point `w + s (z − w)`, `s ≥ 1`, of the ray from `w` beyond `z`).  If
* (base) `r i ⊆ F i` whenever `w ∈ r i`, and
* (propagation) a point `z ≠ w` of `r i ∩ r j ∩ F i` lies in `F j`,
then `p ∈ F j` for every `j` with `p ∈ r j` (`mem_of_propagate`).

Proof: along `t ↦ w + t (p − w)` every `r i` is met in a closed interval `I_i ⊆ [0, 1]`; the
claim holds on `I_i` once it holds at its left end `a_i` (star-closedness), and at `a_i > 0` it is
inherited from a set `r j` whose interval meets `[0, a_i)` (the finite union of those intervals
is closed and contains `[0, a_i)`, hence `a_i`); induct on `a_i`.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry Set

/-- `F` is star-closed from `w`: with `z` it contains the ray from `w` beyond `z`. -/
def StarFrom (w : Point) (F : Set Point) : Prop :=
  ∀ z ∈ F, ∀ s : ℝ, 1 ≤ s → lerp w z s ∈ F

theorem lerp_lerp_div (w p : Point) {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    lerp w (lerp w p a) (t / a) = lerp w p t := by
  ext <;> simp only [lerp_fst, lerp_snd] <;> field_simp <;> ring

/-- **Cone propagation.** -/
theorem mem_of_propagate {ι : Type*} [Finite ι] (r F : ι → Set Point)
    (hr : ∀ i, IsClosed (r i)) {w p : Point}
    (hF : ∀ i, StarFrom w (F i))
    (hbase : ∀ i, w ∈ r i → r i ⊆ F i)
    (hprop : ∀ i j, ∀ z ∈ r i, z ∈ r j → z ∈ F i → z ≠ w → z ∈ F j)
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ i, lerp w p t ∈ r i) :
    ∀ j, p ∈ r j → p ∈ F j := by
  classical
  have _ := Fintype.ofFinite ι
  by_cases hwp : p = w
  · intro j hj
    subst hwp
    exact hbase j hj hj
  -- the parameter sets
  set I : ι → Set ℝ := fun i => {t | 0 ≤ t ∧ t ≤ 1 ∧ lerp w p t ∈ r i} with hI
  have hlc : Continuous (lerp w p) := by
    unfold lerp; fun_prop
  have hIc : ∀ i, IsClosed (I i) := fun i =>
    (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_id continuous_const).inter ((hr i).preimage hlc))
  -- the left ends
  set a : ι → ℝ := fun i => sInf (I i) with ha
  have ha_mem : ∀ i, (I i).Nonempty → a i ∈ I i := fun i hne =>
    (hIc i).csInf_mem hne ⟨0, fun t ht => ht.1⟩
  have ha_le : ∀ i, ∀ t ∈ I i, a i ≤ t := fun i t ht => csInf_le ⟨0, fun t ht => ht.1⟩ ht
  have hzne : ∀ t : ℝ, 0 < t → lerp w p t ≠ w := by
    intro t ht h
    apply hwp
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [lerp_fst, lerp_snd] at h1 h2
    refine Prod.ext ?_ ?_
    · have : t * (p.1 - w.1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    · have : t * (p.2 - w.2) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
  -- the claim on a whole interval follows from its left end
  have hgood_of_left : ∀ i, (I i).Nonempty → lerp w p (a i) ∈ F i → ∀ t ∈ I i, lerp w p t ∈ F i := by
    intro i hne hai t ht
    have h0 : 0 ≤ a i := (ha_mem i hne).1
    rcases h0.lt_or_eq with hpos | hzero
    · have hst : 1 ≤ t / a i := by rw [le_div_iff₀ hpos]; simpa using ha_le i t ht
      have := hF i _ hai (t / a i) hst
      rwa [lerp_lerp_div w p hpos.ne'] at this
    · have hw : w ∈ r i := by
        have := (ha_mem i hne).2.2
        rw [← hzero] at this
        simpa [lerp] using this
      exact hbase i hw ht.2.2
  -- induction on the left end
  by_contra hcon
  push Not at hcon
  obtain ⟨j₀, hpj₀, hpF⟩ := hcon
  set B : Finset ι := Finset.univ.filter (fun i => ∃ t ∈ I i, lerp w p t ∉ F i) with hB
  have hBne : B.Nonempty := ⟨j₀, by
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨1, ⟨zero_le_one, le_rfl, by simpa [lerp] using hpj₀⟩, by simpa [lerp] using hpF⟩⟩
  obtain ⟨i, hiB, hmin⟩ := B.exists_min_image a hBne
  simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hiB
  obtain ⟨t₀, ht₀, hbad⟩ := hiB
  have hne : (I i).Nonempty := ⟨t₀, ht₀⟩
  have hai_bad : lerp w p (a i) ∉ F i := fun h => hbad (hgood_of_left i hne h t₀ ht₀)
  have hpos : 0 < a i := by
    rcases (ha_mem i hne).1.lt_or_eq with h | h
    · exact h
    · exfalso
      have hw : w ∈ r i := by
        have := (ha_mem i hne).2.2
        rw [← h] at this
        simpa [lerp] using this
      exact hai_bad (hbase i hw (ha_mem i hne).2.2)
  -- the sets met before `a i`
  set J : Finset ι := Finset.univ.filter (fun j => ∃ t ∈ I j, t < a i) with hJ
  have hcovJ : Ico 0 (a i) ⊆ ⋃ j ∈ J, I j := by
    intro t ⟨ht0, hta⟩
    have ht1 : t ≤ 1 := hta.le.trans (ha_mem i hne).2.1
    obtain ⟨j, hj⟩ := hseg t ht0 ht1
    refine mem_iUnion₂.2 ⟨j, ?_, ⟨ht0, ht1, hj⟩⟩
    simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t, ⟨ht0, ht1, hj⟩, hta⟩
  have hclJ : IsClosed (⋃ j ∈ J, I j) :=
    isClosed_biUnion_finset fun j _ => hIc j
  have hai_mem : a i ∈ ⋃ j ∈ J, I j := by
    have h := closure_minimal hcovJ hclJ
    rw [closure_Ico (ne_of_lt hpos)] at h
    exact h ⟨hpos.le, le_rfl⟩
  obtain ⟨j, hjJ, hjI⟩ := mem_iUnion₂.1 hai_mem
  simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at hjJ
  obtain ⟨t₁, ht₁, ht₁a⟩ := hjJ
  have hjlt : a j < a i := (ha_le j t₁ ht₁).trans_lt ht₁a
  have hjgood : ∀ t ∈ I j, lerp w p t ∈ F j := by
    by_contra h
    push Not at h
    have hjB : j ∈ B := by
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    exact absurd (hmin j hjB) (not_le.2 hjlt)
  exact hai_bad (hprop j i _ hjI.2.2 (ha_mem i hne).2.2 (hjgood _ hjI) (hzne _ hpos))

end

end ArtGallery.Orthogonal.Hard
