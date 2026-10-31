module

public import ArtGallery.Orthogonal.Hard.GroupsO

/-!
# Counting: the lower bound for the orthogonal polygon

The counting witnesses: those of the template groups (one group instance per variable, per slot,
and the basin) and two per copy nook (its two helpers).  Witnesses of one group instance have
disjoint viewer sets by the group certificates (`group_disjoint`); witnesses of different group
instances by the strips containing their viewers (`group_viewer_x`) and the layout.  The copy-nook
witnesses are handled by `NookCount` (viewers in thin columns inside the nook's box).
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain ArtGallery.Irrational
  ArtGallery.Geometry Set

variable {n : ℕ} {Φ : List Constraint}

/-- The counting witnesses of the template groups: variables, slots, basin. -/
abbrev TIdx (n : ℕ) (Φ : List Constraint) : Type :=
  (Fin n × Fin gVarWs.length) ⊕
    ((Σ c : Fin (paramC Φ), Fin (slotWs (cKind (gadAt Φ c))).length) ⊕ Fin gBasinWs.length)

/-- The witness of an index of a template group. -/
noncomputable def twit : TIdx n Φ → Point
  | .inl (k, i) => (gVarWs[i]).a.real (varA Φ k) (Hr n Φ)
  | .inr (.inl ⟨c, i⟩) => ((slotWs (cKind (gadAt Φ c)))[i]).a.real (slotG n Φ c) (Hr n Φ)
  | .inr (.inr i) => (gBasinWs[i]).a.real (xL n Φ) (Hr n Φ)

/-- The strip containing the viewers of a witness of a template group. -/
noncomputable def tstrip : TIdx n Φ → ℝ × ℝ
  | .inl (k, _) => ((varA Φ k : ℝ) - 16, (varA Φ k : ℝ) + 16)
  | .inr (.inl ⟨c, _⟩) => ((slotG n Φ c : ℝ) - 460, (slotG n Φ c : ℝ) + 560)
  | .inr (.inr _) => ((xL n Φ : ℝ), (xL n Φ : ℝ) + 40)

/-- The viewers of a template witness lie in its strip. -/
theorem twit_viewer (X : TIdx n Φ) {p : Point}
    (hs : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees (twit X) p) :
    (tstrip X).1 < p.1 ∧ p.1 < (tstrip X).2 := by
  rcases X with ⟨k, i⟩ | ⟨c, i⟩ | i
  · have he := var_ext
    simp only [Bool.and_eq_true] at he
    have := group_viewer_x gVar_ok he.1 (varZ_in k.isLt) (List.getElem_mem i.isLt) hs
    simp only [tstrip]; push_cast at this ⊢; constructor <;> linarith [this.1, this.2]
  · have he := slot_ext (cKind (gadAt Φ c))
    simp only [Bool.and_eq_true] at he
    have := group_viewer_x (slot_ok _) he.1 (slotZ_in c.isLt) (List.getElem_mem i.isLt) hs
    simp only [tstrip]; push_cast at this ⊢; constructor <;> linarith [this.1, this.2]
  · have he := basin_ext
    simp only [Bool.and_eq_true] at he
    have := group_viewer_x gBasin_ok he.1 basinZ_in (List.getElem_mem i.isLt) hs
    simp only [tstrip]; push_cast at this ⊢; constructor <;> linarith [this.1, this.2]

/-- Template witnesses are boundary points. -/
theorem twit_boundary (X : TIdx n Φ) :
    twit X ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).boundary := by
  rcases X with ⟨k, i⟩ | ⟨c, i⟩ | i
  · have he := var_ext
    simp only [Bool.and_eq_true, List.all_eq_true] at he
    exact witness_boundary (varZ_in k.isLt) (he.2 _ (List.getElem_mem i.isLt))
  · have he := slot_ext (cKind (gadAt Φ c))
    simp only [Bool.and_eq_true, List.all_eq_true] at he
    exact witness_boundary (slotZ_in c.isLt) (he.2 _ (List.getElem_mem i.isLt))
  · have he := basin_ext
    simp only [Bool.and_eq_true, List.all_eq_true] at he
    exact witness_boundary basinZ_in (he.2 _ (List.getElem_mem i.isLt))

/-! ### Layout -/

theorem varA_cast (k : ℕ) : ((varA Φ k : ℚ) : ℝ) = (varA Φ k : ℝ) := by push_cast; rfl

theorem slotG_sep {c c' : ℕ} (h : c < c') : (slotG n Φ c : ℝ) + 1200 ≤ slotG n Φ c' := by
  have : slotG n Φ c + 1200 ≤ slotG n Φ c' := by unfold slotG; omega
  exact_mod_cast this

theorem varA_sep {k k' : ℕ} (h : k < k') : (varA Φ k : ℝ) + 50 ≤ varA Φ k' := by
  have := s2_var (Φ := Φ) h
  have h0 : (0 : ℚ) ≤ paramC Φ := by positivity
  have : (varA Φ k : ℚ) + 50 ≤ varA Φ k' := by linarith
  exact_mod_cast this

theorem var_slot_sep {k c : ℕ} (hk : k < n) : (varA Φ k : ℝ) + 1000 ≤ slotG n Φ c := by
  have h1 := s1_lower (n := n) (Φ := Φ) (k := k) (c := c) hk
  have h2 := paramH_ge n Φ
  have : varA Φ k + 1000 ≤ slotG n Φ c := by omega
  exact_mod_cast this

theorem xL_var_sep (k : ℕ) : (xL n Φ : ℝ) + 1000 ≤ varA Φ k := by
  have h1 : (xL n Φ : ℝ) = -3 * ((paramH n Φ : ℚ) : ℝ) := by simp [xL]
  have h2 : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := by exact_mod_cast paramH_ge_q n Φ
  have h3 : (0 : ℝ) ≤ varA Φ k := by positivity
  rw [h1]; linarith

theorem xL_slot_sep (c : ℕ) : (xL n Φ : ℝ) + 1000 ≤ slotG n Φ c := by
  have h1 : (xL n Φ : ℝ) = -3 * ((paramH n Φ : ℚ) : ℝ) := by simp [xL]
  have h2 : (1000 : ℝ) ≤ ((paramH n Φ : ℚ) : ℝ) := by exact_mod_cast paramH_ge_q n Φ
  have h3 : (0 : ℝ) ≤ slotG n Φ c := by positivity
  rw [h1]; linarith

/-- Distinct template group instances have disjoint strips; witnesses of one instance are
separated by its certificates.  Hence no point sees two template witnesses. -/
theorem twit_disjoint {X Y : TIdx n Φ} (hXY : X ≠ Y) {p : Point}
    (_hp : p ∈ (Polygon.mk ((polyO n Φ).map ratPoint)).filled)
    (h1 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (twit X))
    (h2 : (Polygon.mk ((polyO n Φ).map ratPoint)).Sees p (twit Y)) : False := by
  have s1 := twit_viewer X (sees_symm h1)
  have s2 := twit_viewer Y (sees_symm h2)
  rcases X with ⟨k, i⟩ | ⟨c, i⟩ | i <;> rcases Y with ⟨k', i'⟩ | ⟨c', i'⟩ | i'
  · -- two variable witnesses
    by_cases hk : k = k'
    · subst hk
      have hii : i.1 ≠ i'.1 := fun h => hXY (by rw [Fin.ext h])
      exact group_disjoint gVar_ok (varZ_in k.isLt) (strip_bound n Φ) i.isLt i'.isLt hii h1 h2
    · simp only [tstrip] at s1 s2
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hk) with h | h
      · have := varA_sep (Φ := Φ) h; linarith [s1.2, s2.1]
      · have := varA_sep (Φ := Φ) h; linarith [s1.1, s2.2]
  · simp only [tstrip] at s1 s2
    have := var_slot_sep (n := n) (Φ := Φ) (c := c'.1) k.isLt; linarith [s1.2, s2.1]
  · simp only [tstrip] at s1 s2
    have := xL_var_sep (n := n) (Φ := Φ) k.1; linarith [s1.1, s2.2]
  · simp only [tstrip] at s1 s2
    have := var_slot_sep (n := n) (Φ := Φ) (c := c.1) k'.isLt; linarith [s1.1, s2.2]
  · by_cases hc : c = c'
    · subst hc
      have hii : i.1 ≠ i'.1 := fun h => hXY (by rw [Fin.ext h])
      exact group_disjoint (slot_ok _) (slotZ_in c.isLt) (strip_bound n Φ) i.isLt i'.isLt hii h1 h2
    · simp only [tstrip] at s1 s2
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hc) with h | h
      · have := slotG_sep (n := n) (Φ := Φ) h; linarith [s1.2, s2.1]
      · have := slotG_sep (n := n) (Φ := Φ) h; linarith [s1.1, s2.2]
  · simp only [tstrip] at s1 s2
    have := xL_slot_sep (n := n) (Φ := Φ) c.1; linarith [s1.1, s2.2]
  · simp only [tstrip] at s1 s2
    have := xL_var_sep (n := n) (Φ := Φ) k'.1; linarith [s1.2, s2.1]
  · simp only [tstrip] at s1 s2
    have := xL_slot_sep (n := n) (Φ := Φ) c'.1; linarith [s1.2, s2.1]
  · have hii : i.1 ≠ i'.1 := fun h => hXY (by rw [Fin.ext h])
    exact group_disjoint gBasin_ok basinZ_in (strip_bound n Φ) i.isLt i'.isLt hii h1 h2

end

end ArtGallery.Orthogonal.Hard
