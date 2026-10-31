module

public import ArtGallery.Orthogonal.Hard.NookCovAll

/-!
# The copy-nook certificate: where the triangle `Q` is used

`treeNB_sound_q` refines `treeNB_sound`: a point reported in the triangle `Q` comes from a tree
with a `Q` leaf, and only the four cells `(13, 4)`, `(13, 5)`, `(14, 4)`, `(14, 5)` have one.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry Set

/-- The tree has a leaf of the triangle `Q`. -/
def NTree.hasQ : NTree → Bool
  | .leaf k _ _ _ => k == 3
  | .empty _ => false
  | .lin _ t1 t2 => t1.hasQ || t2.hasQ

/-- The cells whose trees use the triangle `Q`. -/
def nookQCells : List (ℕ × ℕ) := [(13, 4), (13, 5), (14, 4), (14, 5)]

set_option maxRecDepth 100000 in
theorem nookCells_q : nookCells.all (fun ct => !ct.2.hasQ || decide (ct.1 ∈ nookQCells)) = true := by
  decide +kernel

section

variable {xN H : ℝ} {xs : List ℝ} (hxs : InDom nookDom xs)
  (hφ : StrictMonoOn (nφ xN xs) (Iio 20)) (hψ : StrictMonoOn (nψ H xs) (Iio 19))

include hxs hφ hψ in
/-- **Soundness of a cut tree**, with the use of `Q` recorded. -/
theorem treeNB_sound_q {c : ℕ × ℕ} (hc : c.1 + 1 < 20 ∧ c.2 + 1 < 19) {S : Set Point}
    (hS : IsClosed S) (hreg : ∀ r ∈ cnRR, (realR (nφ xN xs) (nψ H xs) r).set ⊆ S) {z : Point}
    (hz : z ∈ nCell xN H xs c) :
    ∀ (t : NTree) (cuts : List NLn), treeNB c cuts t = true → (∀ l ∈ cuts, z ∈ l.set xN H xs) →
      (∃ k ≤ 1, ArtGallery.segment (nGuardPt xN H xs k) z ⊆ S) ∨ z ∈ nPocket xN H xs ∨
        (t.hasQ = true ∧ z ∈ nQ xN H xs)
  | .lin l t1 t2, cuts, h, hcut => by
    simp only [treeNB, Bool.and_eq_true] at h
    rcases NLn.set_or xN H xs l z with hl | hl
    · rcases treeNB_sound_q hc hS hreg hz t1 (l :: cuts) h.1 (fun l' hl' => by
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact hl
        · exact hcut l' hl') with h | h | ⟨hq, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨by simp [NTree.hasQ, hq], h⟩)
    · rcases treeNB_sound_q hc hS hreg hz t2 ((l.2, l.1) :: cuts) h.2 (fun l' hl' => by
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact hl
        · exact hcut l' hl') with h | h | ⟨hq, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨by simp [NTree.hasQ, hq], h⟩)
  | .empty l, cuts, h, hcut => by
    simp only [treeNB, nLeafB, Bool.and_eq_true, decide_eq_true_eq] at h
    exfalso
    have h1 := emptyB_sound hxs h.2 hz
    have h2 := hcut l h.1
    simp only [NLn.set, mem_ofPred_eq] at h2
    linarith
  | .leaf k ls w seps, cuts, h, hcut => by
    have h' : nLeafB c cuts (.leaf k ls w seps) = true := h
    by_cases hk2 : k = 2
    · subst hk2
      simp only [nLeafB, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h'
      obtain ⟨rfl, hc'⟩ := h'
      exact Or.inr (Or.inl (containB_sound hxs hc' hz hcut))
    by_cases hk3 : k = 3
    · subst hk3
      simp only [nLeafB, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        show (3 : ℕ) ≠ 2 by norm_num] at h'
      obtain ⟨rfl, hc'⟩ := h'
      exact Or.inr (Or.inr ⟨by simp [NTree.hasQ], containB_sound hxs hc' hz hcut⟩)
    obtain ⟨hk, hseg⟩ := nleaf_guard_sound hxs hφ hψ h' hk2 hk3 hc hS hreg hz hcut
    exact Or.inl ⟨k, hk, hseg⟩

end

end

end ArtGallery.Orthogonal.Hard
