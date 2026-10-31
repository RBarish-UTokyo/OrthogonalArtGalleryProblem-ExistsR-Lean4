module

public import ArtGallery.Orthogonal.Hard.NookCovChk0
public import ArtGallery.Orthogonal.Hard.NookCovChk1
public import ArtGallery.Orthogonal.Hard.NookCovChk2
public import ArtGallery.Orthogonal.Hard.NookCovChk3
public import ArtGallery.Orthogonal.Hard.NookCovChk4
public import ArtGallery.Orthogonal.Hard.NookCovChk5
public import ArtGallery.Orthogonal.Hard.NookCovChk6
public import ArtGallery.Orthogonal.Hard.NookCovChk7
public import ArtGallery.Orthogonal.Hard.NookCovChk8
public import ArtGallery.Orthogonal.Hard.NookCovChk9
public import ArtGallery.Orthogonal.Hard.NookCovChk10
public import ArtGallery.Orthogonal.Hard.NookCovChk11
public import ArtGallery.Orthogonal.Hard.NookCovChk12
public import ArtGallery.Orthogonal.Hard.NookCovChk13
public import ArtGallery.Orthogonal.Hard.NookCovChk14
public import ArtGallery.Orthogonal.Hard.NookCovChk15
public import ArtGallery.Orthogonal.Hard.NookCovChk16
public import ArtGallery.Orthogonal.Hard.NookCovChk17
public import ArtGallery.Orthogonal.Hard.NookCovChk18
public import ArtGallery.Orthogonal.Hard.NookCovChk19
public import ArtGallery.Orthogonal.Hard.NookCovChk20
public import ArtGallery.Orthogonal.Hard.NookCovChk21
public import ArtGallery.Orthogonal.Hard.NookCovChk22

/-!
# The copy-nook coverage certificate: all cells

The chunk checks `nookCells_ok0`, …, `nookCells_ok22` (five cells each) assembled.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

/-- A list all of whose chunks satisfy `p` satisfies `p`. -/
theorem List.all_of_chunks {α : Type*} {l : List α} {p : α → Bool} (k m : ℕ)
    (hm : l.length ≤ m * k) (hp : ∀ i < m, ((l.drop (i * k)).take k).all p = true) :
    l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rw [Nat.mul_zero] at hm; omega
    · exact h
  have hi : j / k < m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  have hpi := List.all_eq_true.1 (hp _ hi)
  have hjk := Nat.div_add_mod j k
  have hmk := Nat.mod_lt j hk
  have hlen : j - j / k * k < ((l.drop (j / k * k)).take k).length := by
    simp only [List.length_take, List.length_drop]
    rw [Nat.mul_comm] at hjk
    apply Nat.lt_min.2; constructor <;> omega
  have he : ((l.drop (j / k * k)).take k)[j - j / k * k] = l[j] := by
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
    rw [Nat.mul_comm] at hjk
    omega
  rw [← he]
  exact hpi _ (List.getElem_mem hlen)

set_option maxRecDepth 100000 in
/-- **Every cell of the copy-nook certificate has a valid cut tree.** -/
theorem nookCells_ok : nookCells.all (fun ct => treeNB ct.1 [] ct.2) = true :=
  List.all_of_chunks 5 23 (by decide) fun i hi =>
    match i, hi with
    | 0, _ => nookCells_ok0
    | 1, _ => nookCells_ok1
    | 2, _ => nookCells_ok2
    | 3, _ => nookCells_ok3
    | 4, _ => nookCells_ok4
    | 5, _ => nookCells_ok5
    | 6, _ => nookCells_ok6
    | 7, _ => nookCells_ok7
    | 8, _ => nookCells_ok8
    | 9, _ => nookCells_ok9
    | 10, _ => nookCells_ok10
    | 11, _ => nookCells_ok11
    | 12, _ => nookCells_ok12
    | 13, _ => nookCells_ok13
    | 14, _ => nookCells_ok14
    | 15, _ => nookCells_ok15
    | 16, _ => nookCells_ok16
    | 17, _ => nookCells_ok17
    | 18, _ => nookCells_ok18
    | 19, _ => nookCells_ok19
    | 20, _ => nookCells_ok20
    | 21, _ => nookCells_ok21
    | 22, _ => nookCells_ok22
    | _ + 23, h => absurd h (by omega)

end

end ArtGallery.Orthogonal.Hard
