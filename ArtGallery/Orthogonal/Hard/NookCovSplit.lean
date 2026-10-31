module

public import ArtGallery.Orthogonal.Hard.NookCovData

/-!
# Splitting a chunk of the copy-nook coverage check

A chunk `((l.drop a).take k).all p` of a list check is the conjunction of its first entry and the
rest; heavy chunks are proved one cell per declaration, which bounds the kernel's caches.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

theorem List.all_drop_take_succ {α : Type*} (l : List α) (p : α → Bool) (a k : ℕ)
    (h1 : ((l.drop a).take 1).all p = true) (h2 : ((l.drop (a + 1)).take k).all p = true) :
    ((l.drop a).take (k + 1)).all p = true := by
  rw [← List.drop_drop] at h2
  rcases h : l.drop a with _ | ⟨x, rest⟩
  · simp
  · rw [h] at h1 h2
    simp only [List.take_succ_cons, List.all_cons, List.take_zero, List.all_nil, Bool.and_true,
      List.drop_one, List.tail_cons] at h1 h2 ⊢
    rw [h1, h2]; rfl

/-! ### Splitting a cell by subtrees

The cut tree of a heavy cell is checked subtree by subtree: `NTree.parts d cuts t` lists the
subtrees of `t` at depth `d` (or the leaves above it) with their cut lists. -/

/-- The subtrees of `t` down to depth `d`, with their cut lists. -/
def NTree.parts : ℕ → List NLn → NTree → List (List NLn × NTree)
  | d + 1, cuts, .lin l t1 t2 => NTree.parts d (l :: cuts) t1 ++ NTree.parts d ((l.2, l.1) :: cuts) t2
  | _, cuts, t => [(cuts, t)]

theorem treeNB_of_parts (c : ℕ × ℕ) : ∀ (d : ℕ) (cuts : List NLn) (t : NTree),
    ((NTree.parts d cuts t).all fun p => treeNB c p.1 p.2) = true → treeNB c cuts t = true
  | 0, cuts, t, h => by simpa [NTree.parts] using h
  | d + 1, cuts, .lin l t1 t2, h => by
    simp only [NTree.parts, List.all_append, Bool.and_eq_true] at h
    simp only [treeNB, Bool.and_eq_true]
    exact ⟨treeNB_of_parts c d _ _ h.1, treeNB_of_parts c d _ _ h.2⟩
  | d + 1, cuts, .leaf .., h => by simpa [NTree.parts] using h
  | d + 1, cuts, .empty _, h => by simpa [NTree.parts] using h

/-- The default cell. -/
def nookCellDflt : (ℕ × ℕ) × NTree := ((0, 0), .empty (.f, .f))

/-- The parts of cell `i` at depth `d`. -/
def nookParts (d i : ℕ) : List (List NLn × NTree) :=
  NTree.parts d [] (nookCells.getD i nookCellDflt).2

/-- The grid cell of cell `i`. -/
def nookCellC (i : ℕ) : ℕ × ℕ := (nookCells.getD i nookCellDflt).1

theorem nookCell_of_parts {d i n : ℕ} (hi : i < nookCells.length) (hn : (nookParts d i).length ≤ n)
    (h : (((nookParts d i).drop 0).take n).all (fun p => treeNB (nookCellC i) p.1 p.2) = true) :
    ((nookCells.drop i).take 1).all (fun ct => treeNB ct.1 [] ct.2) = true := by
  rw [List.drop_zero, List.take_of_length_le hn] at h
  have ht := treeNB_of_parts _ d [] _ h
  rw [List.drop_eq_getElem_cons hi]
  simp only [List.take_succ_cons, List.take_zero, List.all_cons, List.all_nil, Bool.and_true]
  unfold nookCellC at ht
  rwa [List.getD_eq_getElem _ _ hi] at ht

/-! ### Splitting a leaf by rows

The separation condition `nSepB` of a leaf ranges over the cells of a box; it is checked row by
row (`nSepRow`), and the other conditions of the leaf in one piece (`nLeafB0`). -/

/-- Row `i` of `nSepB`. -/
def nSepRow (al : List NLn) (seps : List ((ℕ × ℕ) × ℕ)) (b : ℕ × ℕ × ℕ × ℕ) (i : ℕ) : Bool :=
  (List.range' b.2.2.1 (b.2.2.2 - b.2.2.1)).all fun j =>
    cnRR.any (nCellIn i j) ||
      (seps.lookup (i, j)).any fun m => decide (m < al.length) && offCellB (al.getD m (.f, .f)) (i, j)

/-- The lines of a guard leaf. -/
def nLeafLns (c : ℕ × ℕ) (k : ℕ) (ls : List NLn) : List NLn := ls ++ boxLns (nBox c (nGuardIdx k))

/-- The conditions of a leaf other than the separation of a guard leaf. -/
def nLeafB0 (c : ℕ × ℕ) (cuts : List NLn) : NTree → Bool
  | .leaf k ls w seps =>
    if k = 2 ∨ k = 3 then nLeafB c cuts (.leaf k ls w seps)
    else
      decide (k ≤ 1) && containB (nLeafLns c k ls) cuts c &&
        (nLeafLns c k ls).all
          (fun l => nnN (lnDet l (NRef.g (nGuardIdx k).1 (nGuardIdx k).2).mp)) &&
        (nLeafLns c k ls).all (fun l => posN (lnDet l (wpt w)))
  | t => treeNB c cuts t

/-- The rows of the separation condition of a guard leaf. -/
def nLeafRows (c : ℕ × ℕ) : NTree → List ℕ
  | .leaf k _ _ _ =>
    if k = 2 ∨ k = 3 then [] else List.range' (nBox c (nGuardIdx k)).1
      ((nBox c (nGuardIdx k)).2.1 - (nBox c (nGuardIdx k)).1)
  | _ => []

/-- Row `i` of the separation condition of a guard leaf. -/
def nLeafSep (c : ℕ × ℕ) (t : NTree) (i : ℕ) : Bool :=
  match t with
  | .leaf k ls _ seps => nSepRow (nLeafLns c k ls) seps (nBox c (nGuardIdx k)) i
  | _ => true

theorem treeNB_of_leaf {c : ℕ × ℕ} {cuts : List NLn} {t : NTree} (h0 : nLeafB0 c cuts t = true)
    (hs : (nLeafRows c t).all (nLeafSep c t) = true) : treeNB c cuts t = true := by
  cases t with
  | lin l t1 t2 => exact h0
  | empty l => exact h0
  | leaf k ls w seps =>
    simp only [treeNB]
    simp only [nLeafB0] at h0
    by_cases hk : k = 2 ∨ k = 3
    · rw [if_pos hk] at h0; exact h0
    · rw [if_neg hk] at h0
      simp only [nLeafRows, if_neg hk] at hs
      have hk2 : k ≠ 2 := fun e => hk (Or.inl e)
      have hk3 : k ≠ 3 := fun e => hk (Or.inr e)
      simp only [nLeafB, if_neg hk2, if_neg hk3]
      simp only [nLeafLns, Bool.and_eq_true] at h0 ⊢
      refine ⟨h0, ?_⟩
      unfold nSepB
      refine List.all_eq_true.2 fun i hi => ?_
      have := List.all_eq_true.1 hs i hi
      simpa [nLeafSep, nSepRow, nLeafLns] using this

/-- Part `j` of cell `i` at depth `d`. -/
def nookPart (d i j : ℕ) : List NLn × NTree := (nookParts d i).getD j ([], .empty (.f, .f))

theorem nookPart_of_leaf {d i j R : ℕ} (hj : j < (nookParts d i).length)
    (h0 : nLeafB0 (nookCellC i) (nookPart d i j).1 (nookPart d i j).2 = true)
    (hR : (nLeafRows (nookCellC i) (nookPart d i j).2).length ≤ R)
    (hs : (((nLeafRows (nookCellC i) (nookPart d i j).2).drop 0).take R).all
      (nLeafSep (nookCellC i) (nookPart d i j).2) = true) :
    (((nookParts d i).drop j).take 1).all (fun p => treeNB (nookCellC i) p.1 p.2) = true := by
  rw [List.drop_zero, List.take_of_length_le hR] at hs
  have ht := treeNB_of_leaf h0 hs
  rw [List.drop_eq_getElem_cons hj]
  simp only [List.take_succ_cons, List.take_zero, List.all_cons, List.all_nil, Bool.and_true]
  unfold nookPart at ht
  rwa [List.getD_eq_getElem _ _ hj] at ht

end

end ArtGallery.Orthogonal.Hard
