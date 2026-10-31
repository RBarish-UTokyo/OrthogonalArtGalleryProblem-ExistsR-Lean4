module

public import ArtGallery.Orthogonal.Hard.GCert

/-!
# Splitting a grid-certificate check

`GCert.ok` is one boolean; for the largest certificates its kernel evaluation does not fit in
memory.  `GCert.ok_of_parts` splits it into a head check and checks of consecutive chunks of the
local rectangles (each chunk checks the local conditions of its rectangles and their propagation
to all rectangles), which are evaluated in separate files.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

/-- The global conditions of `GCert.ok`. -/
def GCert.okHead (NX NY : ℕ) (O : GOr) (c : GCert) : Bool :=
  c.A.wf NX NY && c.U.all (GBox.wf NX NY) && GCert.ok.boxesSepG c.U &&
  (c.cs.flatMap (fun q => q.2.2.flatten) ++ c.C.getD []).all (gstarB O c.A) &&
  c.A.corners.all (c.U.getD c.Ab GBox.default).memB && decide (c.Ab < c.U.length)

/-- The local condition of one rectangle in `GCert.ok`. -/
def GCert.locB (NX NY : ℕ) (O : GOr) (c : GCert) (q : GRect × ℕ × List (List GHP)) : Bool :=
  q.1.wf NX NY && gbaseB O c.A q && decide (q.2.1 < c.U.length) &&
    match q.1.faces (c.U.getD q.2.1 GBox.default) with
    | none => false
    | some fs => fs.all fun e => gfaceB O c.A c.C q.2.2 e

/-- The propagation condition of one rectangle in `GCert.ok`. -/
def GCert.propB (O : GOr) (c : GCert) (q : GRect × ℕ × List (List GHP)) : Bool :=
  q.2.2.isEmpty || c.cs.all fun q' => gpropB O c.A q q'

/-- The check of the `k` local rectangles from index `i` on. -/
def GCert.okPart (NX NY : ℕ) (O : GOr) (c : GCert) (i k : ℕ) : Bool :=
  ((c.cs.drop i).take k).all fun q => c.locB NX NY O q && c.propB O q

theorem GCert.ok_of_parts {NX NY : ℕ} {O : GOr} {c : GCert} (h0 : c.okHead NX NY O = true)
    (k m : ℕ) (hm : c.cs.length ≤ m * k) (hp : ∀ i < m, c.okPart NX NY O (i * k) k = true) :
    c.ok NX NY O = true := by
  have hall : ∀ q ∈ c.cs, (c.locB NX NY O q && c.propB O q) = true := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; rw [Nat.mul_zero] at hm; omega
      · exact h
    have hi : j / k < m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hpi := List.all_eq_true.1 (hp _ hi)
    have hjk := Nat.div_add_mod j k
    have hmk := Nat.mod_lt j hk
    have hlen : j - j / k * k < ((c.cs.drop (j / k * k)).take k).length := by
      simp only [List.length_take, List.length_drop]
      rw [Nat.mul_comm] at hjk
      apply Nat.lt_min.2; constructor <;> omega
    have he : ((c.cs.drop (j / k * k)).take k)[j - j / k * k] = c.cs[j] := by
      simp only [List.getElem_take, List.getElem_drop]
      congr 1
      rw [Nat.mul_comm] at hjk
      omega
    rw [← he]
    exact hpi _ (List.getElem_mem hlen)
  have hloc : c.cs.all (c.locB NX NY O) = true := List.all_eq_true.2 fun q hq => by
    have := hall q hq; simp only [Bool.and_eq_true] at this; exact this.1
  have hprop : c.cs.all (c.propB O) = true := List.all_eq_true.2 fun q hq => by
    have := hall q hq; simp only [Bool.and_eq_true] at this; exact this.2
  unfold GCert.okHead at h0
  unfold GCert.ok
  rw [h0]
  simp only [Bool.true_and, Bool.and_eq_true]
  exact ⟨hloc, hprop⟩

/-! ### Hinted propagation

Most of the cost of `gpropB` lies in the search, in each cone of `q`, for a half-plane negative on
the intersection with `q'`: each candidate costs oracle evaluations.  A hint names the candidate;
an index out of range falls back to the second alternative of `gpropB`. -/

/-- `gpropB` with hints: `hs.getD k 0` is the index of a half-plane of the `k`-th cone of `q`. -/
def gpropH (O : GOr) (A : GRect) (q q' : GRect × ℕ × List (List GHP)) (hs : List ℕ) : Bool :=
  q.2.2.isEmpty ||
  match q.1.inter q'.1 with
  | none => true
  | some X =>
    (List.range q.2.2.length).all fun k =>
      (decide (hs.getD k 0 < (q.2.2.getD k []).length) &&
          ghNeg O A ((q.2.2.getD k []).getD (hs.getD k 0) (none, none)) X.corners) ||
        q'.2.2.any fun K' => K'.all fun h => decide (h ∈ q.2.2.getD k []) || ghNN O A h X.corners

theorem gpropB_of_H {O : GOr} {A : GRect} {q q' : GRect × ℕ × List (List GHP)} {hs : List ℕ}
    (h : gpropH O A q q' hs = true) : gpropB O A q q' = true := by
  unfold gpropH at h
  unfold gpropB
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [h, Bool.true_or]
  · cases hX : q.1.inter q'.1 with
    | none => simp
    | some X =>
      rw [hX] at h
      simp only at h
      refine Bool.or_eq_true_iff.2 (Or.inr ?_)
      simp only
      refine List.all_eq_true.2 fun K hK => ?_
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hK
      have hk' := List.all_eq_true.1 h k (List.mem_range.2 hk)
      rw [List.getD_eq_getElem _ _ hk] at hk'
      rcases Bool.or_eq_true_iff.1 hk' with h1 | h1
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        obtain ⟨hi, hn⟩ := h1
        rw [List.getD_eq_getElem _ _ hi] at hn
        exact Bool.or_eq_true_iff.2 (Or.inl (List.any_eq_true.2 ⟨_, List.getElem_mem hi, hn⟩))
      · exact Bool.or_eq_true_iff.2 (Or.inr h1)

/-- The propagation condition of `q` with hints `H.getD j []` for the `j`-th rectangle. -/
def GCert.propH (O : GOr) (c : GCert) (q : GRect × ℕ × List (List GHP)) (H : List (List ℕ)) :
    Bool :=
  q.2.2.isEmpty ||
    (List.range c.cs.length).all fun j => gpropH O c.A q (c.cs.getD j default) (H.getD j [])

theorem GCert.propB_of_H {O : GOr} {c : GCert} {q : GRect × ℕ × List (List GHP)}
    {H : List (List ℕ)} (h : c.propH O q H = true) : c.propB O q = true := by
  unfold GCert.propH at h
  unfold GCert.propB
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [h, Bool.true_or]
  · refine Bool.or_eq_true_iff.2 (Or.inr (List.all_eq_true.2 fun q' hq' => ?_))
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq'
    have := List.all_eq_true.1 h j (List.mem_range.2 hj)
    rw [List.getD_eq_getElem _ _ hj] at this
    exact gpropB_of_H this

/-- The check of the local rectangle `i` alone, with hints. -/
def GCert.okPart1H (NX NY : ℕ) (O : GOr) (c : GCert) (i : ℕ) (H : List (List ℕ)) : Bool :=
  match c.cs.drop i with
  | [] => true
  | q :: _ => c.locB NX NY O q && c.propH O q H

theorem GCert.okPart_of_H {NX NY : ℕ} {O : GOr} {c : GCert} {i : ℕ} (H : List (List ℕ))
    (h : c.okPart1H NX NY O i H = true) : c.okPart NX NY O i 1 = true := by
  unfold GCert.okPart1H at h
  unfold GCert.okPart
  cases hd : c.cs.drop i with
  | nil => simp
  | cons q l =>
    rw [hd] at h
    simp only [Bool.and_eq_true] at h
    simp only [List.take_succ_cons, List.take_zero, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true]
    exact ⟨h.1, GCert.propB_of_H h.2⟩

end

end ArtGallery.Orthogonal.Hard
