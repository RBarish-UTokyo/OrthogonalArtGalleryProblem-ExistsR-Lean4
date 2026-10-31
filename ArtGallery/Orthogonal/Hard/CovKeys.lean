module

public import ArtGallery.Orthogonal.Hard.CovGroup
public import ArtGallery.Orthogonal.Hard.PropHint

/-!
# Coverage item checks with integer keys

`GroupCov.itemB` tests every item against every forbidden rectangle of its group; the test
`CItem.offB` first compares the bounding box of the item with the rectangle in rationals.  Here
the boxes of the items and the forbidden rectangles carry integer keys (`Key`,
`ArtGallery/Orthogonal/Hard/PropHint.lean`), checked once per group by `keysOK`; the box test is a
comparison of natural numbers (`offK`), and `CItem.offB` is evaluated only for the rectangles that
are not separated from the box.  `idxAll_itemB_of_K` derives the item checks.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

/-- The boxes with keys `kb` and `kr` are separated (closed half-planes). -/
def offK (kb kr : Key) : Bool :=
  Nat.ble kb.2.1 kr.1 || Nat.ble kr.2.1 kb.1 ||
    (Nat.ble kb.2.2.2.2.1 kr.2.2.1 && Nat.ble kb.2.2.2.2.2 kr.2.2.2.1) ||
    (Nat.ble kr.2.2.2.2.1 kb.2.2.1 && Nat.ble kr.2.2.2.2.2 kb.2.2.2.1)

theorem offK_offB {P : KeyP} (hL : 0 < P.L) {it : CItem} {R : LR} {kb kr : Key}
    (hkb : keyEqB P it.box kb = true) (hkr : keyEqB P R kr = true) (h : offK kb kr = true) :
    it.offB R = true := by
  simp only [keyEqB, Bool.and_eq_true, decide_eq_true_eq] at hkb hkr
  obtain ⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩ := hkb
  obtain ⟨⟨⟨⟨⟨b0, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩ := hkr
  have hL' : (0 : ℚ) < P.L := by exact_mod_cast hL
  simp only [offK, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  simp only [CItem.offB, AH.le, AH.nn, Bool.or_eq_true, decide_eq_true_eq]
  rcases h with ((h | h) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · have : (kb.2.1 : ℚ) ≤ kr.1 := by exact_mod_cast h
    left; left; left; left
    by_contra hc
    have : R.x0 * P.L < it.box.x1 * P.L := mul_lt_mul_of_pos_right (not_le.1 hc) hL'
    linarith
  · have : (kr.2.1 : ℚ) ≤ kb.1 := by exact_mod_cast h
    left; left; left; right
    by_contra hc
    have : it.box.x0 * P.L < R.x1 * P.L := mul_lt_mul_of_pos_right (not_le.1 hc) hL'
    linarith
  · have e1 : (kb.2.2.2.2.1 : ℚ) ≤ kr.2.2.1 := by exact_mod_cast h1
    have e2 : (kb.2.2.2.2.2 : ℚ) ≤ kr.2.2.2.1 := by exact_mod_cast h2
    left; left; right
    constructor
    · by_contra hc
      have : R.y0.2 * P.L < it.box.y1.2 * P.L :=
        mul_lt_mul_of_pos_right (by linarith [not_le.1 hc]) hL'
      linarith
    · by_contra hc
      have : (R.y0.1 + R.y0.2 * 1000) * P.L < (it.box.y1.1 + it.box.y1.2 * 1000) * P.L :=
        mul_lt_mul_of_pos_right (by linarith [not_le.1 hc]) hL'
      linarith
  · have e1 : (kr.2.2.2.2.1 : ℚ) ≤ kb.2.2.1 := by exact_mod_cast h1
    have e2 : (kr.2.2.2.2.2 : ℚ) ≤ kb.2.2.2.1 := by exact_mod_cast h2
    left; right
    constructor
    · by_contra hc
      have : it.box.y0.2 * P.L < R.y1.2 * P.L :=
        mul_lt_mul_of_pos_right (by linarith [not_le.1 hc]) hL'
      linarith
    · by_contra hc
      have : (it.box.y0.1 + it.box.y0.2 * 1000) * P.L < (R.y1.1 + R.y1.2 * 1000) * P.L :=
        mul_lt_mul_of_pos_right (by linarith [not_le.1 hc]) hL'
      linarith

/-- The rectangles of a list with an index (for `keysOK`). -/
def withZero (rs : List LR) : List (LR × ℕ) := rs.map fun r => (r, 0)

/-- The checks of item `k` with keys: `kf` the keys of the forbidden rectangles, `ki` those of
the boxes of the items. -/
def GroupCov.itemK (c : GroupCov) (kf ki : List Key) (k : ℕ) : Bool :=
  let it := c.items.getD k CItem.dflt
  let kb := ki.getD k Key.dflt
  it.innerB &&
    (AH.le c.frame.F.y0 it.box.y0 && AH.le it.box.y1 c.frame.F.y1 &&
      decide (c.frame.F.x0 ≤ it.box.x0) && decide (it.box.x1 ≤ c.frame.F.x1)) &&
    (c.frame.forb.zip kf).all fun p => offK kb p.2 || it.offB p.1

theorem keysOK_mem {P : KeyP} {rs : List LR} {ks : List Key} (h : keysOK P (withZero rs) ks = true) :
    0 < P.L ∧ ks.length = rs.length ∧ ∀ p ∈ rs.zip ks, keyEqB P p.1 p.2 = true := by
  simp only [keysOK, withZero, Bool.and_eq_true, decide_eq_true_eq, List.length_map,
    List.all_eq_true] at h
  obtain ⟨⟨hL, hl⟩, h⟩ := h
  refine ⟨hL, hl, fun p hp => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hi' : i < ((rs.map fun r => (r, 0)).zip ks).length := by simpa using hi
  have := h _ (List.getElem_mem hi')
  simpa [List.getElem_zip] using this

theorem GroupCov.itemB_of_K {c : GroupCov} {P : KeyP} {kf ki : List Key}
    (hf : keysOK P (withZero c.frame.forb) kf = true)
    (hi : keysOK P (withZero (c.items.map CItem.box)) ki = true) {k : ℕ} (hk : k < c.items.length)
    (h : c.itemK kf ki k = true) : c.itemB k = true := by
  obtain ⟨hL, hfl, hf⟩ := keysOK_mem hf
  obtain ⟨-, hil, hi⟩ := keysOK_mem hi
  have hkb : keyEqB P (c.items.getD k CItem.dflt).box (ki.getD k Key.dflt) = true := by
    have hk' : k < ((c.items.map CItem.box).zip ki).length := by
      simp only [List.length_zip, List.length_map, hil]; omega
    have := hi _ (List.getElem_mem hk')
    have hki : k < ki.length := by rw [hil, List.length_map]; exact hk
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hki]
    simpa [List.getElem_zip] using this
  simp only [GroupCov.itemK, Bool.and_eq_true] at h
  simp only [GroupCov.itemB, Bool.and_eq_true]
  refine ⟨h.1, List.all_eq_true.2 fun R hR => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hR
  have hj' : j < (c.frame.forb.zip kf).length := by
    simp only [List.length_zip, hfl]; omega
  have := List.all_eq_true.1 h.2 _ (List.getElem_mem hj')
  simp only [List.getElem_zip, Bool.or_eq_true] at this
  rcases this with h1 | h1
  · have hr := hf _ (List.getElem_mem hj')
    simp only [List.getElem_zip] at hr
    exact offK_offB hL hkb hr h1
  · exact h1

/-- **The item checks from their keyed form** (for a range of items within the list). -/
theorem idxAll_itemB_of_K {c : GroupCov} {P : KeyP} {kf ki : List Key}
    (hf : keysOK P (withZero c.frame.forb) kf = true)
    (hi : keysOK P (withZero (c.items.map CItem.box)) ki = true) {a b : ℕ}
    (hb : b ≤ c.items.length) (h : idxAll (c.itemK kf ki) a b = true) :
    idxAll c.itemB a b = true := by
  unfold idxAll at *
  rw [List.all_eq_true] at *
  intro k hk
  have hkb := List.mem_range'_1.1 hk
  exact GroupCov.itemB_of_K hf hi (by omega) (h k hk)

end

end ArtGallery.Orthogonal.Hard
