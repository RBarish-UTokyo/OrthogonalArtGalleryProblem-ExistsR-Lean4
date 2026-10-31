module

public import ArtGallery.Orthogonal.Hard.Simple
public import ArtGallery.Orthogonal.Spec

/-!
# The orthogonal polygon is orthogonal

**Main result.** `orthogonalO n Φ : (Polygon.mk ((polyO n Φ).map ratPoint)).Orthogonal`.

Consecutive vertices of every template share a coordinate, and its end points lie on the floor
`y = −1` or the ceiling `y = 2H` (checked on the integer data, `tmplOrth_ok`); the same holds for
the grid of the copy nook (`cnGrid_orth`).  Between the features the polygon runs along the floor
and the ceiling, and the walls are vertical.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.ETRINVREV ArtGallery.Stade ArtGallery.Stade.Chain

/-- Two rational points share a coordinate. -/
def OStep (p q : ℚ × ℚ) : Prop := p.1 = q.1 ∨ p.2 = q.2

/-- `r` holds for every pair of consecutive elements. -/
def chainB {α : Type} (r : α → α → Bool) : List α → Bool
  | a :: b :: l => r a b && chainB r (b :: l)
  | _ => true

theorem chainB_sound {α : Type} {r : α → α → Bool} {R : α → α → Prop}
    (hr : ∀ a b, r a b = true → R a b) : ∀ {l : List α}, chainB r l = true → l.IsChain R
  | [], _ => List.IsChain.nil
  | [_], _ => List.IsChain.singleton _
  | a :: b :: l, h => by
    simp only [chainB, Bool.and_eq_true] at h
    exact List.IsChain.cons_cons (hr a b h.1) (chainB_sound hr h.2)

/-! ### Closed chains -/

/-- A polygon whose vertex list is a chain of axis-parallel steps, closed by an axis-parallel
step, is orthogonal. -/
theorem orthogonal_of_chain {l : List (ℚ × ℚ)} (hne : l ≠ []) (hc : l.IsChain OStep)
    (hlast : OStep (l.getLast hne) (l.head hne)) : (Polygon.mk (l.map ratPoint)).Orthogonal := by
  intro i hi
  simp only [Polygon.n, List.length_map] at hi
  have hcast : ∀ p q : ℚ × ℚ, OStep p q →
      (ratPoint p).1 = (ratPoint q).1 ∨ (ratPoint p).2 = (ratPoint q).2 := by
    rintro p q (h | h)
    · left; simp [ratPoint, h]
    · right; simp [ratPoint, h]
  simp only [Polygon.vtx, Polygon.n, List.length_map]
  rcases Nat.lt_or_ge (i + 1) l.length with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using h1)]
    simp only [List.getElem_map]
    exact hcast _ _ (List.isChain_iff_getElem.1 hc i h1)
  · have hi' : i + 1 = l.length := by omega
    rw [hi', Nat.mod_self, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simp [List.length_pos_iff.2 hne])]
    simp only [List.getElem_map]
    have e1 : l[i] = l.getLast hne := by
      rw [List.getLast_eq_getElem]; congr 1; omega
    have e2 : l[0] = l.head hne := List.getElem_zero _
    rw [e1, e2]
    exact hcast _ _ hlast

/-! ### Features on a line -/

/-- A feature of the line `y = y₀`: nonempty, a chain of axis-parallel steps, with both end
points on the line. -/
def LineFeat (y₀ : ℚ) (f : List (ℚ × ℚ)) : Prop :=
  ∃ h : f ≠ [], f.IsChain OStep ∧ (f.head h).2 = y₀ ∧ (f.getLast h).2 = y₀

theorem comb_chain {y₀ : ℚ} (b : ℚ × ℚ) (hb : b.2 = y₀) :
    ∀ (fs : List (List (ℚ × ℚ))) (a : ℚ × ℚ), a.2 = y₀ → (∀ f ∈ fs, LineFeat y₀ f) →
      (a :: (fs.flatten ++ [b])).IsChain OStep
  | [], a, ha, _ => by
    simp only [List.flatten_nil, List.nil_append]
    exact List.IsChain.cons_cons (Or.inr (ha.trans hb.symm)) (List.IsChain.singleton _)
  | f :: fs, a, ha, hF => by
    obtain ⟨hne, hc, hh, hl⟩ := hF f (by simp)
    have ih := comb_chain b hb fs (f.getLast hne) hl (fun g hg => hF g (by simp [hg]))
    have e : a :: ((f :: fs).flatten ++ [b]) = (a :: f) ++ (fs.flatten ++ [b]) := by simp
    rw [e]
    have hfa : (a :: f).IsChain OStep := by
      obtain ⟨c, l, rfl⟩ := List.exists_cons_of_ne_nil hne
      exact List.IsChain.cons_cons (Or.inr (ha.trans hh.symm)) hc
    refine hfa.append ih.tail ?_
    intro x hx y hy
    have hx' : x = f.getLast hne := by
      rw [List.getLast?_cons, Option.mem_def, List.getLast?_eq_some_getLast hne] at hx
      simp only [Option.getD_some, Option.some.injEq] at hx
      exact hx.symm
    subst hx'
    have := List.isChain_cons.1 ih
    exact this.1 y hy

/-! ### Checks on the data -/

/-- Consecutive template vertices share the abscissa or the ordinate (for every `H`), and the end
points have the ordinate key `e`. -/
def tOrthB (e : ℤ × ℤ) (t : ITmpl) : Bool :=
  chainB (fun p q => decide (p.1 = q.1 ∨ p.2 = q.2)) t.pts &&
  (match t.pts.head?, t.pts.getLast? with
   | some a, some z => decide (a.2 = e ∧ z.2 = e)
   | _, _ => false)

theorem tmplOrth_ok :
    (allFloorTmpls.all (fun t => tOrthB (-(t.D : ℤ), 0) t) &&
      allCeilTmpls.all (fun t => tOrthB (0, -2 * (t.D : ℤ)) t)) = true := by
  decide +kernel

theorem cnGrid_orth : chainB (fun p q => decide (p.1 = q.1 ∨ p.2 = q.2)) cnGrid = true := by
  decide

theorem tOrthB_lineFeat {e : ℤ × ℤ} {t : ITmpl} (h : tOrthB e t = true) (H ox : ℚ) :
    LineFeat ((e.1 : ℚ) / t.D - (e.2 : ℚ) / t.D * H) (t.inst H ox) := by
  simp only [tOrthB, Bool.and_eq_true] at h
  obtain ⟨hc, he⟩ := h
  cases ha : t.pts.head? with
  | none => rw [ha] at he; simp at he
  | some a =>
    cases hz : t.pts.getLast? with
    | none => rw [ha, hz] at he; simp at he
    | some z =>
      rw [ha, hz] at he
      simp only [decide_eq_true_eq] at he
      have hne : t.pts ≠ [] := by intro h0; rw [h0] at ha; simp at ha
      have hne' : t.inst H ox ≠ [] := by simpa [ITmpl.inst] using hne
      refine ⟨hne', ?_, ?_, ?_⟩
      · have := chainB_sound (R := fun p q : ℤ × ℤ × ℤ => p.1 = q.1 ∨ p.2 = q.2)
          (fun a b h => of_decide_eq_true h) hc
        unfold ITmpl.inst
        rw [List.isChain_map]
        refine this.imp (fun p q hpq => ?_)
        rcases hpq with h1 | h2
        · left; simp [h1]
        · right; simp [h2]
      · have : (t.inst H ox).head hne' = (ox + (a.1 : ℚ) / t.D,
            (a.2.1 : ℚ) / t.D - (a.2.2 : ℚ) / t.D * H) := by
          rw [List.head_eq_iff_head?_eq_some]
          simp [ITmpl.inst, List.head?_map, ha]
        rw [this, he.1]
      · have : (t.inst H ox).getLast hne' = (ox + (z.1 : ℚ) / t.D,
            (z.2.1 : ℚ) / t.D - (z.2.2 : ℚ) / t.D * H) := by
          rw [List.getLast_eq_iff_getLast?_eq_some]
          simp [ITmpl.inst, List.getLast?_map, hz]
        rw [this, he.2]

variable {n : ℕ} {Φ : List Constraint}

theorem floorTmpl_line {t : ITmpl} (ht : t ∈ allFloorTmpls) (H ox : ℚ) (hD : 0 < t.D) :
    LineFeat (-1) (t.inst H ox) := by
  have h := tmplOrth_ok
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have := tOrthB_lineFeat (h.1 t ht) H ox
  have e : ((-(t.D : ℤ) : ℤ) : ℚ) / t.D - ((0 : ℤ) : ℚ) / t.D * H = -1 := by
    have : (t.D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast; field_simp; ring
  rwa [e] at this

theorem ceilTmpl_line {t : ITmpl} (ht : t ∈ allCeilTmpls) (H ox : ℚ) (hD : 0 < t.D) :
    LineFeat (2 * H) (t.inst H ox) := by
  have h := tmplOrth_ok
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have := tOrthB_lineFeat (h.2 t ht) H ox
  have e : ((0 : ℤ) : ℚ) / t.D - ((-2 * (t.D : ℤ) : ℤ) : ℚ) / t.D * H = 2 * H := by
    have : (t.D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast; field_simp; ring
  rwa [e] at this

theorem floorTmpl_D {t : ITmpl} (ht : t ∈ allFloorTmpls) : 0 < t.D := by
  have := floorTmpls_ok
  simp only [List.all_eq_true] at this
  have h := this t ht
  simp only [floorOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

theorem ceilTmpl_D {t : ITmpl} (ht : t ∈ allCeilTmpls) : 0 < t.D := by
  have := ceilTmpls_ok
  simp only [List.all_eq_true] at this
  have h := this t ht
  simp only [ceilOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

theorem cnPts_line (xN u G e H : ℚ) : LineFeat (2 * H) (cnPts xN u G e H) := by
  have hne : cnPts xN u G e H ≠ [] := by simp [cnPts, cnGrid]
  refine ⟨hne, ?_, ?_, ?_⟩
  · have := chainB_sound (R := fun p q : ℕ × ℕ => p.1 = q.1 ∨ p.2 = q.2)
      (fun a b h => of_decide_eq_true h) cnGrid_orth
    unfold cnPts
    rw [List.isChain_map]
    refine this.imp (fun p q hpq => ?_)
    rcases hpq with h1 | h2
    · left; simp [h1]
    · right; simp [h2]
  · simp [cnPts, cnGrid, cnYs]
  · simp [cnPts, cnGrid, cnYs]

theorem floor_lineO : ∀ f ∈ floorFeatsO n Φ, LineFeat (-1) f := by
  intro f hf
  rcases mem_floorFeatsO hf with rfl | ⟨k, hk, t, ht, rfl⟩ | ⟨c, hc, t, ht, rfl⟩
  · exact floorTmpl_line List.mem_cons_self _ _ (floorTmpl_D List.mem_cons_self)
  · exact floorTmpl_line (mem_allFloorTmpls_var ht) _ _ (floorTmpl_D (mem_allFloorTmpls_var ht))
  · exact floorTmpl_line (mem_allFloorTmpls_slot ht) _ _
      (floorTmpl_D (mem_allFloorTmpls_slot ht))

theorem ceil_lineO : ∀ f ∈ ceilFeatsO n Φ, LineFeat (2 * (paramH n Φ : ℚ)) f := by
  intro f hf
  rcases mem_ceilFeatsO hf with ⟨i, hi, t, ht, rfl⟩ | ⟨k, hk, t, ht, rfl⟩ | ⟨k, hk, i, hi, rfl⟩
  · exact ceilTmpl_line (mem_allCeilTmpls_input ht) _ _ (ceilTmpl_D (mem_allCeilTmpls_input ht))
  · exact ceilTmpl_line (mem_allCeilTmpls_var ht) _ _ (ceilTmpl_D (mem_allCeilTmpls_var ht))
  · rw [copyNookO_eq]; exact cnPts_line _ _ _ _ _

/-- **The orthogonal polygon is orthogonal.** -/
theorem orthogonalO (n : ℕ) (Φ : List Constraint) :
    (Polygon.mk ((polyO n Φ).map ratPoint)).Orthogonal := by
  have hne : polyO n Φ ≠ [] := by simp [polyO]
  have hfl := comb_chain (y₀ := -1) (xR n Φ, -1) rfl (floorFeatsO n Φ) (xL n Φ, -1) rfl
    floor_lineO
  have hcl := comb_chain (y₀ := 2 * (paramH n Φ : ℚ)) (xL n Φ, 2 * (paramH n Φ : ℚ)) rfl
    (ceilFeatsO n Φ) (xR n Φ, 2 * (paramH n Φ : ℚ)) rfl ceil_lineO
  have e : polyO n Φ = ((xL n Φ, -1) :: ((floorFeatsO n Φ).flatten ++ [(xR n Φ, -1)])) ++
      ((xR n Φ, 2 * (paramH n Φ : ℚ)) ::
        ((ceilFeatsO n Φ).flatten ++ [(xL n Φ, 2 * (paramH n Φ : ℚ))])) := by
    simp [polyO]
  refine orthogonal_of_chain hne ?_ ?_
  · rw [e]
    refine hfl.append hcl ?_
    intro x hx y hy
    have hx' : x = (xR n Φ, -1) := by
      simpa [List.getLast?_cons, List.getLast?_append] using hx.symm
    have hy' : y = (xR n Φ, 2 * (paramH n Φ : ℚ)) := by simpa using hy.symm
    subst hx' hy'
    left; rfl
  · have h1 : (polyO n Φ).getLast hne = (xL n Φ, 2 * (paramH n Φ : ℚ)) := by
      simp [polyO]
    have h2 : (polyO n Φ).head hne = (xL n Φ, -1) := by simp [polyO]
    rw [h1, h2]
    left; rfl

end

end ArtGallery.Orthogonal.Hard
