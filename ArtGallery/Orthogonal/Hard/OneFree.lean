module

public import ArtGallery.Orthogonal.Hard.RatEq
public import ArtGallery.Stade.PTimePoly

/-!
# Removing the constraints `x = 1`

The orthogonal construction takes *one-free* instances of ETR-INV-REV (no constraint `one x`).
A constraint `one x` at position `j` of `Φ` is replaced by `invGe x x` and `addLe x x (n + j)`
with the fresh variable `n + j` (`oneFree`): in `[1/2, 2]`, `x² ≥ 1` gives `x ≥ 1` and
`2x ≤ v_{n+j} ≤ 2` gives `x ≤ 1`; conversely `x = 1`, `v_{n+j} = 2` satisfies both.

* `oneFree_isGad`, `oneFree_varsLt`: the new instance is one-free, on `n + |Φ|` variables;
* **`oneFree_sat`**: it is solvable iff `Φ` is;
* `PT.oneFree`: the translation is polynomial-time.
-/

@[expose] public section

namespace ArtGallery.Orthogonal.Hard

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.ETRINVREV ArtGallery.Stade

/-- The one-free form of the constraint `c` at position `j` of an instance on `n` variables. -/
def oneFreeC (n j : ℕ) (c : Constraint) : List Constraint :=
  c.elim (fun x => [.invGe x x, .addLe x x (n + j)]) (fun x y => [.invGe x y])
    (fun x y => [.invRevLe x y]) (fun x y z => [.addLe x y z]) (fun x y z => [.addGe x y z])

/-- **The one-free form** of an instance on `n` variables. -/
def oneFree (n : ℕ) (Φ : List Constraint) : List Constraint :=
  Φ.zipIdx.flatMap fun p => oneFreeC n p.2 p.1

/-- The number of variables of the one-free form. -/
def oneFreeVars (n : ℕ) (Φ : List Constraint) : ℕ := n + Φ.length

theorem mem_oneFree {n : ℕ} {Φ : List Constraint} {c : Constraint} :
    c ∈ oneFree n Φ ↔ ∃ j, ∃ h : j < Φ.length, c ∈ oneFreeC n j Φ[j] := by
  unfold oneFree
  simp only [List.mem_flatMap, List.mem_zipIdx_iff_getElem?, Prod.exists]
  constructor
  · rintro ⟨d, j, hj, hc⟩
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hj
    exact ⟨j, h, hc⟩
  · rintro ⟨j, h, hc⟩
    exact ⟨_, j, List.getElem?_eq_getElem h, hc⟩

theorem oneFree_isGad (n : ℕ) (Φ : List Constraint) : ∀ c ∈ oneFree n Φ, isGad c = true := by
  intro c hc
  obtain ⟨j, h, hc⟩ := mem_oneFree.1 hc
  cases e : Φ[j] <;> simp only [e, oneFreeC, Constraint.elim, List.mem_cons,
    List.not_mem_nil, or_false] at hc <;> rcases hc with rfl | rfl <;> rfl

theorem oneFree_varsLt {n : ℕ} {Φ : List Constraint} (hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    ∀ c ∈ oneFree n Φ, c.VarsLt (oneFreeVars n Φ) := by
  intro c hc
  obtain ⟨j, h, hc⟩ := mem_oneFree.1 hc
  have hv := hΦ _ (List.getElem_mem h)
  unfold oneFreeVars
  cases e : Φ[j] <;> rw [e] at hv <;> simp only [e, oneFreeC, Constraint.elim, List.mem_cons,
    List.not_mem_nil, or_false] at hc <;> simp only [Constraint.VarsLt] at hv <;>
    rcases hc with rfl | rfl <;> simp only [Constraint.VarsLt] <;> omega

theorem holds_congrO {n : ℕ} {c : Constraint} (hc : c.VarsLt n) {v w : ℕ → ℝ}
    (h : ∀ i < n, v i = w i) : c.Holds v ↔ c.Holds w := by
  cases c with
  | one x => simp only [Constraint.Holds, h x hc]
  | invGe x y => simp only [Constraint.Holds, h x hc.1, h y hc.2]
  | invRevLe x y => simp only [Constraint.Holds, h x hc.1, h y hc.2]
  | addLe x y z => simp only [Constraint.Holds, h x hc.1, h y hc.2.1, h z hc.2.2]
  | addGe x y z => simp only [Constraint.Holds, h x hc.1, h y hc.2.1, h z hc.2.2]

/-- **The one-free form is solvable iff the instance is.** -/
theorem oneFree_sat {n : ℕ} {Φ : List Constraint} (hΦ : ∀ c ∈ Φ, c.VarsLt n) :
    Satisfiable (oneFree n Φ) ↔ Satisfiable Φ := by
  constructor
  · rintro ⟨w, hw, hs⟩
    refine ⟨w, hw, fun c hc => ?_⟩
    obtain ⟨j, h, rfl⟩ := List.getElem_of_mem hc
    have hin : ∀ d ∈ oneFreeC n j Φ[j], d.Holds w := fun d hd => hs d (mem_oneFree.2 ⟨j, h, hd⟩)
    cases e : Φ[j] with
    | one x =>
      rw [e] at hin
      have h1 := hin (.invGe x x) (by simp [oneFreeC, Constraint.elim])
      have h2 := hin (.addLe x x (n + j)) (by simp [oneFreeC, Constraint.elim])
      simp only [Constraint.Holds] at h1 h2 ⊢
      obtain ⟨a1, -⟩ := hw x
      obtain ⟨-, b2⟩ := hw (n + j)
      nlinarith
    | _ => rw [e] at hin; exact hin _ (by simp [oneFreeC, Constraint.elim])
  · rintro ⟨v, hv, hs⟩
    refine ⟨fun i => if i < n then v i else 2, fun i => ?_, fun c hc => ?_⟩
    · by_cases hi : i < n
      · simp only [hi, ↓reduceIte]; exact hv i
      · simp only [hi]; norm_num
    obtain ⟨j, h, hc⟩ := mem_oneFree.1 hc
    have hd := hΦ _ (List.getElem_mem h)
    have hh := hs _ (List.getElem_mem h)
    have hcg : ∀ d : Constraint, d.VarsLt n → d.Holds v → d.Holds fun i => if i < n then v i else 2 :=
      fun d hd h => (holds_congrO hd (fun i hi => by simp [hi])).1 h
    cases e : Φ[j] with
    | one x =>
      rw [e] at hc hd hh
      simp only [Constraint.VarsLt] at hd
      simp only [Constraint.Holds] at hh
      simp only [oneFreeC, Constraint.elim, List.mem_cons, List.not_mem_nil, or_false] at hc
      have hj : ¬ n + j < n := by omega
      rcases hc with rfl | rfl <;> simp only [Constraint.Holds, hd, hj, ↓reduceIte, hh] <;> norm_num
    | _ =>
      rw [e] at hc hd hh
      simp only [oneFreeC, Constraint.elim, List.mem_singleton] at hc
      subst hc
      exact hcg _ hd hh

/-! ### Polynomial time -/

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.oneFreeC {n j : α → ℕ} {c : α → Constraint} (hn : PT n)
    (hj : PT j) (hc : PT c) : PT (fun a => oneFreeC (n a) (j a) (c a)) := by
  unfold oneFreeC
  refine PT.revElim ?_ ?_ ?_ ?_ ?_ hc <;> fun_prop

@[fun_prop] protected theorem PT.oneFree {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => oneFree (n a) (Φ a)) := by
  unfold oneFree
  fun_prop

@[fun_prop] protected theorem PT.oneFreeVars {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => oneFreeVars (n a) (Φ a)) := by
  unfold oneFreeVars
  fun_prop

end ArtGallery.Orthogonal.Hard

end
