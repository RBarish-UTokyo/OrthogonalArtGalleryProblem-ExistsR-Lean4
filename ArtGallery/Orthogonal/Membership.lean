module

public import ArtGallery.Orthogonal.Spec
public import ArtGallery.FewVars.Main
public import ArtGallery.FewVars.BoundaryMain
public import ArtGallery.FewVars.BoundaryPointMain

/-!
# The orthogonal art gallery problems are in `∃ℝ`, with only guard variables

An orthogonal instance is an instance of the general problem whose polygon is orthogonal.  The
reductions conjoin the formulas of `ArtGallery/FewVars/` (whose only variables are the `2g` guard
coordinates) with the variable-free formula `orthCheck w`, which states that every edge of the
decoded polygon is horizontal or vertical: for the edge from `xᵢ/dᵢ` to `xⱼ/dⱼ` (and likewise for
the second coordinates) it compares `dⱼ · xᵢ` and `dᵢ · xⱼ`, written as integer constants.

Main results: `agpOrth_inER_guard_variables`, `agpOrthPointBoundary_inER_guard_variables`,
`agpOrthBoundaryPoint_inER_guard_variables` and the corresponding `InER` statements.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Orthogonal

open Complexity Complexity.PT ArtGallery.ETR ArtGallery.Membership ArtGallery.FewVars

/-! ### The orthogonality formula -/

/-- The edge from the vertex with digits `p` to the vertex with digits `q` is vertical or
horizontal, by cross-multiplication. -/
def edgeOrthD (p q : FracDigits) : Formula :=
  .or (.eq (.mul (bitsTerm q.2.1) (intTermD p.1)) (.mul (bitsTerm p.2.1) (intTermD q.1)))
    (.eq (.mul (bitsTerm q.2.2.2) (intTermD p.2.2.1))
      (.mul (bitsTerm p.2.2.2) (intTermD q.2.2.1)))

/-- Every edge of the polygon with vertex digits `D` is vertical or horizontal (the vertex list
`D` is paired with its rotation `D.drop 1 ++ D.take 1`). -/
def orthFD (D : List FracDigits) : Formula :=
  bigAnd (List.zipWith edgeOrthD D (D.drop 1 ++ D.take 1))

/-- The orthogonality test of an instance code (true for words that are not codes). -/
def orthCheck (w : Word) : Formula :=
  match ArtGallery.decodeAGP w with
  | none => fTrue
  | some (D, _) => orthFD D

/-- A reduction to ETR, strengthened by the orthogonality test. -/
def withOrth (F : Word → Formula) (w : Word) : Formula := .and (F w) (orthCheck w)

/-! ### Correctness of the test -/

/-- The cross-multiplied edge condition. -/
def EdgeQ (p q : FracPoint) : Prop :=
  (q.xDen : ℤ) * p.xNum = p.xDen * q.xNum ∨ (q.yDen : ℤ) * p.yNum = p.yDen * q.yNum

theorem cast_cross_iff (a b : ℕ) (c d : ℤ) :
    ((a : ℝ) * (c : ℝ) = (b : ℝ) * (d : ℝ)) ↔ (a : ℤ) * c = b * d := by
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem holds_edgeOrthD (x : ℕ → ℝ) (p q : FracPoint) :
    (edgeOrthD p.digits q.digits).Holds x ↔ EdgeQ p q := by
  simp only [edgeOrthD, FracPoint.digits, Formula.Holds, Term.eval, eval_intTermD_intDigits,
    eval_bitsTerm_bits, EdgeQ, cast_cross_iff]

theorem drop_append_take_one {β : Type} (l : List β) : l.drop 1 ++ l.take 1 = l.rotate 1 := by
  cases l with
  | nil => rfl
  | cons a l => simp [List.rotate_cons_succ]

theorem holds_orthFD (x : ℕ → ℝ) (V : List FracPoint) :
    (orthFD (V.map FracPoint.digits)).Holds x ↔
      ∀ (i : ℕ) (h : i < V.length),
        EdgeQ V[i] (V[(i + 1) % V.length]'(Nat.mod_lt _ (by omega))) := by
  rw [orthFD, holds_bigAnd, drop_append_take_one, List.forall_mem_iff_getElem]
  simp only [List.length_zipWith, List.length_rotate, List.length_map, min_self,
    List.getElem_zipWith, List.getElem_rotate, List.getElem_map, holds_edgeOrthD]

theorem polyOf_vtx (V : List FracPoint) (i : ℕ) (h : i < V.length) :
    (polyOf V).vtx i = V[i].toPoint := by
  simp [polyOf, Polygon.vtx, List.getD_eq_getElem?_getD, h]

theorem edgeQ_iff {p q : FracPoint} (hp : p.Valid) (hq : q.Valid) :
    EdgeQ p q ↔ p.toPoint.1 = q.toPoint.1 ∨ p.toPoint.2 = q.toPoint.2 := by
  have key : ∀ (a b : ℤ) (c d : ℕ), 0 < c → 0 < d →
      ((d : ℤ) * a = c * b ↔ (a : ℝ) / c = (b : ℝ) / d) := by
    intro a b c d hc hd
    have hc' : (c : ℝ) ≠ 0 := by positivity
    have hd' : (d : ℝ) ≠ 0 := by positivity
    rw [div_eq_div_iff hc' hd']
    constructor
    · intro h
      have h' : ((d : ℤ) : ℝ) * a = ((c : ℤ) : ℝ) * b := by exact_mod_cast h
      push_cast at h'
      linarith
    · intro h
      have h' : ((d : ℤ) : ℝ) * a = ((c : ℤ) : ℝ) * b := by push_cast; linarith
      exact_mod_cast h'
  simp only [EdgeQ, FracPoint.toPoint, key _ _ _ _ hp.1 hq.1, key _ _ _ _ hp.2 hq.2]

theorem orthogonal_iff {V : List FracPoint} (hV : ∀ p ∈ V, p.Valid) :
    (polyOf V).Orthogonal ↔
      ∀ (i : ℕ) (h : i < V.length),
        EdgeQ V[i] (V[(i + 1) % V.length]'(Nat.mod_lt _ (by omega))) := by
  rw [Polygon.Orthogonal, polyOf_n]
  refine forall_congr' fun i => ⟨fun h hi => ?_, fun h hi => ?_⟩
  · have hj : (i + 1) % V.length < V.length := Nat.mod_lt _ (by omega)
    have := h hi
    rw [polyOf_vtx V i hi, polyOf_vtx V _ hj] at this
    exact (edgeQ_iff (hV _ (List.getElem_mem hi)) (hV _ (List.getElem_mem hj))).2 this
  · have hj : (i + 1) % V.length < V.length := Nat.mod_lt _ (by omega)
    rw [polyOf_vtx V i hi, polyOf_vtx V _ hj]
    exact (edgeQ_iff (hV _ (List.getElem_mem hi)) (hV _ (List.getElem_mem hj))).1 (h hi)

theorem orthCheck_encodeAGP (x : ℕ → ℝ) (V : List FracPoint) (g : ℕ) :
    (orthCheck (encodeAGP V g)).Holds x ↔
      ∀ (i : ℕ) (h : i < V.length),
        EdgeQ V[i] (V[(i + 1) % V.length]'(Nat.mod_lt _ (by omega))) := by
  simp only [orthCheck, ArtGallery.decodeAGP_encodeAGP]
  exact holds_orthFD x V

/-- **Correctness of the strengthened reduction**, for a language `L` of instances
`(V, g)` with valid vertices and a property `Q`, and its orthogonal restriction `Lo`. -/
theorem withOrth_correct {L Lo : Language} {F : Word → Formula}
    {Q : List FracPoint → ℕ → Prop}
    (hF : ∀ w, L w ↔ (F w).Satisfiable)
    (hL : ∀ w, L w ↔ ∃ (V : List FracPoint) (g : ℕ), encodeAGP V g = w ∧
      (∀ p ∈ V, p.Valid) ∧ Q V g)
    (hLo : ∀ w, Lo w ↔ ∃ (V : List FracPoint) (g : ℕ), encodeAGP V g = w ∧
      (∀ p ∈ V, p.Valid) ∧ (polyOf V).Orthogonal ∧ Q V g) (w : Word) :
    Lo w ↔ (withOrth F w).Satisfiable := by
  rw [hLo]
  constructor
  · rintro ⟨V, g, rfl, hV, hO, hQ⟩
    obtain ⟨x, hx⟩ := (hF _).1 ((hL _).2 ⟨V, g, rfl, hV, hQ⟩)
    exact ⟨x, hx, (orthCheck_encodeAGP x V g).2 ((orthogonal_iff hV).1 hO)⟩
  · rintro ⟨x, hx, hc⟩
    obtain ⟨V, g, rfl, hV, hQ⟩ := (hL _).1 ((hF _).2 ⟨x, hx⟩)
    exact ⟨V, g, rfl, hV, (orthogonal_iff hV).2 ((orthCheck_encodeAGP x V g).1 hc), hQ⟩

/-! ### Variables -/

theorem varsLt_bitsTerm (n : ℕ) (l : List Bool) : (bitsTerm l).VarsLt n := by
  induction l with
  | nil => trivial
  | cons b l ih => cases b <;> exact ⟨trivial, ⟨trivial, trivial⟩, ih⟩

theorem varsLt_intTermD (n : ℕ) (p : Bool × Word) : (intTermD p).VarsLt n := by
  unfold intTermD
  split
  · exact ⟨trivial, varsLt_bitsTerm n _⟩
  · exact varsLt_bitsTerm n _

theorem varsLt_bigAnd (n : ℕ) (l : List Formula) (h : ∀ φ ∈ l, φ.VarsLt n) :
    (bigAnd l).VarsLt n := by
  induction l with
  | nil => exact ⟨trivial, trivial⟩
  | cons φ l ih =>
    exact ⟨h φ (by simp), ih fun ψ hψ => h ψ (by simp [hψ])⟩

theorem forall_mem_zipWith {β γ δ : Type} {P : δ → Prop} (f : β → γ → δ)
    (hf : ∀ b c, P (f b c)) : ∀ (l : List β) (m : List γ), ∀ d ∈ List.zipWith f l m, P d
  | [], _ => by simp
  | _ :: _, [] => by simp
  | b :: l, c :: m => by
    intro d hd
    rw [List.zipWith_cons_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact hf b c
    · exact forall_mem_zipWith f hf l m d hd

theorem varsLt_edgeOrthD (n : ℕ) (p q : FracDigits) : (edgeOrthD p q).VarsLt n :=
  ⟨⟨⟨varsLt_bitsTerm n _, varsLt_intTermD n _⟩, ⟨varsLt_bitsTerm n _, varsLt_intTermD n _⟩⟩,
    ⟨⟨varsLt_bitsTerm n _, varsLt_intTermD n _⟩, ⟨varsLt_bitsTerm n _, varsLt_intTermD n _⟩⟩⟩

theorem varsLt_orthCheck (n : ℕ) (w : Word) : (orthCheck w).VarsLt n := by
  unfold orthCheck
  split
  · exact ⟨trivial, trivial⟩
  · exact varsLt_bigAnd n _ (forall_mem_zipWith _ (varsLt_edgeOrthD n) _ _)

/-! ### Polynomial time -/

section PTLemmas

variable {α : Type} [Code α]

@[fun_prop] protected theorem PT.edgeOrthD {p q : α → FracDigits} (hp : PT p) (hq : PT q) :
    PT (fun a => edgeOrthD (p a) (q a)) := by
  unfold edgeOrthD; fun_prop

@[fun_prop] protected theorem PT.orthFD {D : α → List FracDigits} (hD : PT D) :
    PT (fun a => orthFD (D a)) := by
  unfold orthFD; fun_prop

end PTLemmas

protected theorem PT.orthCheck : PT orthCheck := by
  refine PT.of_optionCases (o := ArtGallery.decodeAGP) (d := fun _ => fTrue)
    (f := fun _ r => orthFD r.1) (PT.decodeAGP PT.id) (PT.const _) (by fun_prop) ?_ ?_
  · intro w h; simp [orthCheck, h]
  · intro w r h; obtain ⟨D, gd⟩ := r; simp [orthCheck, h]

protected theorem PT.withOrth {F : Word → Formula} (hF : PT F) : PT (withOrth F) := by
  unfold withOrth
  have := PT.orthCheck
  fun_prop

end ArtGallery.Orthogonal

end
