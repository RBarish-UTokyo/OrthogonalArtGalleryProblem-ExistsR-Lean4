module

public import ArtGallery.Orthogonal.Hard.CovMain
public import ArtGallery.Orthogonal.Hard.SoundO
public import ArtGallery.Orthogonal.Hard.PTimePolyO
public import ArtGallery.Orthogonal.Hard.OneFree
public import ArtGallery.Orthogonal.Spec
public import ArtGallery.Stade.Main

/-!
# ETR reduces in polynomial time to `AGPOrth` and to `AGPOrthPointBoundary`

A formula `φ` goes to the ETR-INV-REV instance `etrToREV φ` on `etrToREVVars φ` variables
(Stade's reduction), then to its one-free form (`oneFree`, on `oneFreeVars` variables), then to the
orthogonal polygon `polyO n Φ` with `guardsO n Φ` guards, each coordinate written as the fraction
of its normal form.  The polygon is simple (`simpleO`) and orthogonal (`orthogonalO`), and

* completeness (`guardSetO_of_sat`): a solution gives a guard set of `guardsO n Φ` points;
* soundness (`sat_of_boundaryGuardO`): a boundary guard set of `guardsO n Φ` points gives a
  solution;

so `Φ` is solvable iff the polygon has a guard set of cardinality `guardsO n Φ`, iff it has a
boundary guard set of that cardinality (`sat_iff_hasGuardSetOfCardO`,
`sat_iff_hasBoundaryGuardSetOfCardO`).  A word that is not the code of a formula goes to the code
of the empty polygon (not simple).

Main results: **`etr_polyRed_agpOrth`** and **`etr_polyRed_agpOrthPointBoundary`**.
-/

@[expose] public section

namespace ArtGallery.Orthogonal.Hard

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.ETRINVREV ArtGallery.Stade

/-! ### Correctness of the polygon -/

/-- **Solvable iff guardable** (point-point), for one-free instances. -/
theorem sat_iff_hasGuardSetOfCardO (n : ℕ) (Φ : List Constraint) (hΦ : ∀ c ∈ Φ, c.VarsLt n)
    (hone : ∀ c ∈ Φ, isGad c = true) (hn : 0 < n) :
    Satisfiable Φ ↔ (Polygon.mk ((polyO n Φ).map ratPoint)).HasGuardSetOfCard (guardsO n Φ) := by
  constructor
  · rintro ⟨v, hv, hs⟩
    obtain ⟨G, hG, hGS⟩ := guardSetO_of_sat hΦ hn hv hs
    exact ⟨G, hG, hGS⟩
  · rintro ⟨G, hG, hGS⟩
    obtain ⟨v, hv, hs, -⟩ :=
      sat_of_boundaryGuardO n Φ hΦ hone G (isBoundaryGuardSet_of_isGuardSet hGS) hG
    exact sat_of_restricted hΦ hv hs

/-- **Solvable iff the boundary is guardable** (point-boundary), for one-free instances. -/
theorem sat_iff_hasBoundaryGuardSetOfCardO (n : ℕ) (Φ : List Constraint)
    (hΦ : ∀ c ∈ Φ, c.VarsLt n) (hone : ∀ c ∈ Φ, isGad c = true) (hn : 0 < n) :
    Satisfiable Φ ↔
      (Polygon.mk ((polyO n Φ).map ratPoint)).HasBoundaryGuardSetOfCard (guardsO n Φ) := by
  constructor
  · rintro ⟨v, hv, hs⟩
    obtain ⟨G, hG, hGS⟩ := guardSetO_of_sat hΦ hn hv hs
    exact ⟨G, hG, isBoundaryGuardSet_of_isGuardSet hGS⟩
  · rintro ⟨G, hG, hGS⟩
    obtain ⟨v, hv, hs, -⟩ := sat_of_boundaryGuardO n Φ hΦ hone G hGS hG
    exact sat_of_restricted hΦ hv hs

/-! ### Codes -/

theorem fracPoints_valid (L : List (ℚ × ℚ)) : ∀ p ∈ L.map FracPoint.ofRat, p.Valid := by
  intro p hp
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
  exact ⟨q.1.den_pos, q.2.den_pos⟩

theorem AGPOrth_encode_iff (L : List (ℚ × ℚ)) (g : ℕ) :
    AGPOrth (encodeAGP (L.map FracPoint.ofRat) g) ↔ (Polygon.mk (L.map ratPoint)).Simple ∧
      (Polygon.mk (L.map ratPoint)).Orthogonal ∧ (Polygon.mk (L.map ratPoint)).HasGuardSetOfCard g := by
  constructor
  · rintro ⟨V', g', h, -, hS, hO, hG⟩
    obtain ⟨rfl, rfl⟩ := encodeAGP_inj h
    rw [map_toPoint_ofRat] at hS hO hG
    exact ⟨hS, hO, hG⟩
  · rintro ⟨hS, hO, hG⟩
    refine ⟨L.map FracPoint.ofRat, g, rfl, fracPoints_valid L, ?_, ?_, ?_⟩ <;>
      rw [map_toPoint_ofRat] <;> assumption

theorem AGPOrthPointBoundary_encode_iff (L : List (ℚ × ℚ)) (g : ℕ) :
    AGPOrthPointBoundary (encodeAGP (L.map FracPoint.ofRat) g) ↔
      (Polygon.mk (L.map ratPoint)).Simple ∧ (Polygon.mk (L.map ratPoint)).Orthogonal ∧
        (Polygon.mk (L.map ratPoint)).HasBoundaryGuardSetOfCard g := by
  constructor
  · rintro ⟨V', g', h, -, hS, hO, hG⟩
    obtain ⟨rfl, rfl⟩ := encodeAGP_inj h
    rw [map_toPoint_ofRat] at hS hO hG
    exact ⟨hS, hO, hG⟩
  · rintro ⟨hS, hO, hG⟩
    refine ⟨L.map FracPoint.ofRat, g, rfl, fracPoints_valid L, ?_, ?_, ?_⟩ <;>
      rw [map_toPoint_ofRat] <;> assumption

theorem not_AGPOrth_empty : ¬ AGPOrth (encodeAGP [] 0) := by
  rintro ⟨V, g, h, -, hS, -⟩
  obtain ⟨rfl, rfl⟩ := encodeAGP_inj h
  have := hS.1
  simp [Polygon.n] at this

theorem not_AGPOrthPointBoundary_empty : ¬ AGPOrthPointBoundary (encodeAGP [] 0) := by
  rintro ⟨V, g, h, -, hS, -⟩
  obtain ⟨rfl, rfl⟩ := encodeAGP_inj h
  have := hS.1
  simp [Polygon.n] at this

/-! ### The reductions -/

/-- The one-free instance of a formula. -/
def oInstance (φ : ETR.Formula) : List Constraint := oneFree (etrToREVVars φ) (etrToREV φ)

/-- The number of variables of the one-free instance of a formula. -/
def oVars (φ : ETR.Formula) : ℕ := oneFreeVars (etrToREVVars φ) (etrToREV φ)

/-- The orthogonal instance of a formula (the same word for both problems). -/
def agpOrthOfFormula (φ : ETR.Formula) : Word :=
  encodeAGP ((polyO (oVars φ) (oInstance φ)).map FracPoint.ofRat) (guardsO (oVars φ) (oInstance φ))

/-- **The reduction from ETR to `AGPOrth` and to `AGPOrthPointBoundary`** on raw words. -/
def etrToAGPOrth (w : Word) : Word :=
  match ETR.decodeFormula w with
  | some φ => agpOrthOfFormula φ
  | none => encodeAGP [] 0

theorem oneFreeVars_pos (φ : ETR.Formula) : 0 < oneFreeVars (etrToREVVars φ) (etrToREV φ) := by
  have := etrToREVVars_pos φ
  unfold oneFreeVars; omega

theorem oInstance_sat (φ : ETR.Formula) : φ.Satisfiable ↔ Satisfiable (oInstance φ) := by
  rw [etrToREV_iff, oInstance, oneFree_sat (etrToREV_vars φ)]

theorem agpOrthOfFormula_correct (φ : ETR.Formula) :
    φ.Satisfiable ↔ AGPOrth (agpOrthOfFormula φ) := by
  rw [agpOrthOfFormula, AGPOrth_encode_iff, oInstance_sat]
  unfold oVars oInstance
  rw [sat_iff_hasGuardSetOfCardO _ _ (oneFree_varsLt (etrToREV_vars φ)) (oneFree_isGad _ _)
      (oneFreeVars_pos φ)]
  exact ⟨fun h => ⟨simpleO _ _, orthogonalO _ _, h⟩, fun h => h.2.2⟩

theorem agpOrthPointBoundaryOfFormula_correct (φ : ETR.Formula) :
    φ.Satisfiable ↔ AGPOrthPointBoundary (agpOrthOfFormula φ) := by
  rw [agpOrthOfFormula, AGPOrthPointBoundary_encode_iff, oInstance_sat]
  unfold oVars oInstance
  rw [sat_iff_hasBoundaryGuardSetOfCardO _ _ (oneFree_varsLt (etrToREV_vars φ)) (oneFree_isGad _ _)
      (oneFreeVars_pos φ)]
  exact ⟨fun h => ⟨simpleO _ _, orthogonalO _ _, h⟩, fun h => h.2.2⟩

theorem etrToAGPOrth_correct (w : Word) : ArtGallery.ETR w ↔ AGPOrth (etrToAGPOrth w) := by
  unfold etrToAGPOrth
  cases h : ETR.decodeFormula w with
  | none => exact ⟨fun h' => absurd h' (not_ETR_of_decode_none h), fun h' => absurd h' not_AGPOrth_empty⟩
  | some φ =>
    simp only
    rw [← ETR.encode_of_decodeFormula h, ETR.ETR_encode_iff, agpOrthOfFormula_correct]

theorem etrToAGPOrthPointBoundary_correct (w : Word) :
    ArtGallery.ETR w ↔ AGPOrthPointBoundary (etrToAGPOrth w) := by
  unfold etrToAGPOrth
  cases h : ETR.decodeFormula w with
  | none =>
    exact ⟨fun h' => absurd h' (not_ETR_of_decode_none h),
      fun h' => absurd h' not_AGPOrthPointBoundary_empty⟩
  | some φ =>
    simp only
    rw [← ETR.encode_of_decodeFormula h, ETR.ETR_encode_iff, agpOrthPointBoundaryOfFormula_correct]

/-! ### Polynomial time -/

theorem agpOrthOfFormula_eq (φ : ETR.Formula) : agpOrthOfFormula φ =
    encodeList (fun p : ℚ × ℚ => binaryInt p.1.num ++ binaryNat p.1.den ++ binaryInt p.2.num ++
      binaryNat p.2.den) (polyO (oVars φ) (oInstance φ)) ++
      binaryNat (guardsO (oVars φ) (oInstance φ)) := by
  unfold agpOrthOfFormula encodeAGP
  rw [encodeList_map]
  rfl

protected theorem PT.agpOrthOfFormula : PT agpOrthOfFormula := by
  refine PT.of_eq ?_ fun φ => (agpOrthOfFormula_eq φ).symm
  unfold oVars oInstance
  fun_prop

protected theorem PT.etrToAGPOrth : PT etrToAGPOrth := by
  refine PT.of_optionCases (o := ETR.decodeFormula) (d := fun _ => encodeAGP [] 0)
    (f := fun _ φ => agpOrthOfFormula φ) (PT.decodeFormula PT.id) (PT.const _)
    (PT.agpOrthOfFormula.comp PT.snd') ?_ ?_
  · intro w h; simp [etrToAGPOrth, h]
  · intro w φ h; simp [etrToAGPOrth, h]

/-! ### Main theorems -/

/-- **ETR reduces in polynomial time to the orthogonal art gallery problem.** -/
theorem etr_polyRed_agpOrth : PolyRed ETR AGPOrth :=
  PT.polyRed PT.etrToAGPOrth etrToAGPOrth_correct

/-- **ETR reduces in polynomial time to the orthogonal point-boundary art gallery problem.** -/
theorem etr_polyRed_agpOrthPointBoundary : PolyRed ETR AGPOrthPointBoundary :=
  PT.polyRed PT.etrToAGPOrth etrToAGPOrthPointBoundary_correct

end ArtGallery.Orthogonal.Hard

end
