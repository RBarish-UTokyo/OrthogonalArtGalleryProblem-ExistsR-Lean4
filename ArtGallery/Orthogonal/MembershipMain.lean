module

public import ArtGallery.Orthogonal.Membership

/-!
# The three orthogonal art gallery problems are in `∃ℝ`, with only guard variables

Each orthogonal problem reduces in polynomial time to ETR by formulas whose only variables are
the `2g` guard coordinates: the formula of the general problem (`ArtGallery/FewVars/`) conjoined
with the variable-free orthogonality test `Orthogonal.orthCheck`.
-/

@[expose] public section

namespace ArtGallery

open Complexity Complexity.PT ArtGallery.FewVars ArtGallery.Membership ArtGallery.Orthogonal

/-- The guard-variable form of membership, for a strengthened reduction `withOrth F`. -/
theorem withOrth_guard_variables {Lo : Language} {F : Word → ETR.Formula} (hPT : PT F)
    (hc : ∀ w, Lo w ↔ (withOrth F w).Satisfiable)
    (hv : ∀ (V : List FracPoint) (g : ℕ), (F (encodeAGP V g)).VarsLt (2 * g)) :
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, Lo w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g) := by
  refine ⟨fun w => (withOrth F w).encode, (PT.formulaEncode (PT.withOrth hPT)).polyTime_word,
    fun w => ?_, fun V g => ⟨withOrth F (encodeAGP V g), rfl, hv V g, varsLt_orthCheck _ _⟩⟩
  rw [ETR.ETR_encode_iff, hc]

/-- **The orthogonal art gallery problem is in `∃ℝ`**, by formulas whose only variables are the
`2g` guard coordinates. -/
theorem agpOrth_inER_guard_variables :
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, AGPOrth w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g) :=
  withOrth_guard_variables PT.fvToETR
    (withOrth_correct (L := AGP) (Q := fun V g => (polyOf V).Simple ∧
      (polyOf V).HasGuardSetOfCard g) fvToETR_correct (fun _ => Iff.rfl)
      (fun _ => by simp only [AGPOrth, polyOf]; tauto))
    fvToETR_encodeAGP_varsLt

/-- **The orthogonal point-boundary art gallery problem is in `∃ℝ`**, by formulas whose only
variables are the `2g` guard coordinates. -/
theorem agpOrthPointBoundary_inER_guard_variables :
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, AGPOrthPointBoundary w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g) :=
  withOrth_guard_variables Boundary.PT.fvbToETR
    (withOrth_correct (L := AGPPointBoundary) (Q := fun V g => (polyOf V).Simple ∧
      (polyOf V).HasBoundaryGuardSetOfCard g) Boundary.fvbToETR_correct (fun _ => Iff.rfl)
      (fun _ => by simp only [AGPOrthPointBoundary, polyOf]; tauto))
    Boundary.fvbToETR_encodeAGP_varsLt

/-- **The orthogonal boundary-point art gallery problem is in `∃ℝ`**, by formulas whose only
variables are the `2g` guard coordinates. -/
theorem agpOrthBoundaryPoint_inER_guard_variables :
    ∃ f : Word → Word, PolyTime f ∧ (∀ w, AGPOrthBoundaryPoint w ↔ ETR (f w)) ∧
      ∀ (V : List FracPoint) (g : ℕ), ∃ φ : ETR.Formula,
        f (encodeAGP V g) = φ.encode ∧ φ.VarsLt (2 * g) :=
  withOrth_guard_variables BoundaryPoint.PT.fvbpToETR
    (withOrth_correct (L := AGPBoundaryPoint) (Q := fun V g => (polyOf V).Simple ∧
      (polyOf V).HasGuardSetOnBoundaryOfCard g) BoundaryPoint.fvbpToETR_correct
      (fun _ => Iff.rfl) (fun _ => by simp only [AGPOrthBoundaryPoint, polyOf]; tauto))
    BoundaryPoint.fvbpToETR_encodeAGP_varsLt

/-- **The orthogonal art gallery problem is in `∃ℝ`.** -/
theorem agpOrth_inER : InER AGPOrth := by
  obtain ⟨f, hf, hc, -⟩ := agpOrth_inER_guard_variables
  exact ⟨f, hf, hc⟩

/-- **The orthogonal point-boundary art gallery problem is in `∃ℝ`.** -/
theorem agpOrthPointBoundary_inER : InER AGPOrthPointBoundary := by
  obtain ⟨f, hf, hc, -⟩ := agpOrthPointBoundary_inER_guard_variables
  exact ⟨f, hf, hc⟩

/-- **The orthogonal boundary-point art gallery problem is in `∃ℝ`.** -/
theorem agpOrthBoundaryPoint_inER : InER AGPOrthBoundaryPoint := by
  obtain ⟨f, hf, hc, -⟩ := agpOrthBoundaryPoint_inER_guard_variables
  exact ⟨f, hf, hc⟩

end ArtGallery

end
