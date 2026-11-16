module

public import QuantitativeHolomorphicNewtonTransportV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open QuantitativeHolomorphic
namespace QuantitativeMaass

variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Extending a source by an orthogonal complement preserves its polynomial
reconstruction after the source projection. -/
theorem coisometry_newton (R : E →L[ℂ] F) (S : H →L[ℂ] E)
    (hS : S.comp S.adjoint=1) (n : ℕ) :
    polynomialNormalizedReconstruction (R.comp S) n=
      (polynomialNormalizedReconstruction R n).comp S := by
  have hs (x : E) : S (S.adjoint x)=x := DFunLike.congr_fun hS x
  have hi : (R.adjoint.comp R).comp S=
      S.comp ((R.comp S).adjoint.comp (R.comp S)) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,hs]
  have hp := real_polynomial_intertwines ((R.comp S).adjoint.comp (R.comp S))
    (R.adjoint.comp R) S hi (inverseSqrtPolynomial n)
  apply ContinuousLinearMap.ext
  intro x
  exact (congrArg R (DFunLike.congr_fun hp x)).symm

/-- The polynomial cogram is exactly unchanged by a coisometric source extension. -/
theorem coisometry_newton_cogram (R : E →L[ℂ] F) (S : H →L[ℂ] E)
    (hS : S.comp S.adjoint=1) (n : ℕ) :
    (polynomialNormalizedReconstruction (R.comp S) n).comp
      (polynomialNormalizedReconstruction (R.comp S) n).adjoint=
    (polynomialNormalizedReconstruction R n).comp
      (polynomialNormalizedReconstruction R n).adjoint := by
  rw [coisometry_newton R S hS n,ContinuousLinearMap.adjoint_comp]
  have hs (x : E) : S (S.adjoint x)=x := DFunLike.congr_fun hS x
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,hs]

#print axioms coisometry_newton
#print axioms coisometry_newton_cogram
end QuantitativeMaass
