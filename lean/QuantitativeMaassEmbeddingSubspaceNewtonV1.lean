module

public import QuantitativeMaassWeightedSubspaceGramV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeHolomorphic
namespace QuantitativeMaass

variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Gram of a restriction is the orthogonal compression of the actual Gram. -/
theorem embedding_subspace_gram (R : E →L[ℂ] F)
    (K : Submodule ℂ E) [CompleteSpace K] :
    (R.comp K.subtypeL).adjoint.comp (R.comp K.subtypeL)=
      K.orthogonalProjectionOnto.comp ((R.adjoint.comp R).comp K.subtypeL) := by
  rw [ContinuousLinearMap.adjoint_comp,Submodule.adjoint_subtypeL]
  rfl

/-- Polynomial reconstruction commutes with inclusion of a closed source subspace. -/
theorem embedding_subspace_newton (R : E →L[ℂ] F)
    (K : Submodule ℂ E) [CompleteSpace K]
    (J : H →L[ℂ] E) (hJ : ∀ x,J x∈K) (n : ℕ) :
    R.comp ((Polynomial.aeval (K.starProjection.comp (R.adjoint.comp R))
      (inverseSqrtPolynomial n)).comp J)=
      (polynomialNormalizedReconstruction (R.comp K.subtypeL) n).comp
        (K.orthogonalProjectionOnto.comp J) := by
  let G := (R.comp K.subtypeL).adjoint.comp (R.comp K.subtypeL)
  let A := K.starProjection.comp (R.adjoint.comp R)
  have hi : A.comp K.subtypeL=K.subtypeL.comp G := by
    dsimp only [G,A]
    rw [embedding_subspace_gram]
    rfl
  have hp := real_polynomial_intertwines G A K.subtypeL hi (inverseSqrtPolynomial n)
  apply ContinuousLinearMap.ext
  intro x
  have hx : K.subtypeL (K.orthogonalProjectionOnto (J x))=J x :=
    K.starProjection_eq_self_iff.mpr (hJ x)
  have hh := DFunLike.congr_fun hp (K.orthogonalProjectionOnto (J x))
  change Polynomial.aeval A (inverseSqrtPolynomial n)
      (K.subtypeL (K.orthogonalProjectionOnto (J x)))=
    K.subtypeL (Polynomial.aeval G (inverseSqrtPolynomial n) (K.orthogonalProjectionOnto (J x))) at hh
  rw [hx] at hh
  exact congrArg R hh

#print axioms embedding_subspace_gram
#print axioms embedding_subspace_newton
end QuantitativeMaass
