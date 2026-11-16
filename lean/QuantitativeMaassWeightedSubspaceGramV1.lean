module

public import QuantitativeMaassNormalizedWeightedEmbeddingV1
public import QuantitativeHolomorphicNewtonTransportV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson QuantitativeHolomorphic

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

theorem normalizedWeightedSubspace_gram (N : ℕ) (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (K : Submodule ℂ (localCuspidalSpace N hN)) [CompleteSpace K] :
    ((normalizedCuspidalWeightedEmbedding N hN hδ hν).comp K.subtypeL).adjoint.comp
      ((normalizedCuspidalWeightedEmbedding N hN hδ hν).comp K.subtypeL)=
        K.orthogonalProjectionOnto.comp ((normalizedCuspidalQuotientWeight N hN hδ hν).comp K.subtypeL) := by
  rw [normalizedCuspidalWeightedEmbedding_restricted_gram,Submodule.adjoint_subtypeL]

/-- A polynomial of the actual fixed compression is exactly the included
polynomial of the actual restricted embedding's Gram. -/
theorem normalizedWeightedSubspace_polynomial {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (N : ℕ) (hN : 0<N) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (K : Submodule ℂ (localCuspidalSpace N hN)) [CompleteSpace K]
    (J : E →L[ℂ] localCuspidalSpace N hN) (hJ : ∀ x,J x∈K) (p : Polynomial ℝ) :
    (Polynomial.aeval (K.starProjection.comp (normalizedCuspidalQuotientWeight N hN hδ hν)) p).comp J=
      K.subtypeL.comp ((Polynomial.aeval
        (((normalizedCuspidalWeightedEmbedding N hN hδ hν).comp K.subtypeL).adjoint.comp
          ((normalizedCuspidalWeightedEmbedding N hN hδ hν).comp K.subtypeL)) p).comp
            (K.orthogonalProjectionOnto.comp J)) := by
  let R := (normalizedCuspidalWeightedEmbedding N hN hδ hν).comp K.subtypeL
  let G := R.adjoint.comp R
  let A := K.starProjection.comp (normalizedCuspidalQuotientWeight N hN hδ hν)
  have hi : A.comp K.subtypeL=K.subtypeL.comp G := by
    dsimp only [G,R,A]
    rw [normalizedWeightedSubspace_gram]
    rfl
  have hp := real_polynomial_intertwines G A K.subtypeL hi p
  apply ContinuousLinearMap.ext
  intro x
  have hx : K.subtypeL (K.orthogonalProjectionOnto (J x))=J x :=
    K.starProjection_eq_self_iff.mpr (hJ x)
  have hh := DFunLike.congr_fun hp (K.orthogonalProjectionOnto (J x))
  change Polynomial.aeval A p (K.subtypeL (K.orthogonalProjectionOnto (J x)))=
    K.subtypeL (Polynomial.aeval G p (K.orthogonalProjectionOnto (J x))) at hh
  rw [hx] at hh
  exact hh

/-- The finite normalization used by reconstruction is the literal Newton
polynomial of the fixed compression, followed by the actual embedding. -/
theorem normalizedWeightedSubspace_newton {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (N : ℕ) (hN : 0<N) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (K : Submodule ℂ (localCuspidalSpace N hN)) [CompleteSpace K]
    (J : E →L[ℂ] localCuspidalSpace N hN) (hJ : ∀ x,J x∈K) (n : ℕ) :
    (normalizedCuspidalWeightedEmbedding N hN hδ hν).comp
      ((Polynomial.aeval (K.starProjection.comp (normalizedCuspidalQuotientWeight N hN hδ hν))
        (inverseSqrtPolynomial n)).comp J)=
      (polynomialNormalizedReconstruction
        ((normalizedCuspidalWeightedEmbedding N hN hδ hν).comp K.subtypeL) n).comp
          (K.orthogonalProjectionOnto.comp J) := by
  rw [normalizedWeightedSubspace_polynomial N hN hδ hν K J hJ]
  rfl

#print axioms normalizedWeightedSubspace_gram
#print axioms normalizedWeightedSubspace_polynomial
#print axioms normalizedWeightedSubspace_newton

end QuantitativeMaass
