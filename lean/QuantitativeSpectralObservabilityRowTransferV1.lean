module

public import QuantitativeSpectralObservabilityOldCoordinatesV1
public import QuantitativeSpectralExceptionalQuotientPolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticOrbitDiagonal
open AsymptoticRegularBranchFamily QuantitativeSpectralFiniteReduction
open scoped lp

attribute [local instance] Classical.propDecidable

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Literal coordinate recombination transported back into the actual
quotient. The two extra factors are contractions. -/
def retainedRecombiner (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (H : ℝ) (x : ℍ) (A : V →L[ℂ] ℓ²(OrbitGroup,ℂ)) :
    V →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  ((fundamentalTransfer N hε ht x).comp (corner (fundamentalRetained N H) x)).comp A

theorem retainedRecombiner_norm (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (H : ℝ) (x : ℍ) (A : V →L[ℂ] ℓ²(OrbitGroup,ℂ)) :
    ‖retainedRecombiner N hε ht H x A‖≤‖A‖ := by
  have hc : ‖(fundamentalTransfer N hε ht x).comp
      (corner (fundamentalRetained N H) x)‖≤1 :=
    (opNorm_comp_le _ _).trans ((mul_le_mul (fundamentalTransfer_norm N hε ht x)
      (AsymptoticOrbitRegion.corner_norm_le _ _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1))
  exact (opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hc (norm_nonneg A)).trans_eq (one_mul _))

/-- Coordinate identities on the concrete retained region give an exact
bounded quotient row, with its error supported by the actual tail projection. -/
theorem quotient_row_decompose (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (H : ℝ) (x : ℍ) (hx : fundamentalGood N x)
    (A : V →L[ℂ] ℓ²(OrbitGroup,ℂ)) (d : V) (u : ℓ²(OrbitGroup,ℂ))
    (hu : u∈quotientSpace N hε ht x)
    (hrow : ∀ g, g • x∈openCover N \ wideTailCover N H →
      coordinate N ε t x g u=A d g) :
    u=retainedRecombiner N hε ht H x A d+
      fundamentalSubsetProjection N hε ht (fundamentalTail N H) x u := by
  have he := fundamentalSubsetProjection_of_coordinates N hε ht
    (s:=fundamentalRetained N H) sdiff_subset x hx u (A d) hu
    (fun g hg => hrow g (fundamentalRetained_subset_cover N H hg))
  exact (fundamental_quotient_decompose N hε ht H x hx u hu).trans
    (congrArg (fun v => v+fundamentalSubsetProjection N hε ht (fundamentalTail N H) x u) he)

#print axioms retainedRecombiner_norm
#print axioms quotient_row_decompose

end QuantitativeSpectralObservability
