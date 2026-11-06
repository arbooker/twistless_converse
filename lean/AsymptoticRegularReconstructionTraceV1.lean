module

public import AsymptoticRegularReconstructionFamilyV1
public import AsymptoticHyperbolicAreaV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularReconstruction

open MeasureTheory UpperHalfPlane ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularCertificate
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCertificateOperators (terminalConstant highStrip)
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem full_right_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ) :
    (full A hN P χ z).comp (highProjection A P z)=full A hN P χ z := by
  let T : Space →L[ℂ] Space := 1+AsymptoticReconstruction.low (low A hN P χ (P.s+3) z)
    (terminal A hN P χ (by omega : 2≤P.s+3) z)
  have hp : (highProjection A P z).comp (highProjection A P z)=highProjection A P z :=
    AsymptoticOrbitDiagonal.corner_idempotent _ _
  exact congrArg (fun X : Space →L[ℂ] Space => T.comp X) hp

/-- The actual regular reconstruction has finite squared Hilbert-module
mass, supplied by its uniform bound and the finite terminal corner. -/
theorem full_gram_trace_finite (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hK : ∀ z,‖low A hN P χ (P.s+3) z‖<1/2) :
    trace volume (fun z => (full A hN P χ z).adjoint.comp (full A hN P χ z))<∞ := by
  apply AsymptoticHyperbolicArea.closed_terminal_trace_finite (C:=(1+2*terminalConstant A P)^2) P.epsilon_pos
  · intro z
    have hn := full_norm_le A hN P χ hχ z (hK z)
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    simpa only [pow_two] using mul_le_mul hn hn (norm_nonneg (full A hN P χ z))
      ((norm_nonneg (full A hN P χ z)).trans hn)
  · intro z
    change ((full A hN P χ z).adjoint.comp (full A hN P χ z)).comp (highProjection A P z)=_
    exact congrArg (fun X : Space →L[ℂ] Space => (full A hN P χ z).adjoint.comp X)
      (full_right_terminal A hN P χ z)

/-- Traciality transfers the finite Gram mass to the range-side
operator. All covariance and measurability inputs have been proved. -/
theorem full_range_gram_trace_finite (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hK : ∀ z,‖low A hN P χ (P.s+3) z‖<1/2) :
    trace volume (fun z => (full A hN P χ z).comp (full A hN P χ z).adjoint)<∞ := by
  have hk : ∀ z,‖low A hN P χ (P.s+3) z‖<1 := fun z => lt_trans (hK z) (by norm_num)
  rw [← rational_trace_adjoint_mul (full A hN P χ)
    (full_matrix_measurable A hN P χ hk) (full_covariant A hN P χ hk)]
  exact full_gram_trace_finite A hN P χ hχ hK

#print axioms full_right_terminal
#print axioms full_gram_trace_finite
#print axioms full_range_gram_trace_finite

end AsymptoticRegularReconstruction
