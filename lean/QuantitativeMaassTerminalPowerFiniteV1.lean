module

public import QuantitativeMaassTerminalPowerTraceV1
public import QuantitativeMaassMetricReconstructionExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticFiniteBranch
open QuantitativeSpectralRegularAlgebra QuantitativeEulerEndpointRegularBase
open FinitenessCertificate FinitenessGlobalHeight QuantitativeEulerEndpointTerminalAlgebra
open QuantitativeHolomorphic
open scoped ENNReal

theorem regular_trace_finite_of_diagonal_integrable
    (B : UpperHalfPlane→RegularSpace→L[ℂ]RegularSpace)
    (hi : Integrable (fun x => (matrix (B x) 1 1).re) volume) : trace volume B<∞ := by
  have hn := hi.norm
  have hf : (∫⁻ x,ENNReal.ofReal ‖(matrix (B x) 1 1).re‖ ∂volume)<∞ :=
    lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
      hn.aestronglyMeasurable (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).mpr hn)
  apply lt_of_le_of_lt (lintegral_mono (fun x => ?_)) hf
  exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using le_abs_self (matrix (B x) 1 1).re)

/-- Finiteness is proved for the actual ambient power polynomial, despite
its displayed identity term. The constant term cancels in the sandwich. -/
theorem regular_power_trace_finite {N Q : ℕ} {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A)
    (U : Expression) (hU : ∀ x,‖regularSum U x‖≤1)
    (hsource : ∀ x,regularSum U x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=regularSum U x)
    (F : Algebra A P) (m : ℕ) :
    trace volume (fun x => 1-(1-regularSum U x*rep A P F x*(regularSum U x).adjoint)^m)<∞ := by
  let G := terminalExpressionGram A P U hU hsource
  let K := powerSandwichCoefficient F G m
  have he : (fun x => 1-(1-regularSum U x*rep A P F x*(regularSum U x).adjoint)^m)=
      (fun x => (regularSum U x).comp ((rep A P K x).comp (regularSum U x).adjoint)) := by
    funext x
    let r : Algebra A P→ₙ+*(RegularSpace→L[ℂ]RegularSpace) :=
      { toFun := fun a => rep A P a x
        map_zero' := rfl
        map_add' := fun _ _ => rfl
        map_mul' := fun _ _ => rfl }
    exact (powerSandwichCoefficient_rep r F G (regularSum U x) (regularSum U x).adjoint rfl m).symm
  rw [he]
  apply regular_trace_finite_of_diagonal_integrable
  exact bounded_sandwich_diagonal_integrable volume AsymptoticRationalGroup.measurePreserving
    (regularSum U) (rep A P K) (regularSum_matrix_measurable U)
    (representation_matrix_measurable _ _ _ _ _ K) (regularSum_covariant U)
    (right_terminal_gram_trace_finite A P U hU hsource) (representation_norm_le _ _ _ _ _ K)

#print axioms regular_trace_finite_of_diagonal_integrable
#print axioms regular_power_trace_finite
end QuantitativeMaass
