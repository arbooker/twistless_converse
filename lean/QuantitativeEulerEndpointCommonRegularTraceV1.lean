module

public import QuantitativeEulerEndpointSandwichPerturbationV1
public import QuantitativeEulerEndpointActualTerminalRegularFilterV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticFiniteBranch
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open QuantitativeEulerEndpointTerminalAlgebra QuantitativeEulerEndpointTerminalTrace
open scoped ENNReal
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

theorem regular_gram_trace_finite (hN : 0<N) (s : ℝ) (e : Sector N) :
    AsymptoticRegularTrace.trace volume (fun x =>
      (regularSum (expression A P hN s e) x).adjoint.comp
        (regularSum (expression A P hN s e) x))<∞ :=
  finiteNormalizedRegularAmbient_gram_trace_finite A hN P e _ _ _ _

/-- The same literal finite sandwich used for physical trace comparison
is dominated by the intrinsic positive terminal trace, with fixed-area error. -/
theorem retained_regular_le_terminal (hN : 0<N) (s : ℝ) (e : Sector N)
    (a : Algebra A P) (ha : 0≤a ∧ a≤1) (T : Expression)
    (hT : ∀ x,0≤regularSum T x ∧ regularSum T x≤1)
    (δ : ℝ) (he : ∀ x,‖rep A P a x-regularSum T x‖≤δ) (Y H : ℝ) :
    signedTrace volume (regularSum (retainedExpression Y H (sandwichExpression A P hN s e T)))≤
      tr A P a+δ*(AsymptoticReconstructedCount.parameters A P).ε⁻¹ := by
  have hfamily : regularSum (retainedExpression Y H (sandwichExpression A P hN s e T))=
      regularRetained Y H (fun x => (regularSum (expression A P hN s e) x).comp
        ((regularSum T x).comp (regularSum (expression A P hN s e) x).adjoint)) := by
    funext x
    rw [regularSum_retainedExpression]
    unfold regularRetained
    simp only [sandwichExpression,regularSum_compose,regularSum_adjoint]
  rw [hfamily]
  exact retained_sandwich_le_trace A P a ha (expression A P hN s e) T
    (regular_norm A P hN s e) hT (regular_right_terminal A P hN s e)
    (regular_gram_trace_finite A P hN s e) δ he Y H

#print axioms regular_gram_trace_finite
#print axioms retained_regular_le_terminal
end QuantitativeEulerEndpointCommonReconstruction
