module

public import QuantitativeMaassTerminalDefectTraceV1
public import QuantitativeMaassTerminalFiniteElementV1
public import QuantitativeMaassFilterDefectPerturbationV1
public import QuantitativeMaassMetricReconstructionExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open QuantitativeEulerEndpointRegularBase QuantitativeEulerEndpointTerminalAlgebra
open FinitenessCertificate FinitenessGlobalHeight

/-- Quantitative regular trace bound for the literal finite filter, with
all approximation errors charged in the fixed terminal algebra. -/
theorem finite_regular_power_trace_bound {N Q : ℕ} {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A)
    (U : Expression) (hU : ∀ x,‖regularSum U x‖≤1)
    (hsource : ∀ x,regularSum U x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=regularSum U x)
    (T : Expression) (hT : ∀ x,0≤regularSum T x ∧ regularSum T x≤1)
    (hleft : ∀ x,AsymptoticOrbitDiagonal.corner (terminalRegion A P) x*regularSum T x=regularSum T x)
    (hright : ∀ x,regularSum T x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=regularSum T x)
    (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1) {δ : ℝ} (hδ : 0≤δ)
    (he : ∀ x,‖regularSum T x-rep A P F x‖≤δ) (m : ℕ) :
    signedTrace volume (fun x => 1-(1-regularSum U x*regularSum T x*(regularSum U x).adjoint)^m)≤
      tr A P F+4*((m:ℝ)+1)*tr A P (F-F^2)+(12*(m:ℝ)+13)*‖tr A P‖*δ := by
  let V := terminalFiniteElement A P T hT hleft hright
  have hv := terminalFiniteElement_order A P T hT hleft hright
  have hvnorm : ‖V‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hv.1).mpr hv.2
  have hfnorm : ‖F‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hF0).mpr hF1
  have herr := tracial_filter_defect_perturbation (tr A P) V F hvnorm hfnorm
    (terminalFiniteElement_close A P T hT hleft hright F hδ he)
  have hh := regular_power_trace_defect A P U hU hsource
    (right_terminal_gram_trace_finite A P U hU hsource) V hv.1 hv.2 m
  change signedTrace volume (fun x => 1-(1-regularSum U x*regularSum T x*(regularSum U x).adjoint)^m)≤_ at hh
  apply hh.trans
  have hm : 0≤4*((m:ℝ)+1) := by positivity
  have h2 := mul_le_mul_of_nonneg_left herr.2 hm
  nlinarith [herr.1]

#print axioms finite_regular_power_trace_bound
end QuantitativeMaass
