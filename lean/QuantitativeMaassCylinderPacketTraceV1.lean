module

public import QuantitativeMaassCylinderPacketKernelV1
public import QuantitativeMaassColumnInputTraceV1
public import QuantitativeMaassCylinderZeroModeV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped Topology ContDiff ENNReal

namespace QuantitativeMaass

/-- Concrete smooth cylinder-packet energy after any bounded input map.
The right side consists of the actual Abel kernel columns. -/
theorem cylinderTimePacket_input_energy_trace {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι]
    (basis : HilbertBasis ι ℂ H) (A : H →L[ℂ] Lp ℂ 2 (quotientMeasure 0))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (hsF : Function.support (evenCoshLift f)⊆Iic (Real.cosh R)) :
    (∑' i,ENNReal.ofReal (‖cylinderTimePacket f hf hc (A (basis i))‖^2))=
      ∫⁻ x,ENNReal.ofReal (‖A.adjoint (cylinderAbelColumn (evenCoshLift f)
        (evenCoshLift_smoothOn f hf he hc) R hR hsF x)‖^2) ∂quotientMeasure 0 :=
  column_input_energy_trace (quotientMeasure 0) basis (cylinderTimePacket f hf hc) _
    (cylinderTimePacket_column_coeFn f hf he hc hr R hR hs hsF) A

/-- In particular the nonzero-mode source space contributes the projected
column energy. This identity alone does not assert its integrability. -/
theorem cylinderTimePacket_nonzero_energy_trace {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ cylinderNonzeroModes)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (hsF : Function.support (evenCoshLift f)⊆Iic (Real.cosh R)) :
    (∑' i,ENNReal.ofReal (‖cylinderTimePacket f hf hc (basis i).val‖^2))=
      ∫⁻ x,ENNReal.ofReal (‖cylinderNonzeroModes.subtypeL.adjoint (cylinderAbelColumn (evenCoshLift f)
        (evenCoshLift_smoothOn f hf he hc) R hR hsF x)‖^2) ∂quotientMeasure 0 :=
  cylinderTimePacket_input_energy_trace basis cylinderNonzeroModes.subtypeL f hf he hc hr R hR hs hsF

#print axioms cylinderTimePacket_input_energy_trace
#print axioms cylinderTimePacket_nonzero_energy_trace

end QuantitativeMaass
