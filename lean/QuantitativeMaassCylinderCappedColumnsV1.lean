module

public import QuantitativeMaassCylinderPacketTraceV1
public import QuantitativeMaassConjugatedColumnsV1
public import QuantitativeMaassColumnTraceFiniteV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped ContDiff ENNReal

namespace QuantitativeMaass

variable (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
  (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
  (hsF : Function.support (evenCoshLift f)⊆Iic (Real.cosh R))
  (ε : ℝ) (hε : 0<ε) (t : ℕ)

/-- Explicit finite-band Abel column for the actual capped time packet. -/
def cylinderCappedTimeColumn (x : ℍ) : Lp ℂ 2 (quotientMeasure 0) :=
  LogBands.conjugatedColumn (quotientMeasure 0)
    (fun z => Real.log (cappedHeightWeight ε t z)) (cappedHeightWeight_log_measurable ε t)
    (cylinderAbelColumn (evenCoshLift f) (evenCoshLift_smoothOn f hf he hc) R hR hsF)
    ⌈(t:ℝ)*R+1⌉₊ x

theorem cylinderCappedTimePacket_column_coeFn (v : Lp ℂ 2 (quotientMeasure 0)) :
    cylinderCappedTimePacket f hf he hc hr R hR hs ε hε t v=ᵐ[quotientMeasure 0]
      (fun x => inner ℂ (cylinderCappedTimeColumn f hf he hc R hR hsF ε t x) v) :=
  LogBands.boundedConjugation_column_coeFn _ _ _ (cylinderTimePacket f hf hc) _
    (cylinderTimePacket_column_coeFn f hf he hc hr R hR hs hsF) _
    (cylinderTimePacket_band f hf he hc hr R hR hs ε hε t) v

/-- Exact extended energy of a capped packet after a bounded source map;
the integrand uses its constructed finite-band kernel column. -/
theorem cylinderCappedTimePacket_input_energy_trace {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι]
    (basis : HilbertBasis ι ℂ H) (A : H →L[ℂ] Lp ℂ 2 (quotientMeasure 0)) :
    (∑' i,ENNReal.ofReal (‖cylinderCappedTimePacket f hf he hc hr R hR hs ε hε t (A (basis i))‖^2))=
      ∫⁻ x,ENNReal.ofReal (‖A.adjoint (cylinderCappedTimeColumn f hf he hc R hR hsF ε t x)‖^2)
        ∂quotientMeasure 0 :=
  column_input_energy_trace _ basis _ _
    (cylinderCappedTimePacket_column_coeFn f hf he hc hr R hR hs hsF ε hε t) A

#print axioms cylinderCappedTimePacket_column_coeFn
#print axioms cylinderCappedTimePacket_input_energy_trace

end QuantitativeMaass
