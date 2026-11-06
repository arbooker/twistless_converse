module

public import QuantitativeEulerEndpointFiniteUpperTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule AsymptoticCylinder
open AsymptoticObservation AsymptoticDiagonalTrace AsymptoticFourierNorm AsymptoticCylinderModeComparison
open QuantitativeEulerEndpointReconstructionTrace
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

def retainedTraceError (s : ℝ) (h : ℕ) : ℝ :=
  (2*traceRateConstant A P+upperScheduledHeightConstant A P 0)*Real.exp (-3*s)+
    (sharpGrowthConstant A P 0*upperWeightCoefficient (fixedMajorant A P)*s^4)*
      (Real.sqrt (2*h+2:ℝ))⁻¹

/-- Exact-reconstruction trace is replaced by a finite trace cut only at
the output height exp(16s). The weight-dependent error keeps its polynomial
accuracy factor, which is essential to the endpoint horizon. -/
theorem physicalCylinder_retained_trace_rate (hN : 0<N) {s : ℝ} (hs : 1≤s) (e : Sector N) (h : ℕ)
    (F : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (hF : ‖F‖≤1) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let W := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    ‖trace fb (compressedSandwich (normalizedCountReconstruction A hN P h e) F W)-
      upperCutTrace (physicalCylinder A P hN s e h) F (2*h) (P'.s+4)
        (by positivity : 0<4*Real.pi) P'.epsilon_pos (Real.exp (16*s))‖/(2*h+2:ℝ)≤
      retainedTraceError A P s h := by
  intro P' W fb
  let V := physicalCylinder A P hN s e h
  let U := normalizedCountReconstruction A hN P h e
  let x := trace fb (compressedSandwich U F W)
  let y := trace fb (compressedSandwich V F W)
  let z := upperCutTrace V F (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos (Real.exp (16*s))
  have he := physicalCylinder_trace_rate A P hN hs e h F hF
  let n := newtonDepth A P 2 (Real.exp (-8*s))
  let j := reconstructionDepth A P 2 (Real.exp (-8*s)) n
  let J := foldCutoff A P 2 (Real.exp (-8*s)) j n
  let Y := lowerCutoff A P 2 (Real.exp (-8*s)) n
  have hc := (finite_upper_trace_error A hN P h e F hF Y (Real.exp (16*s)) (Real.exp_pos _) j J n).trans
    (scheduled_upper_error_sharp A P hs h)
  have hc' : ‖y-z‖/(2*h+2:ℝ)≤upperScheduledHeightConstant A P 0*Real.exp (-3*s)+
      (sharpGrowthConstant A P 0*upperWeightCoefficient (fixedMajorant A P)*s^4)*(Real.sqrt (2*h+2:ℝ))⁻¹ := hc
  have hk : (0:ℝ)<2*h+2 := by positivity
  have hk' : (0:ℝ)<4*h+2 := by positivity
  have he' : ‖x-y‖≤(traceRateConstant A P*Real.exp (-3*s))*(4*h+2:ℝ) := by
    rw [norm_sub_rev]
    exact (div_le_iff₀ hk').mp he
  have he0 : 0≤traceRateConstant A P*Real.exp (-3*s) := (div_nonneg (norm_nonneg _) hk'.le).trans he
  have he'' : ‖x-y‖/(2*h+2:ℝ)≤2*traceRateConstant A P*Real.exp (-3*s) := by
    apply (div_le_iff₀ hk).mpr
    have hh := mul_le_mul_of_nonneg_left (show (4*h+2:ℝ)≤2*(2*h+2:ℝ) by linarith) he0
    exact he'.trans (hh.trans_eq (by ring))
  change ‖x-z‖/(2*h+2:ℝ)≤_
  have ht := div_le_div_of_nonneg_right (norm_sub_le_norm_sub_add_norm_sub x y z) hk.le
  rw [add_div] at ht
  exact ht.trans ((add_le_add he'' hc').trans_eq (by unfold retainedTraceError; ring))

#print axioms physicalCylinder_retained_trace_rate
end QuantitativeEulerEndpointCommonReconstruction
