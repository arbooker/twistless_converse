module

public import QuantitativeEulerEndpointCommonReconstructionTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointReconstructionTrace
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticDiagonalTrace
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule AsymptoticCylinderModeComparison
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Upper truncation is performed only on the reconstructed trace. The
terminal filter itself remains on the entire source strip. -/
theorem finite_upper_trace_error (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (F : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (hF : ‖F‖≤1) (Y H : ℝ) (hH : 0<H) (j J n : ℕ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let W := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let V := polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n
    let B := (3/2:ℝ)^n
    ‖trace fb (compressedSandwich V F W)-upperCutTrace V F (2*h) (P'.s+4)
      (by positivity : 0<4*Real.pi) P'.epsilon_pos H‖/(2*h+2:ℝ)≤
      upperCutError (B^2*(1+fixedMajorant A P)) B 1
        (massBound (2*h) (P'.s+4) (4*Real.pi) H/(2*h+2:ℝ)) := by
  intro P' W fb V B
  let R := finiteCountWeightedNormalizer A hN P h e Y j J n
  have ht := factored_upperCut_trace_bound R F (Sharp.finiteCountWeightedNormalizer_norm_le A hN P h e Y j J n)
    hF (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos hH
  have hv : (inclusion P'.epsilon_pos).comp R=V := (finiteCountReconstruction_weighted A hN P h e Y j J n).symm
  rw [hv] at ht
  have hm := div_le_div_of_nonneg_right (Sharp.upperCompression_trace_le_massBound (2*h) (P'.s+4)
    (by positivity : 0<4*Real.pi) P'.epsilon_pos hH) (by positivity : (0:ℝ)≤2*h+2)
  have ht' : ‖trace fb (compressedSandwich V F W)-upperCutTrace V F (2*h) (P'.s+4)
      (by positivity : 0<4*Real.pi) P'.epsilon_pos H‖/(2*h+2:ℝ)≤
      upperCutError (B^2*(1+fixedMajorant A P)) B 1
        (trace fb (upperCompression (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos H)/(2*h+2:ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,B,fb,W,fixedMajorant,P'] using ht
  apply ht'.trans
  unfold upperCutError
  gcongr

/-- Retain the polynomial accuracy factor in the weight-dependent tail.
Overestimating it by a double exponential would lose the endpoint schedule. -/
theorem scheduled_upper_error_sharp (P : Parameters A) {s : ℝ} (hs : 1≤s) (h : ℕ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let n := newtonDepth A P 2 (Real.exp (-8*s))
    let B := (3/2:ℝ)^n
    upperCutError (B^2*(1+fixedMajorant A P)) B 1
      (massBound (2*h) (P'.s+4) (4*Real.pi) (Real.exp (16*s))/(2*h+2:ℝ))≤
      upperScheduledHeightConstant A P 0*Real.exp (-3*s)+
      (sharpGrowthConstant A P 0*upperWeightCoefficient (fixedMajorant A P)*s^4)*
        (Real.sqrt (2*h+2:ℝ))⁻¹ := by
  intro P' n B
  have hg := growing_sharp_majorant A P (C:=0) (by norm_num) hs 0 (by norm_num)
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at hg
  have hb : B^2≤sharpGrowthConstant A P 0*s^4 := (le_max_right _ _).trans hg
  exact upperCutError_split (by dsimp [B]; positivity) (fixedMajorant_nonneg A P)
    (upperMassCoefficient_nonneg _ (by positivity)) (sharpGrowthConstant_nonneg A P 0) hs
    (by have := Nat.cast_nonneg (α:=ℝ) h; linarith) hb
    (scheduled_upper_mass h (P'.s+4) (by linarith))

#print axioms finite_upper_trace_error
#print axioms scheduled_upper_error_sharp
end QuantitativeEulerEndpointReconstructionTrace
