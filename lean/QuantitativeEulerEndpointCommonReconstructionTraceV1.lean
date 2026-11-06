module

public import QuantitativeEulerEndpointFiniteReconstructionTraceV1
public import QuantitativeHolomorphicScheduledUpperCutV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule AsymptoticCylinder
open AsymptoticObservation AsymptoticDiagonalTrace AsymptoticFourierNorm
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- The cylinder operator of the SAME common finite reconstruction expression. -/
def physicalCylinder (hN : 0<N) (s : ℝ) (e : Sector N) (h : ℕ) :=
  let t := Real.exp (-8*s)
  let n := newtonDepth A P 2 t
  let j := reconstructionDepth A P 2 t n
  let J := foldCutoff A P 2 t j n
  let Y := lowerCutoff A P 2 t n
  polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n

theorem physicalCylinder_realization (hN : 0<N) (s : ℝ) (e : Sector N) (h : ℕ) :
    AsymptoticFiniteBranch.holomorphicSum (expression A P hN s e) (h+1)=
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        ((physicalCylinder A P hN s e h).comp
          (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε).adjoint) := by
  dsimp only [expression]
  rw [holomorphicSum_normalizedCutCountExpression]
  rfl

def traceRateConstant : ℝ := approximationGrowthConstant A P 0 (fixedMajorant A P)

theorem physicalCylinder_trace_rate (hN : 0<N) {s : ℝ} (hs : 1≤s) (e : Sector N) (h : ℕ)
    (F : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (hF : ‖F‖≤1) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let W := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    ‖trace fb (compressedSandwich (physicalCylinder A P hN s e h) F W)-
      trace fb (compressedSandwich (normalizedCountReconstruction A hN P h e) F W)‖/(4*h+2:ℝ)≤
        traceRateConstant A P*Real.exp (-3*s) := by
  intro P' W fb
  let t := Real.exp (-8*s)
  let n := newtonDepth A P 2 t
  let j := reconstructionDepth A P 2 t n
  let J := foldCutoff A P 2 t j n
  let Y := lowerCutoff A P 2 t n
  have hh := countFilterError_schedule A P 0 (Real.exp_pos (-8*s))
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at hh
  have ht : t≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have he := QuantitativeEulerEndpointReconstructionTrace.finite_reconstruction_trace_error A hN P h e
    F hF Y hh.2.1.le j J n hh.1 hh.2.2.1 (hh.2.2.2.trans ht)
  have hg := growing_reconstruction_approximation A P (C:=0) (by norm_num) hs
    (fixedMajorant_nonneg A P) 0 (by norm_num)
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at hg
  exact he.trans hg

#print axioms physicalCylinder_realization
#print axioms physicalCylinder_trace_rate
end QuantitativeEulerEndpointCommonReconstruction
