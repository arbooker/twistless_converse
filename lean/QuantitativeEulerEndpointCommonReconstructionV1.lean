module

public import QuantitativeHolomorphicSimultaneousCutoffsV1
public import QuantitativeHolomorphicTerminalFiniteNormalizerV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule AsymptoticFiniteBranch
open ContinuousLinearMap

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- One explicit expression, with cutoffs chosen before the sector, physical
weight or regular root. The auxiliary filter depth is zero: its schedule
then pays twice the actual reconstruction error. -/
def expression (hN : 0<N) (s : ℝ) (e : Sector N) : Expression :=
  let t := Real.exp (-8*s)
  let n := newtonDepth A P 2 t
  let j := reconstructionDepth A P 2 t n
  let J := foldCutoff A P 2 t j n
  let Y := lowerCutoff A P 2 t n
  normalizedReconstructionExpression (scaledCutCountExpression A hN P e Y j J) n

theorem scheduled_error (s : ℝ) :
    let t := Real.exp (-8*s)
    let n := newtonDepth A P 2 t
    let j := reconstructionDepth A P 2 t n
    let J := foldCutoff A P 2 t j n
    let Y := lowerCutoff A P 2 t n
    0<J ∧ 0<Y ∧ normalizedCutError A P Y j J n≤t/2 := by
  have hh := countFilterError_schedule A P 0 (Real.exp_pos (-8*s))
  dsimp only at hh ⊢
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at hh
  refine ⟨hh.1,hh.2.1,?_⟩
  have he := hh.2.2.2
  unfold countFilterError at he
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at he
  linarith

theorem regular_error (hN : 0<N) (s : ℝ) (e : Sector N) (x : UpperHalfPlane) :
    ‖regularSum (expression A P hN s e) x-
      normalizedRegularAmbientCountReconstruction A hN P e x‖≤Real.exp (-8*s)/2 := by
  have hh := scheduled_error A P s
  exact (finiteNormalizedRegularAmbient_error A hN P e hh.2.1.le _ _ _ hh.1 x).trans hh.2.2

theorem physical_error (hN : 0<N) (s : ℝ) (e : Sector N) (h : ℕ) :
    ‖holomorphicSum (expression A P hN s e) (h+1)-
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        ((normalizedCountReconstruction A hN P h e).comp
          (AsymptoticCylinderTerminal.ambientLift
            (AsymptoticReconstructedCount.parameters A P).ε).adjoint)‖≤Real.exp (-8*s)/2 := by
  have hh := scheduled_error A P s
  exact (normalizedCutCountExpression_ambient_error A hN P h _ e _ hh.2.1.le _ _ hh.1).trans hh.2.2

theorem regular_norm (hN : 0<N) (s : ℝ) (e : Sector N) (x : UpperHalfPlane) :
    ‖regularSum (expression A P hN s e) x‖≤1 :=
  finiteNormalizedRegularAmbient_norm_le A hN P e _ _ _ _ x

theorem physical_norm (hN : 0<N) (s : ℝ) (e : Sector N) (h : ℕ) :
    ‖holomorphicSum (expression A P hN s e) (h+1)‖≤1 := by
  dsimp only [expression]
  rw [holomorphicSum_normalizedCutCountExpression]
  let t := Real.exp (-8*s)
  let n := newtonDepth A P 2 t
  let j := reconstructionDepth A P 2 t n
  let J := foldCutoff A P 2 t j n
  let Y := lowerCutoff A P 2 t n
  let V := polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n
  have hv : ‖V‖≤1 := polynomialNormalizedReconstruction_norm_le _
    (scaledCutFiniteCountReconstruction_norm_le A hN P h e Y j J) n
  have hh := norm_isometric_transport_difference_le
    (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε)
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _)
    AsymptoticCylinderLift.lift.toContinuousLinearMap AsymptoticCylinderLift.lift.adjoint_comp_self
    V (0 : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε
      →L[ℂ] AsymptoticCylinder.Space)
  simp only [zero_comp,comp_zero,sub_zero] at hh
  exact hh.trans hv

theorem regular_right_terminal (hN : 0<N) (s : ℝ) (e : Sector N) (x : UpperHalfPlane) :
    (regularSum (expression A P hN s e) x).comp
      (AsymptoticOrbitDiagonal.corner
        (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) x)=
      regularSum (expression A P hN s e) x :=
  finiteNormalizedRegularAmbient_right_terminal A hN P e _ _ _ _ x

#print axioms scheduled_error
#print axioms regular_error
#print axioms physical_error
#print axioms regular_norm
#print axioms physical_norm
#print axioms regular_right_terminal
end QuantitativeEulerEndpointCommonReconstruction
