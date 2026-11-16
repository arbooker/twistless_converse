module

public import QuantitativeMaassRegularMetricAmplitudeV1
public import QuantitativeEulerEndpointSectorWeightedBridgeV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticNestedQuotients AsymptoticSectorSigns QuantitativeNewGap
open AsymptoticRegularTrace ContinuousLinearMap AsymptoticClassicalPetersson
open scoped lp ENNReal ComplexConjugate
namespace QuantitativeMaass.CountingMetric

theorem diagonal_sandwich_matrix {X : Type*} (c : X→ℂ) {C : ℝ} (hC : 0≤C)
    (hc : ∀ q,‖c q‖≤C) (P : ℓ²(X,ℂ)→L[ℂ]ℓ²(X,ℂ)) (i j : X) :
    matrix ((AsymptoticOrbitDiagonal.operator c hC hc).comp P |>.comp
      (AsymptoticOrbitDiagonal.operator c hC hc).adjoint) i j=
      c i*conj (c j)*matrix P i j := by
  change (AsymptoticOrbitDiagonal.operator c hC hc)
    (P ((AsymptoticOrbitDiagonal.operator c hC hc).adjoint (delta j))) i=_
  rw [AsymptoticOrbitDiagonal.operator_adjoint,AsymptoticOrbitDiagonal.operator_delta,
    map_smul,AsymptoticOrbitDiagonal.operator_apply]
  change c i*(conj (c j)*P (delta j) i)=c i*conj (c j)*P (delta j) i
  ring

variable {ι : Type*} [Fintype ι] [Nonempty ι]
    (N : ℕ) (g : ι→quotientNormalizerGroup N)
    {δ Y : ℝ} (hδ : 0<δ) (hY : 0<Y) {ν : ℕ} (hν : 1≤ν)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im)

/-- A literal regular metric compression, with the same coefficient as
its physical scalar-corrected cap. -/
def metricCompression (P : ℓ²(Classes (gamma N),ℂ)→L[ℂ]ℓ²(Classes (gamma N),ℂ))
    (z : ℍ) : ℓ²(AsymptoticRationalGroup.Group,ℂ)→L[ℂ]ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  AsymptoticCongruenceQuotient.compression N hδ hν
    (((regularMetricDiagonal N g hδ hY hν hcover z).comp P).comp
      (regularMetricDiagonal N g hδ hY hν hcover z).adjoint) z

theorem metricCompression_diagonal
    (P : ℓ²(Classes (gamma N),ℂ)→L[ℂ]ℓ²(Classes (gamma N),ℂ)) (z : ℍ) :
    (matrix (metricCompression N g hδ hY hν hcover P z) 1 1).re=
      ‖amplitude N δ ν z*((Real.sqrt (weight N δ ν z)*normalizerCoverMetric N g δ ν z:ℝ):ℂ)‖^2*
        (matrix P (classOf (gamma N) 1) (classOf (gamma N) 1)).re := by
  rw [metricCompression,AsymptoticCongruenceQuotient.compression_matrix]
  dsimp only [regularMetricDiagonal]
  rw [diagonal_sandwich_matrix]
  change (amplitude N δ ν (1 • z)*conj (amplitude N δ ν (1 • z))*
    (regularCoverCoefficient N g δ ν z (classOf (gamma N) 1)*
      conj (regularCoverCoefficient N g δ ν z (classOf (gamma N) 1))*
        matrix P (classOf (gamma N) 1) (classOf (gamma N) 1))).re=_
  rw [regularCoverCoefficient_classOf,one_smul,Complex.mul_conj',Complex.mul_conj',norm_mul,mul_pow]
  simp only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- The metric canonical model has exactly the original regular trace;
there is no multiplicative metric loss in its leading mass. -/
theorem metricCompression_trace (hN : 0<N)
    (P : ℓ²(Classes (gamma N),ℂ)→L[ℂ]ℓ²(Classes (gamma N),ℂ))
    (hP : 0≤(matrix P (classOf (gamma N) 1) (classOf (gamma N) 1)).re) :
    trace volume (metricCompression N g hδ hY hν hcover P)=
      trace volume (AsymptoticCongruenceQuotient.compression N hδ hν P) := by
  have hp (z) : 0<normalizerCoverWeight N g δ ν z :=
    (heightWeightFloor_pos hδ hY ν).trans_le (normalizerCoverWeight_lower N g hδ hY hν hcover z)
  rw [AsymptoticCongruenceQuotient.compression_trace_covolume N hδ hν hN P hP]
  unfold trace
  simp_rw [metricCompression_diagonal N g hδ hY hν hcover P,
    mul_comm _ (matrix P (classOf (gamma N) 1) (classOf (gamma N) 1)).re,
    ENNReal.ofReal_mul hP]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,metric_amplitude_mass N g hδ hν hp,
    quotientMeasure_univ N hN]
  rfl

#print axioms diagonal_sandwich_matrix
#print axioms metricCompression_diagonal
#print axioms metricCompression_trace
end QuantitativeMaass.CountingMetric
