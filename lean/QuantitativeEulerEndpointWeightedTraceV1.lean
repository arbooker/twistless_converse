module

public import QuantitativeEulerEndpointActualRetainedSectorTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointWeightedTrace
open ContinuousLinearMap AsymptoticCylinder AsymptoticObservation AsymptoticDiagonalTrace
open AsymptoticFiniteBranch
open AsymptoticFourierNorm QuantitativeHolomorphic AsymptoticCylinderModeComparison

section Generic
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem retained_sandwich (V : G →L[ℂ] Space) (F : G →L[ℂ] G) (Y H : ℝ)
    (hV : (upperProjection Y).comp V=V) (W : Submodule ℂ Space) [CompleteSpace W] :
    compressedSandwich (retainedProjection Y H) (V.comp (F.comp V.adjoint)) W=
      compressedSandwich (removePart (upperProjection H) V) F W := by
  have hp : (retainedProjection Y H).comp V=removePart (upperProjection H) V := by
    rw [retainedProjection,comp_assoc,hV]
    ext1 x
    simp [removePart]
  rw [←hp]
  simp only [compressedSandwich,adjoint_comp,retainedProjection_adjoint,comp_assoc]

theorem contraction_sandwich (V : G →L[ℂ] Space) (F : G →L[ℂ] G)
    (hV : ‖V‖≤1) (hF : ‖F‖≤1) : ‖V.comp (F.comp V.adjoint)‖≤1 := by
  have ha : ‖V.adjoint‖≤1 := by rwa [adjoint.norm_map]
  have hf : ‖F.comp V.adjoint‖≤1 := (opNorm_comp_le _ _).trans
    (by simpa only [one_mul] using mul_le_mul hF ha (norm_nonneg _) zero_le_one)
  exact (opNorm_comp_le _ _).trans (by simpa only [one_mul] using mul_le_mul hV hf (norm_nonneg _) zero_le_one)

/-- Weighted and unweighted traces of the same output-truncated sandwich.
The terminal filter and all its coefficients are unchanged. -/
theorem upper_weighted_difference (m t : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) (H : ℝ)
    (V : G →L[ℂ] Space) (F : G →L[ℂ] G) (hV : ‖V‖≤1) (hF : ‖F‖≤1)
    (hs : (upperProjection Y).comp V=V) :
    ‖upperCutTrace V F m t (by positivity : 0<4*Real.pi) hε H-
      upperCutTrace V F m 0 (by positivity : 0<4*Real.pi) hε H‖/(m+2:ℝ)≤
      (2*Real.sqrt (localizedErrorBound t (4*Real.pi) Y)*Real.sqrt (massSlope t (4*Real.pi) Y))*
        (Real.sqrt (m+2:ℝ))⁻¹ := by
  have hh := retained_weighted_trace_difference m t hε hY H (V.comp (F.comp V.adjoint))
    (contraction_sandwich V F hV hF)
  rw [retained_sandwich V F Y H hs,retained_sandwich V F Y H hs] at hh
  rw [norm_div,Real.norm_of_nonneg (by positivity : (0:ℝ)≤m+2)] at hh
  exact hh
end Generic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic.Schedule
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- Sharp coefficient growth in the scheduled lower cutoff. -/
theorem lower_mode_sharp {s : ℝ} (hs : 1≤s) (h : ℕ) :
    let n := newtonDepth A P 2 (Real.exp (-8*s))
    let Y := lowerCutoff A P 2 (Real.exp (-8*s)) n
    let P' := AsymptoticReconstructedCount.parameters A P
    (2*Real.sqrt (localizedErrorBound (P'.s+4) (4*Real.pi) Y)*Real.sqrt (massSlope (P'.s+4) (4*Real.pi) Y))*
      (Real.sqrt (2*h+2:ℝ))⁻¹≤
      Real.exp ((2*lowerModeCoefficient A P+abs (lowerInverseGrowthConstant A P 0))*s^4)*
        (Real.sqrt (2*h+2:ℝ))⁻¹ := by
  intro n Y P'
  have hh := countFilterError_schedule A P 0 (Real.exp_pos (-8*s))
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at hh
  have hY : 0<Y := hh.2.1
  have hi := growing_lower_inverse A P (C:=0) (by norm_num) hs 0 (by norm_num)
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at hi
  have hi' : Y⁻¹≤Real.exp (abs (lowerInverseGrowthConstant A P 0)*s^4) := hi.trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
  have hT := lowerModeCoefficient_nonneg A P
  have hE : 1≤Real.exp (abs (lowerInverseGrowthConstant A P 0)*s^4) := Real.one_le_exp (by positivity)
  have hcoeff : lowerModeCoefficient A P*(1+Y⁻¹)≤
      Real.exp ((2*lowerModeCoefficient A P+abs (lowerInverseGrowthConstant A P 0))*s^4) := by
    calc
      _ ≤ (2*lowerModeCoefficient A P)*Real.exp (abs (lowerInverseGrowthConstant A P 0)*s^4) := by
        nlinarith [mul_le_mul_of_nonneg_left hi' hT,mul_le_mul_of_nonneg_left hE hT]
      _ ≤ _ := constant_mul_exp_le (by positivity) (by simpa using pow_le_pow_right₀ hs (by norm_num : 0≤4))
  exact mul_le_mul_of_nonneg_right
    ((localized_sqrt_product_le (P'.s+4) (by positivity : 0<4*Real.pi) hY).trans hcoeff) (by positivity)

#print axioms retained_sandwich
#print axioms upper_weighted_difference
#print axioms lower_mode_sharp
end QuantitativeEulerEndpointWeightedTrace
