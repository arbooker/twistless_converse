module

public import QuantitativeMaassCrossResidualLeakageV1
public import QuantitativeMaassGraphResidualEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassWave
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- Squared flux-vector control in terms of the source and residual norms.
The spectral denominator cancels the energy cost of the source. -/
theorem residual_flux_norm_bound
    {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : X →L[ℂ] F) (B : E →L[ℂ] Y) (T : X →L[ℂ] Y)
    (g d : X) (v : E) (κ β μ : ℝ) (hκ : 0 ≤ κ) (hβ : 0 ≤ β)
    (hμ : 0 ≤ μ) (hA : ‖A‖ ≤ κ) (hB : ‖B‖ ≤ κ) (hT : ‖T‖ ≤ β)
    (hv : ‖v‖^2 ≤ 2*(1+μ)*‖g‖^2 + ‖d‖^2) :
    ‖A g‖^2 + ‖B v - T d‖^2 / (1+μ) ≤
      5*κ^2*‖g‖^2 + (2*κ^2+2*β^2)*‖d‖^2/(1+μ) := by
  have hAg : ‖A g‖ ≤ κ*‖g‖ := (A.le_opNorm g).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg g))
  have hBv : ‖B v‖ ≤ κ*‖v‖ := (B.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg v))
  have hTd : ‖T d‖ ≤ β*‖d‖ := (T.le_opNorm d).trans
    (mul_le_mul_of_nonneg_right hT (norm_nonneg d))
  have hAg2 : ‖A g‖^2 ≤ κ^2*‖g‖^2 := by
    nlinarith [sq_le_sq₀ (norm_nonneg (A g)) (mul_nonneg hκ (norm_nonneg g)) |>.mpr hAg]
  have hBv2 : ‖B v‖^2 ≤ κ^2*‖v‖^2 := by
    nlinarith [sq_le_sq₀ (norm_nonneg (B v)) (mul_nonneg hκ (norm_nonneg v)) |>.mpr hBv]
  have hTd2 : ‖T d‖^2 ≤ β^2*‖d‖^2 := by
    nlinarith [sq_le_sq₀ (norm_nonneg (T d)) (mul_nonneg hβ (norm_nonneg d)) |>.mpr hTd]
  have hdiff : ‖B v - T d‖^2 ≤ 2*κ^2*‖v‖^2 + 2*β^2*‖d‖^2 := by
    have h := norm_sub_le (B v) (T d)
    have hs := (sq_le_sq₀ (norm_nonneg (B v-T d))
      (add_nonneg (norm_nonneg (B v)) (norm_nonneg (T d)))).mpr h
    nlinarith [sq_nonneg (‖B v‖-‖T d‖)]
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2*κ^2 by positivity)
  have hpos : 0 < 1+μ := by linarith
  have ha := mul_le_mul_of_nonneg_right hAg2 hpos.le
  calc
    _ = (‖A g‖^2*(1+μ) + ‖B v - T d‖^2)/(1+μ) := by
      field_simp
    _ ≤ (5*κ^2*‖g‖^2*(1+μ) + (2*κ^2+2*β^2)*‖d‖^2)/(1+μ) :=
      div_le_div_of_nonneg_right (by nlinarith) hpos.le
    _ = _ := by field_simp

#print axioms residual_flux_norm_bound

end QuantitativeMaass
