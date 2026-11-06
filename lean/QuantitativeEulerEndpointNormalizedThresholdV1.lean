module

public import QuantitativeEulerEndpointBlockNormalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNormalizedThreshold
open QuantitativeEulerEndpointBlockNormalization

variable (C : ℕ → ℝ) (n : ℕ)

def squareSum : ℝ := ∑ i : Fin n, (C i)^2

theorem squareSum_nonneg : 0≤squareSum C n := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem factor_le_one : factor C n≤1 := by
  apply (inv_le_one₀ (show 0<1+squareSum C n by linarith [squareSum_nonneg C n])).mpr
  linarith [squareSum_nonneg C n]

def threshold (A : ℝ) : ℝ := Real.sqrt ((2*(1+2*A))⁻¹)

theorem threshold_pos {A : ℝ} (hA : 0≤A) : 0<threshold A := by
  apply Real.sqrt_pos.mpr
  positivity

theorem threshold_le_one {A : ℝ} (hA : 0≤A) : threshold A≤1 := by
  have ha : (2*(1+2*A))⁻¹≤1 := (inv_le_one₀ (by positivity)).mpr (by linarith)
  simpa only [threshold,Real.sqrt_one] using Real.sqrt_le_sqrt ha

theorem normalized_range {A : ℝ} (hA : 0≤A) :
    0<factor C n*threshold A ∧ factor C n*threshold A≤1 := by
  refine ⟨mul_pos (factor_pos C n) (threshold_pos hA),?_⟩
  exact (mul_le_mul_of_nonneg_right (factor_le_one C n) (threshold_pos hA).le).trans
    (by simpa only [one_mul] using threshold_le_one hA)

/-- Exact denominator after normalizing the ORIGINAL row family and
using its prepared observation threshold. -/
theorem normalized_inverse_square {A : ℝ} (hA : 0≤A) :
    2/(factor C n*threshold A)^2=4*(1+2*A)*(1+squareSum C n)^2 := by
  have ha : 0<2*(1+2*A) := by positivity
  have hs : 0<1+squareSum C n := by linarith [squareSum_nonneg C n]
  rw [mul_pow,threshold,Real.sq_sqrt (inv_pos.mpr ha).le]
  change 2/((1+squareSum C n)⁻¹^2*(2*(1+2*A))⁻¹)=_
  field_simp
  ring

/-- The logarithmic normalization cost separates into observation cost
and the finite sum of PROVED row norm bounds. -/
theorem logarithmic_cost {A : ℝ} (hA : 0≤A) :
    Real.log (2/(factor C n*threshold A)^2)=
      Real.log 4+Real.log (1+2*A)+2*Real.log (1+squareSum C n) := by
  rw [normalized_inverse_square C n hA]
  have ha : 0<1+2*A := by positivity
  have hs : 0<1+squareSum C n := by linarith [squareSum_nonneg C n]
  rw [Real.log_mul (mul_pos (by norm_num) ha).ne' (pow_pos hs 2).ne',
    Real.log_mul (by norm_num : (4:ℝ)≠0) ha.ne',Real.log_pow]
  norm_num

#print axioms normalized_range
#print axioms normalized_inverse_square
#print axioms logarithmic_cost
end QuantitativeEulerEndpointNormalizedThreshold
