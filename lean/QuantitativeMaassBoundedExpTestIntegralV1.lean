module

public import QuantitativeMaassBoundedExpEvolutionV1
public import QuantitativeMaassTestMomentL1V1
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def boundedExpTestTerm (B : H →L[ℝ] H) (v : H) (φ : PositiveSmoothTest) (n : ℕ) (t : ℝ) : H :=
  ((-1:ℝ)^n*(n.factorial:ℝ)⁻¹) • (positiveTestPower n φ t • (B^n) v)

theorem boundedExpTestTerm_integrable (B : H →L[ℝ] H) (v : H) (φ : PositiveSmoothTest) (n : ℕ) :
    Integrable (boundedExpTestTerm B v φ n) := by
  have hp : Integrable (positiveTestPower n φ : ℝ → ℝ) :=
    (positiveTestPower n φ).continuous.integrable_of_hasCompactSupport (positiveTestPower n φ).hasCompactSupport
  exact (hp.smul_const ((B^n) v)).smul _

theorem boundedExpTestTerm_norm (B : H →L[ℝ] H) (v : H) (φ : PositiveSmoothTest) (n : ℕ) (t : ℝ) :
    ‖boundedExpTestTerm B v φ n t‖=(n.factorial:ℝ)⁻¹*
      (‖positiveTestPower n φ t‖*‖(B^n) v‖) := by
  unfold boundedExpTestTerm
  simp only [norm_smul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,norm_inv,one_mul]
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤n.factorial)]

theorem boundedExpTestTerm_integral_norm_le (B : H →L[ℝ] H) (v : H) (φ : PositiveSmoothTest)
    (R : ℝ) (hR : 0≤R) (hr : ∀ t∈tsupport φ,‖t‖≤R) (n : ℕ) :
    (∫ t,‖boundedExpTestTerm B v φ n t‖)≤
      ((∫ t,‖φ t‖)*‖v‖)*((‖B‖*R)^n/(n.factorial:ℝ)) := by
  simp_rw [boundedExpTestTerm_norm]
  rw [integral_const_mul,integral_mul_const]
  calc
    _ ≤ (n.factorial:ℝ)⁻¹*(((∫ t,‖φ t‖)*R^n)*(‖B‖^n*‖v‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (positiveTestPower_L1_bound φ R hr n) (operatorPower_apply_norm_le B v n)
        (norm_nonneg _) (mul_nonneg (integral_nonneg (fun t => norm_nonneg (φ t))) (pow_nonneg hR n))
    _ = _ := by rw [mul_pow]; ring

theorem boundedExpTestTerm_integral_norm_summable (B : H →L[ℝ] H) (v : H) (φ : PositiveSmoothTest) :
    Summable (fun n => ∫ t,‖boundedExpTestTerm B v φ n t‖) := by
  obtain ⟨R,hR,hr⟩ := positiveSmoothTest_radius φ
  exact Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _))
    (boundedExpTestTerm_integral_norm_le B v φ R hR hr)
    ((Real.summable_pow_div_factorial (‖B‖*R)).mul_left ((∫ t,‖φ t‖)*‖v‖))

variable [CompleteSpace H]

theorem boundedExpTestTerm_hasSum (B : H →L[ℝ] H) (v : H) (φ : PositiveSmoothTest) (t : ℝ) :
    HasSum (fun n => boundedExpTestTerm B v φ n t) (φ t • boundedExpEvolution B v t) := by
  have h := (boundedExpEvolution_hasSum B v t).const_smul (φ t)
  convert! h using 1
  funext n
  simp only [boundedExpTestTerm,positiveTestPower_apply,smul_smul]
  congr 1
  ring

/-- The exponential-moment series is the genuine Bochner integral of the
bounded exponential evolution. Absolute integrability is proved from the
fixed compact test support, so exchanging series and integral is justified. -/
theorem boundedExpEvolution_test_integral (B : H →L[ℝ] H) (v : H) (φ : PositiveSmoothTest) :
    (∑' n,((-1:ℝ)^n*(n.factorial:ℝ)⁻¹) • ((∫ t,φ t*t^n) • (B^n) v))=
      ∫ t,φ t • boundedExpEvolution B v t := by
  have hi := integral_tsum_of_summable_integral_norm (boundedExpTestTerm_integrable B v φ)
    (boundedExpTestTerm_integral_norm_summable B v φ)
  calc
    _ = ∑' n,∫ t,boundedExpTestTerm B v φ n t := by
      apply tsum_congr
      intro n
      simp only [boundedExpTestTerm,positiveTestPower_apply,integral_smul,integral_smul_const]
    _ = ∫ t,∑' n,boundedExpTestTerm B v φ n t := hi
    _ = _ := integral_congr_ae (Eventually.of_forall (fun t => (boundedExpTestTerm_hasSum B v φ t).tsum_eq))

#print axioms boundedExpTestTerm_integral_norm_summable
#print axioms boundedExpEvolution_test_integral

end QuantitativeMaass
