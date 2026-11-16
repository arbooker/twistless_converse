module

public import QuantitativeMaassDistributionExpTermsV1
public import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

theorem nat_succ_sq_le_four_pow (n : ℕ) : (n+1:ℝ)^2≤4^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ (4:ℝ) n]
    push_cast
    nlinarith [show (0:ℝ)≤n by positivity]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

private theorem pow_apply_norm_bound (B : H →L[ℝ] H) (x : H) (n : ℕ) :
    ‖(B^n) x‖≤‖B‖^n*‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp]
    calc
      _ ≤ ‖B‖*‖(B^n) x‖ := B.le_opNorm _
      _ ≤ ‖B‖*(‖B‖^n*‖x‖) := mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = _ := by rw [pow_succ']; ring

theorem distributionExpTerm_norm_bound (T : PositiveSmoothTest →ₗ[ℝ] H)
    (B : H →L[ℝ] H) (φ : PositiveSmoothTest) (C R : ℝ) (hC : 0≤C) (hR : 0≤R)
    (hb : ∀ n,‖T (positiveTestPower n φ)‖≤C*(n+1:ℝ)^2*R^n) (n : ℕ) :
    ‖distributionExpTerm T B φ n‖≤C*((4*‖B‖*R)^n/(n.factorial:ℝ)) := by
  rw [distributionExpTerm,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(n.factorial:ℝ)⁻¹)]
  calc
    _ ≤ (n.factorial:ℝ)⁻¹*(‖B‖^n*(C*(n+1:ℝ)^2*R^n)) := by
      gcongr
      exact (pow_apply_norm_bound B _ n).trans
        (mul_le_mul_of_nonneg_left (hb n) (by positivity))
    _ ≤ (n.factorial:ℝ)⁻¹*(‖B‖^n*(C*4^n*R^n)) := by
      gcongr
      exact nat_succ_sq_le_four_pow n
    _ = _ := by simp only [mul_pow]; ring

/-- A quadratic moment bound suffices for absolute convergence of the
bounded integrating factor. Its polynomial growth is absorbed by 4^n,
leaving the ordinary exponential series. -/
theorem distributionExpTerm_summable [CompleteSpace H]
    (T : PositiveSmoothTest →ₗ[ℝ] H) (B : H →L[ℝ] H) (φ : PositiveSmoothTest)
    (C R : ℝ) (hC : 0≤C) (hR : 0≤R)
    (hb : ∀ n,‖T (positiveTestPower n φ)‖≤C*(n+1:ℝ)^2*R^n) :
    Summable (distributionExpTerm T B φ) := by
  apply Summable.of_norm_bounded ((Real.summable_pow_div_factorial (4*‖B‖*R)).mul_left C)
  exact distributionExpTerm_norm_bound T B φ C R hC hR hb

#print axioms distributionExpTerm_norm_bound
#print axioms distributionExpTerm_summable

end QuantitativeMaass
