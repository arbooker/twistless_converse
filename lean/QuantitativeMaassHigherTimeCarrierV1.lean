module

public import QuantitativeMaassWindowAbelDecayV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Every derivative of a modulated carrier is expressed without differentiating
the spectral phase again. -/
theorem timeDerivativeCarrier_iterated (t : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) (n : ℕ) (u : ℝ) :
    iteratedDeriv n (timeDerivativeCarrier t A) u=
      (t:ℂ)*Complex.I*iteratedDeriv n A u+iteratedDeriv (n+1) A u := by
  have hAd : ContDiff ℝ ∞ (deriv A) := (contDiff_infty_iff_deriv.mp hA).2
  have hAn : ContDiffAt ℝ n A u := (hA.of_le (by simp)).contDiffAt
  have hAn' : ContDiffAt ℝ n (deriv A) u := (hAd.of_le (by simp)).contDiffAt
  have hc : ContDiffAt ℝ n (fun x => (t:ℂ)*Complex.I*A x) u :=
    contDiffAt_const.mul hAn
  change iteratedDeriv n ((fun x => (t:ℂ)*Complex.I*A x)+deriv A) u=_
  rw [iteratedDeriv_add hc hAn',iteratedDeriv_const_mul _ hAn,← iteratedDeriv_succ']

/-- Explicit derivative costs for arbitrary finite carrier order. -/
theorem timeDerivativeCarrier_iterated_bound (t : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) (m : ℕ) (M : ℝ)
    (hb : ∀ n : ℕ,n≤m+1 → ∀ u,‖iteratedDeriv n A u‖≤M) :
    ∀ n : ℕ,n≤m → ∀ u,‖iteratedDeriv n (timeDerivativeCarrier t A) u‖≤(|t|+1)*M := by
  intro n hn u
  rw [timeDerivativeCarrier_iterated t A hA n u]
  calc
    _ ≤ ‖(t:ℂ)*Complex.I*iteratedDeriv n A u‖+‖iteratedDeriv (n+1) A u‖ := norm_add_le _ _
    _ = |t| *‖iteratedDeriv n A u‖+‖iteratedDeriv (n+1) A u‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    _ ≤ |t| *M+M := add_le_add
      (mul_le_mul_of_nonneg_left (hb n (by omega) u) (abs_nonneg _)) (hb (n+1) (by omega) u)
    _ = _ := by ring

/-- First two time derivatives retain the square-root-frequency estimate with
only three derivatives of the original carrier. -/
theorem timeSecondDerivativeCarrier_bounds (t : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) (M : ℝ)
    (hb : ∀ n : ℕ,n≤3 → ∀ u,‖iteratedDeriv n A u‖≤M) :
    ∀ n : ℕ,n≤1 → ∀ u,
      ‖iteratedDeriv n (timeDerivativeCarrier t (timeDerivativeCarrier t A)) u‖≤(|t|+1)^2*M := by
  have h1 := timeDerivativeCarrier_iterated_bound t A hA 2 M hb
  have h2 := timeDerivativeCarrier_iterated_bound t (timeDerivativeCarrier t A)
    (timeDerivativeCarrier_smooth t A hA) 1 ((|t|+1)*M) h1
  intro n hn u
  convert h2 n hn u using 1
  ring

#print axioms timeDerivativeCarrier_iterated
#print axioms timeDerivativeCarrier_iterated_bound
#print axioms timeSecondDerivativeCarrier_bounds

end QuantitativeMaass
