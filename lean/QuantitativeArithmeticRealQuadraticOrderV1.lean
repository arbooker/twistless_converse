module
public import SmallLevelQuadraticExponentialTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticQuadraticTwistQuotient
open Complex FinitenessOriginalInput SmallLevelQuadraticExponential

theorem finiteOrder_of_real_factor (p : ℝ) (hp : 1<p) (σ m : ℂ) {A G : ℂ → ℂ}
    (hAc : Continuous A) (hA : FiniteOrder A) (hG : Differentiable ℂ G)
    (hAG : ∀ z : ℂ, (1+σ*(p : ℂ)^(m-z))*G z=A z) : FiniteOrder G := by
  have hl : (Real.log p : ℂ) ≠ 0 := ofReal_ne_zero.mpr
    (ne_of_gt (Real.log_pos hp))
  apply finiteOrder_of_exponential_factor (a := -(Real.log p : ℂ))
    (c := -σ*exp ((Real.log p : ℂ)*m)) (neg_ne_zero.mpr hl) hAc hA hG
  intro z
  convert hAG z using 2
  rw [cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith : p≠0)),
    show log (p : ℂ) = (Real.log p : ℂ) from
      (ofReal_log (by linarith : (0 : ℝ) ≤ p)).symm]
  rw [show (Real.log p : ℂ)*(m-z)=(Real.log p : ℂ)*m + -(Real.log p : ℂ)*z by ring,
    exp_add]
  ring

theorem real_factor_entire (p : ℝ) (hp : 1<p) (c m : ℂ) :
    Differentiable ℂ (fun s : ℂ => 1+c*(p:ℂ)^(m-s)) := by
  have hp0 : (p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  simp_rw [Complex.cpow_def_of_ne_zero hp0]
  fun_prop

/-- Entire division by a quadratic in any real base greater than one
preserves finite order, including repeated roots. -/
theorem finiteOrder_of_real_quadratic (p : ℝ) (hp : 1<p) (a m : ℂ) {A G : ℂ → ℂ}
    (hAc : Continuous A) (hA : FiniteOrder A) (hG : Differentiable ℂ G)
    (hAG : ∀ s, (1+a*(p:ℂ)^(m-s)+((p:ℂ)^(m-s))^2)*G s=A s) :
    FiniteOrder G := by
  have hi : Differentiable ℂ (fun s => (1+minusFactor a*(p:ℂ)^(m-s))*G s) :=
    (real_factor_entire p hp (minusFactor a) m).mul hG
  have ho : FiniteOrder (fun s => (1+minusFactor a*(p:ℂ)^(m-s))*G s) := by
    apply finiteOrder_of_real_factor p hp (plusFactor a) m hAc hA hi
    intro s
    rw [← mul_assoc,← quadratic_factorization]
    exact hAG s
  exact finiteOrder_of_real_factor p hp (minusFactor a) m hi.continuous ho hG (fun _ => rfl)

#print axioms finiteOrder_of_real_quadratic
end QuantitativeArithmeticQuadraticTwistQuotient
