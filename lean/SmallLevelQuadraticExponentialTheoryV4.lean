module

public import QuantitativeArithmeticQuadraticTwistQuotientOrderV1

/-! Consolidated chapter: SmallLevelQuadraticExponential. Original declarations and local scopes are retained. -/

/-! ## SmallLevelQuadraticExponentialOrderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace SmallLevelQuadraticExponential
open Complex FinitenessOriginalInput QuantitativeArithmeticQuadraticTwistQuotient

def plusFactor (a : ℂ) : ℂ := (a+(a^2-4)^(2⁻¹:ℂ))/2
def minusFactor (a : ℂ) : ℂ := (a-(a^2-4)^(2⁻¹:ℂ))/2

theorem quadratic_factorization (a x : ℂ) :
    1+a*x+x^2=(1+plusFactor a*x)*(1+minusFactor a*x) := by
  have hs : ((a^2-4)^(2⁻¹:ℂ))^2=a^2-4 :=
    Complex.cpow_nat_inv_pow _ (by decide : (2:ℕ)≠0)
  dsimp [plusFactor,minusFactor]
  linear_combination (x^2/4)*hs

theorem factor_entire (c m : ℂ) :
    Differentiable ℂ (fun s : ℂ => 1+c*(2:ℂ)^(m-s)) := by
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop

/-- Entire division by a quadratic in2^(m-s) preserves finite order,
including repeated roots and arbitrary complex coefficient. -/
theorem finiteOrder_of_quadratic (a m : ℂ) {A G : ℂ → ℂ}
    (hAc : Continuous A) (hA : FiniteOrder A) (hG : Differentiable ℂ G)
    (hAG : ∀ s, (1+a*(2:ℂ)^(m-s)+((2:ℂ)^(m-s))^2)*G s=A s) :
    FiniteOrder G := by
  have hi : Differentiable ℂ (fun s => (1+minusFactor a*(2:ℂ)^(m-s))*G s) :=
    (factor_entire (minusFactor a) m).mul hG
  have ho : FiniteOrder (fun s => (1+minusFactor a*(2:ℂ)^(m-s))*G s) := by
    apply finiteOrder_of_two_factor (plusFactor a) m hAc hA hi
    intro s
    rw [← mul_assoc,← quadratic_factorization]
    exact hAG s
  exact finiteOrder_of_two_factor (minusFactor a) m hi.continuous ho hG (fun _ => rfl)

#print axioms quadratic_factorization
#print axioms finiteOrder_of_quadratic
end SmallLevelQuadraticExponential
end
end

/-! ## SmallLevelPositiveBaseExponentialOrderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelQuadraticExponential
open Complex FinitenessOriginalInput QuantitativeArithmeticQuadraticTwistQuotient

theorem finiteOrder_of_base_factor (p : ℕ) (hp : 1<p) (c m : ℂ) {A G : ℂ→ℂ}
    (hAc : Continuous A) (hA : FiniteOrder A) (hG : Differentiable ℂ G)
    (hAG : ∀ s,(1+c*(p:ℂ)^(m-s))*G s=A s) : FiniteOrder G := by
  have hpR : (1:ℝ)<p := by exact_mod_cast hp
  have hl : (Real.log p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hpR).ne'
  apply finiteOrder_of_exponential_factor (a:= -(Real.log p:ℂ))
    (c:= -c*exp ((Real.log p:ℂ)*m)) (neg_ne_zero.mpr hl) hAc hA hG
  intro s
  convert hAG s using 2
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by omega : p≠0)),
    show log (p:ℂ)=(Real.log p:ℂ) from (Complex.ofReal_log (Nat.cast_nonneg p)).symm]
  rw [show (Real.log p:ℂ)*(m-s)=(Real.log p:ℂ)*m+ -(Real.log p:ℂ)*s by ring,exp_add]
  ring

theorem base_factor_entire (p : ℕ) (hp : p≠0) (c m : ℂ) :
    Differentiable ℂ (fun s : ℂ => 1+c*(p:ℂ)^(m-s)) := by
  simp_rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp : (p:ℂ)≠0)]
  fun_prop

/-- Quadratic division at any positive integral base greater than one,
including repeated roots and all complex Hecke coefficients. -/
theorem finiteOrder_of_quadratic_base (p : ℕ) (hp : 1<p) (a m : ℂ) {A G : ℂ→ℂ}
    (hAc : Continuous A) (hA : FiniteOrder A) (hG : Differentiable ℂ G)
    (hAG : ∀ s,(1+a*(p:ℂ)^(m-s)+((p:ℂ)^(m-s))^2)*G s=A s) : FiniteOrder G := by
  have hi : Differentiable ℂ (fun s => (1+minusFactor a*(p:ℂ)^(m-s))*G s) :=
    (base_factor_entire p (by omega) (minusFactor a) m).mul hG
  have ho : FiniteOrder (fun s => (1+minusFactor a*(p:ℂ)^(m-s))*G s) := by
    apply finiteOrder_of_base_factor p hp (plusFactor a) m hAc hA hi
    intro s
    rw [←mul_assoc,←quadratic_factorization]
    exact hAG s
  exact finiteOrder_of_base_factor p hp (minusFactor a) m hi.continuous ho hG (fun _ => rfl)

#print axioms finiteOrder_of_base_factor
#print axioms finiteOrder_of_quadratic_base
end SmallLevelQuadraticExponential
end
end
