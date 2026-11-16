module

public import QuantitativeHolomorphicNewtonCoefficientsV1
public import QuantitativeMaassNewtonScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter QuantitativeHolomorphic
open scoped Topology

namespace QuantitativeMaass

theorem inverseSqrtPolynomial_support_card (n : ℕ) :
    (inverseSqrtPolynomial n).support.card≤3^n := by
  have hh : (inverseSqrtPolynomial n).support.card≤(inverseSqrtPolynomial n).natDegree+1 := by
    apply (Finset.card_le_card (show (inverseSqrtPolynomial n).support ⊆
      Finset.range ((inverseSqrtPolynomial n).natDegree+1) from ?_)).trans_eq (Finset.card_range _)
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)))
  exact hh.trans (inverseSqrtPolynomial_degree_bound n)

/-- Explicit coefficient cost for the actual Newton polynomials, without
an assumed bound on a user-supplied polynomial sequence. -/
theorem inverseSqrtPolynomial_source_cost (n : ℕ) :
    ((inverseSqrtPolynomial n).support.card:ℝ)*
      (∑ j∈(inverseSqrtPolynomial n).support,((inverseSqrtPolynomial n).coeff j)^2)≤
        (48:ℝ)^(4^n) := by
  let p := inverseSqrtPolynomial n
  have hc : (p.support.card:ℝ)≤(3:ℝ)^n := by exact_mod_cast inverseSqrtPolynomial_support_card n
  have hs : (∑ j∈p.support,(p.coeff j)^2)≤(polynomialMass p 1)^2 := by
    have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := p.support)
      (f := fun j => |p.coeff j|) (by intros; exact abs_nonneg _)
    simpa only [sq_abs,polynomialMass,one_pow,mul_one] using hh
  have hm : 0≤polynomialMass p 1 := by unfold polynomialMass; positivity
  have hmass : polynomialMass p 1≤(4:ℝ)^(4^n) := by
    simpa only [show (3:ℝ)+1=4 by norm_num] using
      polynomialMass_inverseSqrt_le (by norm_num : (0:ℝ)≤1) n
  have hn : n≤4^n := (Nat.lt_pow_self (by norm_num : 1<(4:ℕ))).le
  calc
    _ ≤ (3:ℝ)^n*(polynomialMass p 1)^2 :=
      mul_le_mul hc hs (by positivity) (by positivity)
    _ ≤ (3:ℝ)^(4^n)*((4:ℝ)^(4^n))^2 := by
      apply mul_le_mul (pow_le_pow_right₀ (by norm_num) hn)
        (pow_le_pow_left₀ hm hmass 2) (by positivity) (by positivity)
    _ = _ := by rw [pow_two,←mul_pow,←mul_pow]; norm_num

/-- The scheduled actual Newton degree and coefficient cost both fit the
proved fourth-root exponential compression regime. -/
theorem bandNewtonDepth_source_cost :
    ∀ᶠ t in atTop,
      ((inverseSqrtPolynomial (bandNewtonDepth t)).natDegree:ℝ)≤2*fourthRootScale t ∧
      ((inverseSqrtPolynomial (bandNewtonDepth t)).support.card:ℝ)*
        (∑ j∈(inverseSqrtPolynomial (bandNewtonDepth t)).support,
          ((inverseSqrtPolynomial (bandNewtonDepth t)).coeff j)^2)≤
        Real.exp ((2*Real.log 48)*fourthRootScale t) := by
  filter_upwards [bandNewtonDepth_cost_bound] with t ht
  let n := bandNewtonDepth t
  have hdeg : (inverseSqrtPolynomial n).natDegree≤4^n := by
    have hd := inverseSqrtPolynomial_degree_bound n
    have hp : (3:ℕ)^n≤4^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    omega
  constructor
  · exact (by exact_mod_cast hdeg : ((inverseSqrtPolynomial n).natDegree:ℝ)≤(4:ℝ)^n).trans ht
  · apply (inverseSqrtPolynomial_source_cost n).trans
    have heq : (48:ℝ)^(4^n)=Real.exp (((4^n:ℕ):ℝ)*Real.log 48) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<48)]
    rw [heq]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right ht (Real.log_nonneg (by norm_num : (1:ℝ)≤48))
    push_cast
    nlinarith only [hh]

#print axioms inverseSqrtPolynomial_support_card
#print axioms inverseSqrtPolynomial_source_cost
#print axioms bandNewtonDepth_source_cost

end QuantitativeMaass
