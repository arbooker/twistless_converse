module

public import QuantitativeEulerEndpointCornerPolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointResidual
open Polynomial
open scoped Classical

/-- Explicit coefficient budget for approximate polynomial invariance. -/
def slopeMass (q : ℝ[X]) : ℝ := ∑ i∈q.support, |q.coeff i| * (i:ℝ)

theorem slopeMass_nonneg (q : ℝ[X]) : 0≤slopeMass q :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

theorem slopeMass_le (q : ℝ[X]) :
    slopeMass q≤(q.natDegree:ℝ)*(∑ i∈q.support, |q.coeff i|) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hd : (i:ℝ)≤q.natDegree := by exact_mod_cast le_natDegree_of_mem_supp i hi
  nlinarith [abs_nonneg (q.coeff i)]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem mul_contract (a b : A) (ha : ‖a‖≤1) : ‖a*b‖≤‖b‖ :=
  (norm_mul_le a b).trans (by nlinarith [norm_nonneg b])

theorem power_residual (a E : A) (r : ℝ) (ha : ‖a‖≤1) (hr : |r|≤1) (n : ℕ) :
    ‖a^n*E-r^n • E‖≤(n:ℝ)*‖a*E-r • E‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : a^(n+1)*E-r^(n+1) • E=
        a*(a^n*E-r^n • E)+r^n • (a*E-r • E) := by
      rw [pow_succ',pow_succ,mul_sub,smul_sub,mul_smul_comm,smul_smul]
      noncomm_ring
    have hrn : ‖r^n‖≤1 := by
      rw [norm_pow,Real.norm_eq_abs]
      exact pow_le_one₀ (abs_nonneg r) hr
    rw [he]
    have hh : ‖a*(a^n*E-r^n • E)+r^n • (a*E-r • E)‖≤
        ‖a^n*E-r^n • E‖+‖a*E-r • E‖ :=
      (norm_add_le _ _).trans
        (add_le_add (mul_contract a _ ha) (by rw [norm_smul]; nlinarith [norm_nonneg (a*E-r • E)]))
    push_cast
    nlinarith

/-- A contraction approximately satisfying a scalar relation satisfies the
same polynomial relation, with an explicit coefficient/degree budget. -/
theorem polynomial_residual (a E : A) (r : ℝ) (ha : ‖a‖≤1) (hr : |r|≤1) (q : ℝ[X]) :
    ‖aeval a q*E-q.eval r • E‖≤slopeMass q*‖a*E-r • E‖ := by
  have he : aeval a q*E-q.eval r • E=
      ∑ i∈q.support, q.coeff i • (a^i*E-r^i • E) := by
    rw [QuantitativeEulerEndpointCornerPolynomial.aeval_sum,eval_eq_sum,sum_def,
      Finset.sum_mul,Finset.sum_smul,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_mul_assoc,mul_smul,smul_sub]
  rw [he,slopeMass,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,Real.norm_eq_abs]
  have hh := mul_le_mul_of_nonneg_left (power_residual a E r ha hr i) (abs_nonneg (q.coeff i))
  simpa only [mul_assoc] using hh

theorem polynomial_fixed_residual (a E : A) (ha : ‖a‖≤1) (q : ℝ[X]) (hq : q.eval 1=1) :
    ‖aeval a q*E-E‖≤slopeMass q*‖a*E-E‖ := by
  simpa only [hq,one_smul] using polynomial_residual a E 1 ha (by norm_num) q

theorem polynomial_zero_residual (a E : A) (ha : ‖a‖≤1) (q : ℝ[X]) (hq : q.eval 0=1) :
    ‖aeval a q*E-E‖≤slopeMass q*‖a*E‖ := by
  simpa only [hq,one_smul,zero_smul,sub_zero] using polynomial_residual a E 0 ha (by norm_num) q

#print axioms polynomial_residual
#print axioms polynomial_fixed_residual
#print axioms polynomial_zero_residual
end QuantitativeEulerEndpointResidual
