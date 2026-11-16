module

public import QuantitativeMaassFinitePolynomialEnergyV1
public import QuantitativeHolomorphicNewtonCoefficientsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open scoped BigOperators
open QuantitativeHolomorphic

namespace QuantitativeMaass

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype ι]

/-- Polynomial coefficient mass gives an explicit dimension-free bound
for the error measured on a finite spectral band. -/
theorem finiteBandEnergy_aeval_difference (b : OrthonormalBasis ι ℂ E)
    (A B : E →L[ℂ] E) {D : ℝ} (hD : 1≤D) (hA : ‖A‖≤D) (hB : ‖B‖≤D)
    (p : Polynomial ℝ) :
    finiteBandEnergy b (Polynomial.aeval A p-Polynomial.aeval B p) ≤
      ((p.support.card:ℝ)*(polynomialMass p (2*D))^2)*finiteBandEnergy b (A-B) := by
  have hD0 : 0≤D := zero_le_one.trans hD
  have hs : (∑ j ∈ p.support,(p.coeff j)^2*(4*D^2)^j) ≤
      (polynomialMass p (2*D))^2 := by
    have hh := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := p.support) (f := fun j => |p.coeff j| * (2*D)^j) (by intros; positivity)
    unfold polynomialMass
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow (|p.coeff j|) ((2*D)^j) 2,sq_abs]
    congr 1
    rw [←pow_mul,Nat.mul_comm j 2,pow_mul]
    congr 1
    ring
  rw [polynomial_aeval_sum,polynomial_aeval_sum]
  exact (finiteBandEnergy_polynomial_difference b A B hD hA hB p.support p.coeff).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
      (finiteBandEnergy_nonneg b _))

/-- The Newton inverse-square-root polynomial has a completely explicit
Hilbert--Schmidt perturbation cost, uniform in the spectral band. -/
theorem finiteBandEnergy_newton_difference (b : OrthonormalBasis ι ℂ E)
    (A B : E →L[ℂ] E) {D : ℝ} (hD : 1≤D) (hA : ‖A‖≤D) (hB : ‖B‖≤D)
    (n : ℕ) :
    finiteBandEnergy b (Polynomial.aeval A (inverseSqrtPolynomial n)-
      Polynomial.aeval B (inverseSqrtPolynomial n)) ≤
      ((3^n:ℕ):ℝ)*(3+2*D)^(2*(4^n))*finiteBandEnergy b (A-B) := by
  have hD0 : 0≤D := zero_le_one.trans hD
  have hcard : (inverseSqrtPolynomial n).support.card ≤ 3^n := by
    have hh : (inverseSqrtPolynomial n).support.card ≤
        (inverseSqrtPolynomial n).natDegree+1 := by
      apply (Finset.card_le_card (show (inverseSqrtPolynomial n).support ⊆
        Finset.range ((inverseSqrtPolynomial n).natDegree+1) from ?_)).trans_eq (Finset.card_range _)
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)))
    exact hh.trans (inverseSqrtPolynomial_degree_bound n)
  have hm : 0≤polynomialMass (inverseSqrtPolynomial n) (2*D) := by
    unfold polynomialMass
    positivity
  have hp := pow_le_pow_left₀ hm (polynomialMass_inverseSqrt_le
    (by positivity : 0≤2*D) n) 2
  have he := finiteBandEnergy_aeval_difference b A B hD hA hB (inverseSqrtPolynomial n)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (finiteBandEnergy_nonneg b _)
  have hc : ((inverseSqrtPolynomial n).support.card:ℝ) ≤ ((3^n:ℕ):ℝ) := by
    exact_mod_cast hcard
  exact (mul_le_mul hc hp (sq_nonneg _) (Nat.cast_nonneg _)).trans_eq (by
    rw [←pow_mul,Nat.mul_comm (4^n) 2])

#print axioms finiteBandEnergy_aeval_difference
#print axioms finiteBandEnergy_newton_difference

end QuantitativeMaass
