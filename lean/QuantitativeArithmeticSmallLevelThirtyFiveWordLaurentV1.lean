module

public import QuantitativeArithmeticSmallLevelThirtyFiveWordRowMatrixV1
public import QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticTheoryV4

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex

def fourPrimeMonomial (e : ℤ×ℤ×ℤ×ℤ) (x y z w : ℂ) : ℂ :=
  x^e.1*y^e.2.1*z^e.2.2.1*w^e.2.2.2

def primeParameter (p m : ℕ) (s : ℂ) : ℂ := (p:ℂ)^(s-(m:ℂ))

/-- Positive rational rates have an unambiguous Laurent specialization;
the proof never distributes complex powers across arbitrary complex bases. -/
theorem rational_four_prime_power (r : ℚ) (e : ℤ×ℤ×ℤ×ℤ)
    (hr : r=(2:ℚ)^e.1*(3:ℚ)^e.2.1*(5:ℚ)^e.2.2.1*(7:ℚ)^e.2.2.2)
    (s : ℂ) : (r:ℂ)^s=fourPrimeMonomial e
      ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) := by
  have hreal : (r:ℝ)=(2:ℝ)^e.1*(3:ℝ)^e.2.1*(5:ℝ)^e.2.2.1*(7:ℝ)^e.2.2.2 := by
    simpa only [Rat.cast_mul,Rat.cast_zpow,Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q:ℝ)) hr
  have hc : (r:ℂ)=(((2:ℝ)^e.1*(3:ℝ)^e.2.1*(5:ℝ)^e.2.2.1*(7:ℝ)^e.2.2.2:ℝ):ℂ) := by
    simpa only [Complex.ofReal_ratCast] using congrArg (fun t : ℝ => (t:ℂ)) hreal
  rw [hc,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  simp only [Complex.ofReal_zpow]
  rw [QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic.positive_zpow_cpow (by norm_num : (0:ℝ)<2),
    QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic.positive_zpow_cpow (by norm_num : (0:ℝ)<3),
    QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic.positive_zpow_cpow (by norm_num : (0:ℝ)<5),
    QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic.positive_zpow_cpow (by norm_num : (0:ℝ)<7)]
  rfl

theorem word_leading_laurent (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ)
    (e : ℤ×ℤ×ℤ×ℤ)
    (hr : rationalRate w t=(2:ℚ)^e.1*(3:ℚ)^e.2.1*(5:ℚ)^e.2.2.1*(7:ℚ)^e.2.2.2)
    (s : ℂ) :
    wordCoefficient m χ w t 0 s=χ^(frickeCount w)*fourPrimeMonomial e
      (primeParameter 2 m s) (primeParameter 3 m s)
      (primeParameter 5 m s) (primeParameter 7 m s) := by
  rw [wordCoefficient_rational]
  simp only [pow_zero,Ring.choose_zero_right,mul_one]
  rw [rational_four_prime_power _ e hr]
  rfl

theorem primeParameter_shift (p m : ℕ) (hp : p≠0) (s : ℂ) :
    primeParameter p m (s-1)=primeParameter p m s/(p:ℂ) := by
  unfold primeParameter
  rw [show s-1-(m:ℂ)=(s-(m:ℂ))-1 by ring,
    Complex.cpow_sub _ _ (by exact_mod_cast hp),Complex.cpow_one]

/-- The first correction at s-1 has precisely the common factor
i(s-k) removed in the algebraic first-jet certificate. -/
theorem word_first_shift_factor (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ) (s : ℂ) :
    wordCoefficient m χ w t 1 (s-1)=
      I*(s-((2*m:ℕ):ℂ))*wordCoefficient m χ w t 0 (s-1)*
        (rationalDerivative w t : ℂ) := by
  simp only [wordCoefficient_rational,pow_one,pow_zero,Ring.choose_one_right,
    Ring.choose_zero_right,mul_one,Nat.cast_one,Nat.cast_zero,add_zero]
  ring

theorem word_first_shift_laurent (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ)
    (e : ℤ×ℤ×ℤ×ℤ)
    (hr : rationalRate w t=(2:ℚ)^e.1*(3:ℚ)^e.2.1*(5:ℚ)^e.2.2.1*(7:ℚ)^e.2.2.2)
    (s : ℂ) :
    wordCoefficient m χ w t 1 (s-1)=I*(s-((2*m:ℕ):ℂ))*χ^(frickeCount w)*
      fourPrimeMonomial e (primeParameter 2 m s/2) (primeParameter 3 m s/3)
        (primeParameter 5 m s/5) (primeParameter 7 m s/7)*(rationalDerivative w t : ℂ) := by
  rw [word_first_shift_factor,word_leading_laurent m χ w t e hr,
    primeParameter_shift 2 m (by decide),primeParameter_shift 3 m (by decide),
    primeParameter_shift 5 m (by decide),primeParameter_shift 7 m (by decide)]
  norm_num only [Nat.cast_ofNat]
  ring

#print axioms rational_four_prime_power
#print axioms word_leading_laurent
#print axioms word_first_shift_laurent
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
