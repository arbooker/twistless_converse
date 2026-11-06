module
public import QuantitativeArithmeticSmallLevelThirtyFiveFullTaylorLaurentV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex SmallLevelTaylor FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

theorem fourPrimeMonomial_sign (e : ℤ×ℤ×ℤ×ℤ) (x y z w u v : ℂ) :
    fourPrimeMonomial e x y (u*z) (v*w)=
      u^e.2.2.1*v^e.2.2.2*fourPrimeMonomial e x y z w := by
  simp only [fourPrimeMonomial,mul_zpow]
  ring

theorem word_leading_signed_laurent (m : ℕ) (χ u v : ℂ) (w : Word) (t : ℤ)
    (e : ℤ×ℤ×ℤ×ℤ)
    (hr : rationalRate w t=(2:ℚ)^e.1*(3:ℚ)^e.2.1*(5:ℚ)^e.2.2.1*(7:ℚ)^e.2.2.2)
    (hsign : χ^(frickeCount w)=(-1:ℂ)^(frickeCount w)*u^e.2.2.1*v^e.2.2.2)
    (s : ℂ) :
    wordCoefficient m χ w t 0 s=(-1:ℂ)^(frickeCount w)*fourPrimeMonomial e
      (primeParameter 2 m s) (primeParameter 3 m s)
      (u*primeParameter 5 m s) (v*primeParameter 7 m s) := by
  rw [word_leading_laurent m χ w t e hr,hsign,fourPrimeMonomial_sign]
  ring

theorem fullTaylorCoefficient_signed_laurent (m : ℕ) (f : ℕ → ℂ) (ε u v : ℂ)
    (q : ℕ) (t : ℤ) (e : ℤ×ℤ×ℤ×ℤ)
    (hr : (Nat.lcm 35 (q^2):ℚ)*((t:ℚ)/210)^2=
      (2:ℚ)^e.1*(3:ℚ)^e.2.1*(5:ℚ)^e.2.2.1*(7:ℚ)^e.2.2.2)
    (hsign : root 35 f q*ε*I^(2*m)= -u^e.2.2.1*v^e.2.2.2) (s : ℂ) :
    fullTaylorCoefficient (2*m) f ε q t 0 s=
      -fourPrimeMonomial e (primeParameter 2 m s) (primeParameter 3 m s)
        (u*primeParameter 5 m s) (v*primeParameter 7 m s) := by
  have hex : s-((2*m:ℕ):ℂ)/2=s-(m:ℂ) := by push_cast; ring
  have hc : (((Nat.lcm 35 (q^2):ℝ)*((t:ℝ)/210)^2:ℝ):ℂ)=
      (((Nat.lcm 35 (q^2):ℚ)*((t:ℚ)/210)^2:ℚ):ℂ) := by push_cast; rfl
  simp only [fullTaylorCoefficient,taylorRowScalar,hsign,
    pow_zero,Ring.choose_zero_right,mul_one,hex,hc]
  rw [rational_four_prime_power _ e hr,fourPrimeMonomial_sign]
  simp only [primeParameter,Nat.cast_ofNat]
  ring

theorem root_signed_10 (f : ℕ → ℂ) : root 35 f 10=-badFive f := by
  have hp : (10:ℕ).primeFactors={2,5} := by
    rw [show (10:ℕ)=2*5 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    rw [(by decide : Nat.Prime 2).primeFactors,(by decide : Nat.Prime 5).primeFactors]
    decide
  have hv2 : (10:ℕ).factorization 2=1 := by
    rw [show (10:ℕ)=2*5 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 2).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣5)]
  have hv5 : (10:ℕ).factorization 5=1 := by
    rw [show (10:ℕ)=5*2 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 5).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬5∣2)]
  norm_num [root,hp,hv2,hv5,FinitenessNormalizedTwistLocal.sign,badFive,badSeven]
  ring

theorem root_signed_14 (f : ℕ → ℂ) : root 35 f 14=-badSeven f := by
  have hp : (14:ℕ).primeFactors={2,7} := by
    rw [show (14:ℕ)=2*7 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    rw [(by decide : Nat.Prime 2).primeFactors,(by decide : Nat.Prime 7).primeFactors]
    decide
  have hv2 : (14:ℕ).factorization 2=1 := by
    rw [show (14:ℕ)=2*7 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 2).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣7)]
  have hv7 : (14:ℕ).factorization 7=1 := by
    rw [show (14:ℕ)=7*2 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 7).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬7∣2)]
  norm_num [root,hp,hv2,hv7,FinitenessNormalizedTwistLocal.sign,badFive,badSeven]
  ring

theorem root_signed_70 (f : ℕ → ℂ) : root 35 f 70=badFive f*badSeven f := by
  have hp : (70:ℕ).primeFactors={2,5,7} := by
    rw [show (70:ℕ)=2*5*7 by decide,Nat.primeFactors_mul (by decide) (by decide),Nat.primeFactors_mul (by decide) (by decide)]
    rw [(by decide : Nat.Prime 2).primeFactors,(by decide : Nat.Prime 5).primeFactors,(by decide : Nat.Prime 7).primeFactors]
    decide
  have hv2 : (70:ℕ).factorization 2=1 := by
    rw [show (70:ℕ)=2*35 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 2).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣35)]
  have hv5 : (70:ℕ).factorization 5=1 := by
    rw [show (70:ℕ)=5*14 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 5).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬5∣14)]
  have hv7 : (70:ℕ).factorization 7=1 := by
    rw [show (70:ℕ)=7*10 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 7).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬7∣10)]
  norm_num [root,hp,hv2,hv5,hv7,FinitenessNormalizedTwistLocal.sign,badFive,badSeven]
  ring

#print axioms fourPrimeMonomial_sign
#print axioms word_leading_signed_laurent
#print axioms fullTaylorCoefficient_signed_laurent
#print axioms root_signed_10
#print axioms root_signed_14
#print axioms root_signed_70
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
