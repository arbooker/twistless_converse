module
public import QuantitativeArithmeticSmallLevelThirtyFivePoleFullRowsV1
public import QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex SmallLevelTaylor FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic

theorem root_three (f : ℕ → ℂ) : root 35 f 3=1 := by
  have hp : (3:ℕ).primeFactors={3} := (by decide : Nat.Prime 3).primeFactors
  have hv : (3:ℕ).factorization 3=1 := (by decide : Nat.Prime 3).factorization_self
  norm_num [root,hp,hv,FinitenessNormalizedTwistLocal.sign]

theorem fullTaylorCoefficient_negative_laurent (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (hphase : ε*I^(2*m)= -1) (q : ℕ) (hroot : root 35 f q=1)
    (t : ℤ) (e : ℤ×ℤ×ℤ×ℤ)
    (hr : (Nat.lcm 35 (q^2):ℚ)*((t:ℚ)/210)^2=
      (2:ℚ)^e.1*(3:ℚ)^e.2.1*(5:ℚ)^e.2.2.1*(7:ℚ)^e.2.2.2) (s : ℂ) :
    fullTaylorCoefficient (2*m) f ε q t 0 s=
      -fourPrimeMonomial e (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) := by
  have hex : s-((2*m:ℕ):ℂ)/2=s-(m:ℂ) := by push_cast; ring
  have hc : (((Nat.lcm 35 (q^2):ℝ)*((t:ℝ)/210)^2:ℝ):ℂ)=
      (((Nat.lcm 35 (q^2):ℚ)*((t:ℚ)/210)^2:ℚ):ℂ) := by push_cast; rfl
  simp only [fullTaylorCoefficient,taylorRowScalar,hroot,one_mul,hphase,
    pow_zero,Ring.choose_zero_right,mul_one,hex,hc]
  rw [rational_four_prime_power _ e hr]
  simp only [neg_one_mul,primeParameter,Nat.cast_ofNat]

#print axioms fullTaylorCoefficient_negative_laurent
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
