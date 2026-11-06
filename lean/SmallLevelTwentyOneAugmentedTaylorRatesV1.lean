module

public import SmallLevelTwentyOneAugmentedRatesV1
public import SmallLevelTwentyOneAugmentedArithmeticDataV1

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex SmallLevelTwentyOne

def augmentedTaylorPowers : Fin 72 → ℤ×ℤ×ℤ :=
  ![(-2,-1,-1), (-2,-1,-1), (0,-1,-1), (0,-1,-1), (-2,1,-1), (-2,1,-1), (2,-1,-1), (2,-1,-1), (0,1,-1), (0,1,-1), (-2,-1,1), (-2,-1,1), (2,1,-1), (2,1,-1), (0,-1,1), (0,-1,1), (-2,1,1), (-2,1,1), (2,-1,1), (2,-1,1), (0,1,1), (0,1,1), (2,1,1), (2,1,1), (0,-1,-1), (0,-1,-1), (0,1,-1), (0,1,-1), (0,-1,1), (0,-1,1), (0,1,1), (0,1,1), (-2,0,-1), (-2,0,-1), (0,0,-1), (0,0,-1), (2,0,-1), (2,0,-1), (-2,0,1), (-2,0,1), (0,0,1), (0,0,1), (2,0,1), (2,0,1), (0,0,-1), (0,0,-1), (0,0,1), (0,0,1), (-2,-1,0), (-2,-1,0), (0,-1,0), (0,-1,0), (-2,1,0), (-2,1,0), (2,-1,0), (2,-1,0), (0,1,0), (0,1,0), (2,1,0), (2,1,0), (0,-1,0), (0,-1,0), (0,1,0), (0,1,0), (-2,0,0), (-2,0,0), (0,0,0), (0,0,0), (2,0,0), (2,0,0), (0,0,0), (0,0,0)]

theorem augmentedTaylor_rate_certificate (i : Fin 72) :
    ramanujanRate (augmentedTaylorSpecs i).1 (augmentedTaylorSpecs i).2.1=
      (2:ℚ)^(augmentedTaylorPowers i).1*(3:ℚ)^(augmentedTaylorPowers i).2.1*
        (7:ℚ)^(augmentedTaylorPowers i).2.2 := by
  fin_cases i <;> norm_num [ramanujanRate,augmentedTaylorSpecs,augmentedTaylorPowers]

theorem fullTaylor_leading_laurent (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (i : Fin 72) :
    fullTaylorCoefficient (2*m) f ε (augmentedTaylorSpecs i).1 (augmentedTaylorSpecs i).2.1 0 s=
      phaseRoot m ε*localRoot (rootU f) (rootV f) (augmentedTaylorSpecs i).1*
        threePrimeMonomial (augmentedTaylorPowers i)
          (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s) := by
  rw [fullTaylorCoefficient_rational m f ε (augmentedTaylorSpecs_valid i).2.1]
  simp only [pow_zero,Ring.choose_zero_right,mul_one]
  rw [rational_three_prime_power _ _ (augmentedTaylor_rate_certificate i)]
  rfl

theorem fullTaylor_first_shift_factor (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (i : Fin 72) :
    fullTaylorCoefficient (2*m) f ε (augmentedTaylorSpecs i).1 (augmentedTaylorSpecs i).2.1 1 (s-1)=
      I*(s-((2*m:ℕ):ℂ))*
        fullTaylorCoefficient (2*m) f ε (augmentedTaylorSpecs i).1 (augmentedTaylorSpecs i).2.1 0 (s-1)*
          (ramanujanSlope (augmentedTaylorSpecs i).1 (augmentedTaylorSpecs i).2.1:ℂ) := by
  rw [fullTaylorCoefficient_rational m f ε (augmentedTaylorSpecs_valid i).2.1,
    fullTaylorCoefficient_rational m f ε (augmentedTaylorSpecs_valid i).2.1]
  simp only [pow_one,pow_zero,Ring.choose_one_right,Ring.choose_zero_right,mul_one,
    Nat.cast_one,Nat.cast_zero,add_zero]
  ring

theorem fullTaylor_first_shift_laurent (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (i : Fin 72) :
    fullTaylorCoefficient (2*m) f ε (augmentedTaylorSpecs i).1 (augmentedTaylorSpecs i).2.1 1 (s-1)=
      I*(s-((2*m:ℕ):ℂ))*phaseRoot m ε*
        localRoot (rootU f) (rootV f) (augmentedTaylorSpecs i).1*
        threePrimeMonomial (augmentedTaylorPowers i)
          (primeParameter 2 m s/2) (primeParameter 3 m s/3) (primeParameter 7 m s/7)*
          (ramanujanSlope (augmentedTaylorSpecs i).1 (augmentedTaylorSpecs i).2.1:ℂ) := by
  rw [fullTaylor_first_shift_factor,fullTaylor_leading_laurent,
    primeParameter_shift 2 m (by decide),primeParameter_shift 3 m (by decide),
    primeParameter_shift 7 m (by decide)]
  norm_num only [Nat.cast_ofNat]
  ring

#print axioms augmentedTaylor_rate_certificate
#print axioms fullTaylor_leading_laurent
#print axioms fullTaylor_first_shift_laurent
end SmallLevelTwentyOneKnownWords
