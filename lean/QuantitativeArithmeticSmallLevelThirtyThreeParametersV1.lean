module
public import QuantitativeArithmeticSmallLevelThirtyThreeGridRamanujanV1
public import SmallLevelFourPrimeRatesV1
public import SmallLevelRamifiedPrimeAdditiveV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex FinitenessNormalizedTwistProduct SmallLevelPrimeRates

def badParameter (f : ℕ→ℂ) (p : ℕ) : ℂ := (Real.sqrt p:ℂ)*f p
def phase (m : ℕ) (ε : ℂ) : ℂ := ε*I^(2*m)

theorem root_three (f : ℕ→ℂ) : root 33 f 3= -badParameter f 3 := by
  norm_num [root,FinitenessNormalizedTwistLocal.sign,badParameter]
  ring

theorem root_eleven (f : ℕ→ℂ) : root 33 f 11= -badParameter f 11 := by
  norm_num [root,FinitenessNormalizedTwistLocal.sign,badParameter]
  ring

theorem badParameter_three_sign {f : ℕ→ℂ} (hf : FinitenessOriginalInput.EulerData 33 f) :
    badParameter f 3=1 ∨ badParameter f 3= -1 := by
  have h:=root_unit hf 3
  rw [root_three] at h
  rcases h with h|h
  · right; linear_combination -h
  · left; linear_combination -h

theorem badParameter_eleven_sign {f : ℕ→ℂ} (hf : FinitenessOriginalInput.EulerData 33 f) :
    badParameter f 11=1 ∨ badParameter f 11= -1 := by
  have h:=root_unit hf 11
  rw [root_eleven] at h
  rcases h with h|h
  · right; linear_combination -h
  · left; linear_combination -h

theorem grid_ramanujan_root (f : ℕ→ℂ) (i : Fin 72) :
    root 33 f (gridTaylorQ i)=
      (if 3∣gridTaylorQ i then -badParameter f 3 else 1)*
      (if 11∣gridTaylorQ i then -badParameter f 11 else 1) := by
  have hp6 : Nat.primeFactors 6=({2,3}:Finset ℕ) := by
    rw [show (6:ℕ)=2*3 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have hp22 : Nat.primeFactors 22=({2,11}:Finset ℕ) := by
    rw [show (22:ℕ)=2*11 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have hp33 : Nat.primeFactors 33=({3,11}:Finset ℕ) := by
    rw [show (33:ℕ)=3*11 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have hp66 : Nat.primeFactors 66=({2,3,11}:Finset ℕ) := by
    rw [show (66:ℕ)=2*33 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [hp33]
    all_goals decide
  fin_cases i <;>
    norm_num [gridTaylorQ,gridTaylorSpecs,root,FinitenessNormalizedTwistLocal.sign,badParameter,
      Nat.factorization_eq_zero_iff,hp6,hp22,hp33,hp66] <;> ring

theorem ramified_scalar (m : ℕ) (f : ℕ→ℂ) {p : ℕ} (hp : p≠0) (s : ℂ) :
    SmallLevelRamifiedPrimeAdditive.heckeScalar m f p s=
      badParameter f p/parameter p m s := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp
  have hc : (p:ℂ)^((m:ℂ)-s)=(p:ℂ)^m*(p:ℂ)^(-s) := by
    rw [sub_eq_add_neg,Complex.cpow_add _ _ hp0,Complex.cpow_natCast]
  calc
    SmallLevelRamifiedPrimeAdditive.heckeScalar m f p s=
        badParameter f p*(p:ℂ)^((m:ℂ)-s) := by
      rw [hc]
      unfold SmallLevelRamifiedPrimeAdditive.heckeScalar
        QuantitativeArithmeticRamifiedFullTrace.multiplier badParameter
      ring
    _=badParameter f p/parameter p m s := by
      rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
      rfl

#print axioms grid_ramanujan_root
#print axioms badParameter_three_sign
#print axioms badParameter_eleven_sign
#print axioms ramified_scalar
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
