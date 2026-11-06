module
public import SmallLevelTwentySixGridRamanujanV1
public import SmallLevelFourPrimeRatesV1
public import SmallLevelRamifiedPrimeAdditiveV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex FinitenessNormalizedTwistProduct SmallLevelPrimeRates

def badParameter (f : ℕ→ℂ) (p : ℕ) : ℂ := (Real.sqrt p:ℂ)*f p
def phase (m : ℕ) (ε : ℂ) : ℂ := ε*I^(2*m)

theorem root_two (f : ℕ→ℂ) : root 26 f 2= -badParameter f 2 := by
  norm_num [root,FinitenessNormalizedTwistLocal.sign,badParameter]
  ring

theorem root_thirteen (f : ℕ→ℂ) : root 26 f 13= -badParameter f 13 := by
  norm_num [root,FinitenessNormalizedTwistLocal.sign,badParameter]
  ring

theorem badParameter_two_sign {f : ℕ→ℂ} (hf : FinitenessOriginalInput.EulerData 26 f) :
    badParameter f 2=1 ∨ badParameter f 2= -1 := by
  have h:=root_unit hf 2
  rw [root_two] at h
  rcases h with h|h
  · right; linear_combination -h
  · left; linear_combination -h

theorem badParameter_thirteen_sign {f : ℕ→ℂ} (hf : FinitenessOriginalInput.EulerData 26 f) :
    badParameter f 13=1 ∨ badParameter f 13= -1 := by
  have h:=root_unit hf 13
  rw [root_thirteen] at h
  rcases h with h|h
  · right; linear_combination -h
  · left; linear_combination -h

theorem grid_ramanujan_root (f : ℕ→ℂ) (i : Fin 71) :
    root 26 f (gridTaylorQ i)=
      (if 2∣gridTaylorQ i then -badParameter f 2 else 1)*
      (if 13∣gridTaylorQ i then -badParameter f 13 else 1) := by
  have hp4 : Nat.primeFactors 4=({2}:Finset ℕ) := by
    rw [show (4:ℕ)=2*2 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have hp6 : Nat.primeFactors 6=({2,3}:Finset ℕ) := by
    rw [show (6:ℕ)=2*3 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have hp10 : Nat.primeFactors 10=({2,5}:Finset ℕ) := by
    rw [show (10:ℕ)=2*5 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have hp12 : Nat.primeFactors 12=({2,3}:Finset ℕ) := by
    rw [show (12:ℕ)=2*6 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [hp6]
  have hp26 : Nat.primeFactors 26=({2,13}:Finset ℕ) := by
    rw [show (26:ℕ)=2*13 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have hp39 : Nat.primeFactors 39=({3,13}:Finset ℕ) := by
    rw [show (39:ℕ)=3*13 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have hp52 : Nat.primeFactors 52=({2,13}:Finset ℕ) := by
    rw [show (52:ℕ)=2*26 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [hp26]
  have hp78 : Nat.primeFactors 78=({2,3,13}:Finset ℕ) := by
    rw [show (78:ℕ)=2*39 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [hp39]
    all_goals decide
  have hp156 : Nat.primeFactors 156=({2,3,13}:Finset ℕ) := by
    rw [show (156:ℕ)=2*78 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [hp78]
    all_goals decide
  fin_cases i <;>
    norm_num [gridTaylorQ,gridTaylorSpecs,root,FinitenessNormalizedTwistLocal.sign,badParameter,
      Nat.factorization_eq_zero_iff,hp4,hp6,hp10,hp12,hp26,hp39,hp52,hp78,hp156] <;> ring

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
#print axioms badParameter_two_sign
#print axioms badParameter_thirteen_sign
#print axioms ramified_scalar
end SmallLevelTwentySixGrid
