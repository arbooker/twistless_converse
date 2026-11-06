module

public import QuantitativeArithmeticSmallLevelThirtyFivePoleWordRowsV1
public import QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanTheoryV4
public import QuantitativeArithmeticAnalyticGermTheoryV4

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Matrix SmallLevelTaylor
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

def frickeFifthRow : ClosedWordRow where
  word := .generator 4
  source := 42
  target := -30
  nonaffine := by norm_num [integerRaw,integerSeed]
  denominator := by norm_num [integerDen,integerRaw,integerSeed]
  closed := by norm_num [integerDen,integerNumer,integerRaw,integerSeed]

theorem primeParameter_ne_zero (p m : ℕ) (hp : p≠0) (s : ℂ) : primeParameter p m s≠0 :=
  cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))

theorem primeParameter_analytic (p m : ℕ) (hp : p≠0) (s : ℂ) :
    AnalyticAt ℂ (primeParameter p m) s := by
  unfold primeParameter
  have hpc : (p:ℂ)≠0 := by exact_mod_cast hp
  simp_rw [Complex.cpow_def_of_ne_zero hpc]
  fun_prop

theorem frickeFifth_coefficient (m n : ℕ) (s : ℂ) :
    rationalWordCoefficient m (-1) (.generator 4) 42 n s=
      -(primeParameter 7 m s/primeParameter 5 m s)*(I*7)^n*
        Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  have hr : rationalRate (.generator 4) 42=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,integerRaw,integerSeed,Matrix.det_fin_two]
  have hd : rationalDerivative (.generator 4) 42=7 := by
    norm_num [rationalDerivative,integerDen,integerRaw,integerSeed,Matrix.det_fin_two]
  rw [rationalWordCoefficient,hd,rational_four_prime_power _ (0,0,-1,1) hr]
  norm_num [frickeCount,fourPrimeMonomial,primeParameter,zpow_neg,div_eq_mul_inv]
  ring_nf
  simp

theorem seven_coefficient {m : ℕ} {f : ℕ → ℂ} {ε : ℂ}
    (hphase : ε*I^(2*m)= -1) (h7 : badSeven f= -1) (n : ℕ) (s : ℂ) :
    fullTaylorCoefficient (2*m) f ε 7 (-30) n s=
      -primeParameter 5 m s*(I*(-35))^n*
        Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  have hex : s-((2*m:ℕ):ℂ)/2=s-(m:ℂ) := by push_cast; ring
  simp only [fullTaylorCoefficient,taylorRowScalar,root_seven,h7,neg_neg,one_mul,hphase,hex]
  norm_num [primeParameter]
  ring_nf
  simp

def sevenTargetSum (v : Fin 210 → ℂ) : ℂ :=
  v 36+v 66+v 96+v 126+v 156+v 186

theorem sampleSeven_zero (v : Fin 210 → ℂ) :
    sampleSum 7 0 v=v 30+v 60+v 90+v 120+v 150+v 180 := by
  norm_num [sampleSum,FinitenessRamanujanSum.residues,Finset.sum_filter,
    Finset.sum_range_succ,gridIndex]

theorem sampleSeven_source (v : Fin 210 → ℂ) :
    sampleSum 7 (-30) v=v 0+v 30+v 60+v 90+v 120+v 150 := by
  norm_num [sampleSum,FinitenessRamanujanSum.residues,Finset.sum_filter,
    Finset.sum_range_succ,gridIndex]

theorem sampleSeven_target (v : Fin 210 → ℂ) : sampleSum 7 6 v=sevenTargetSum v := by
  norm_num [sampleSum,FinitenessRamanujanSum.residues,Finset.sum_filter,
    Finset.sum_range_succ,gridIndex,sevenTargetSum]

theorem completeSeven_six (v : Fin 210 → ℂ) : completeSum 7 6 v=v 6+sevenTargetSum v := by
  norm_num [completeSum,Finset.sum_range_succ,gridIndex,sevenTargetSum]
  ring

theorem seven_hecke_row {m : ℕ} {f : ℕ → ℂ} (h7 : badSeven f= -1)
    (s : ℂ) (v : Fin 210 → ℂ) : fullHeckeRow m f 7 6 s v=
      v 6+sevenTargetSum v+(primeParameter 7 m s)⁻¹*v 42 := by
  have hp : (7:ℂ)^((m:ℂ)-s)=(primeParameter 7 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  change (Real.sqrt 7:ℂ)*f 7= -1 at h7
  simp only [fullHeckeRow,completeSeven_six]
  norm_num [gridIndex]
  rw [h7,hp]
  ring

#print axioms frickeFifth_coefficient
#print axioms seven_coefficient
#print axioms seven_hecke_row
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
