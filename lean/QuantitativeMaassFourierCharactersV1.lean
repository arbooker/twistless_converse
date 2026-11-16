module

public import QuantitativeMaassEulerPhaseV1
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

def eulerCharacter (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*(k:ℝ)*x:ℝ):ℂ)*Complex.I)

theorem eulerCharacter_continuous (k : ℤ) : Continuous (eulerCharacter k) := by
  unfold eulerCharacter
  fun_prop

theorem eulerCharacter_norm (k : ℤ) (x : ℝ) : ‖eulerCharacter k x‖=1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem eulerCharacter_mul (k l : ℤ) (x : ℝ) :
    eulerCharacter k x*eulerCharacter l x=eulerCharacter (k+l) x := by
  unfold eulerCharacter
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eulerCharacter_integral (k : ℤ) :
    (∫ x in Ioc (0:ℝ) 1,eulerCharacter k x)=if k=0 then 1 else 0 := by
  by_cases hk : k=0
  · subst k
    simp [eulerCharacter]
  · rw [ite_eq_right hk,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    have hc : (k:ℂ)*(2*Real.pi*Complex.I)≠0 := by
      exact mul_ne_zero (by exact_mod_cast hk)
        (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    have he : eulerCharacter k=(fun x : ℝ => ((k:ℂ)*(2*Real.pi*Complex.I)*x).exp) := by
      funext x
      unfold eulerCharacter
      congr 1
      push_cast
      ring
    rw [he,integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one,mul_one,Complex.ofReal_zero,mul_zero,Complex.exp_zero]
    rw [Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow,sub_self,zero_div]

theorem eulerParityPhase_characters (σ n : ℕ) (x : ℝ) :
    eulerParityPhase σ n x=eulerCharacter (n:ℤ) x+(-1:ℂ)^σ*eulerCharacter (-(n:ℤ)) x := by
  unfold eulerParityPhase eulerCharacter
  push_cast
  congr 2
  ring

theorem eulerParityPhase_character_integral (σ n m : ℕ) (hn : 0<n) (hm : 0<m) :
    (∫ x in Ioc (0:ℝ) 1,eulerCharacter (-(m:ℤ)) x*eulerParityPhase σ n x)=
      if n=m then 1 else 0 := by
  have he : (fun x => eulerCharacter (-(m:ℤ)) x*eulerParityPhase σ n x)=
      fun x => eulerCharacter (-(m:ℤ)+(n:ℤ)) x+(-1:ℂ)^σ*eulerCharacter (-(m:ℤ)+ -(n:ℤ)) x := by
    funext x
    rw [eulerParityPhase_characters,mul_add]
    rw [eulerCharacter_mul,show eulerCharacter (-(m:ℤ)) x*((-1:ℂ)^σ*eulerCharacter (-(n:ℤ)) x)=
      (-1:ℂ)^σ*(eulerCharacter (-(m:ℤ)) x*eulerCharacter (-(n:ℤ)) x) by ring,eulerCharacter_mul]
  rw [he,integral_add
    ((eulerCharacter_continuous _).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (((eulerCharacter_continuous _).const_mul _).integrableOn_Icc.mono_set Ioc_subset_Icc_self),integral_const_mul,
    eulerCharacter_integral,eulerCharacter_integral]
  have hneg : -(m:ℤ)+ -(n:ℤ)≠0 := by omega
  rw [ite_eq_right hneg,mul_zero,add_zero]
  have hi : (-(m:ℤ)+(n:ℤ)=0) ↔ n=m := by omega
  simp only [hi]

#print axioms eulerCharacter_continuous
#print axioms eulerCharacter_norm
#print axioms eulerCharacter_mul
#print axioms eulerCharacter_integral
#print axioms eulerParityPhase_characters
#print axioms eulerParityPhase_character_integral

end QuantitativeMaass
