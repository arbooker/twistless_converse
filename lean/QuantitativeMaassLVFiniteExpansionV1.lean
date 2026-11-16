module

public import QuantitativeMaassMixedWordPolynomialV1
public import QuantitativeMaassLVUniformDeficitV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
namespace QuantitativeMaass.MixedExpansion

local instance (N : ℕ) : Ring (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.ring
local instance (N : ℕ) : Algebra ℝ (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.algebra

def difference (p : ℕ) : Expression := [⟨1,1,0⟩,⟨-2,0,Real.log p⟩]
def lvBase (p : ℕ) : Expression :=
  one++scale (-((lvBound p)^2)⁻¹) (mul (difference p) (difference p))
def lvExpression (p d : ℕ) : Expression := one++scale (-1) (power (lvBase p) d)

theorem bounded_mono {m n : ℕ} {R S : ℝ} {E : Expression}
    (hm : m≤n) (hR : R≤S) (hE : Bounded m R E) : Bounded n S E :=
  fun u hu => ⟨(hE u hu).1.trans hm,(hE u hu).2.trans hR⟩

theorem mass_difference (p : ℕ) : mass (difference p)=3 := by
  norm_num [difference,mass]
theorem bounded_difference (p : ℕ) : Bounded 1 |Real.log p| (difference p) := by
  intro u hu
  simp only [difference,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl|rfl
  · exact ⟨le_rfl,by simpa only [abs_zero] using abs_nonneg (Real.log p)⟩
  · exact ⟨Nat.zero_le _,le_rfl⟩
theorem mass_lvBase (p : ℕ) : mass (lvBase p)=1+9/((lvBound p)^2) := by
  simp only [lvBase,mass_append,mass_one,mass_scale,mass_mul,mass_difference,abs_neg,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (lvBound p)))]
  ring
theorem mass_lvBase_le (p : ℕ) [Fact p.Prime] : mass (lvBase p)≤2 := by
  rw [mass_lvBase]
  have hp := lvBound_gt_four p
  have hh : 9/((lvBound p)^2)≤1 := (div_le_one (sq_pos_of_pos (lvBound_pos p))).mpr (by nlinarith)
  linarith
theorem bounded_lvBase (p : ℕ) : Bounded 2 (2*|Real.log p|) (lvBase p) := by
  apply bounded_append
  · exact bounded_mono (by norm_num) (by positivity) bounded_one
  · apply bounded_scale
    have hh := bounded_mul (difference p) (difference p) (bounded_difference p) (bounded_difference p)
    simpa only [one_add_one_eq_two,two_mul] using hh

/-- The literal LV polynomial has a common finite expansion of mass at
most 2*2^d, Hecke length at most 2d, and time shift at most 2d log(p). -/
theorem lvExpression_bounds (p : ℕ) [Fact p.Prime] (d : ℕ) :
    mass (lvExpression p d)≤2*(2:ℝ)^d ∧
      Bounded (2*d) (2*(d:ℝ)*|Real.log p|) (lvExpression p d) := by
  constructor
  · rw [lvExpression,mass_append,mass_one,mass_scale,mass_power]
    norm_num only [abs_neg,abs_one,one_mul]
    have hh := pow_le_pow_left₀ (mass_nonneg (lvBase p)) (mass_lvBase_le p) d
    have hp : 1≤(2:ℝ)^d := one_le_pow₀ (by norm_num)
    linarith
  · apply bounded_append
    · exact bounded_mono (Nat.zero_le _) (by positivity) bounded_one
    · apply bounded_scale
      have hh := bounded_power (lvBase p) (bounded_lvBase p) d
      convert hh using 1
      ring

variable (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)

theorem eval_difference :
    eval N p hN hpN a b hab (difference p)=
      (lvDifference N p hN hpN a b hab,fun z : ℝ×ℝ => z.1-2*Real.cos (Real.log p*z.2)) := by
  apply Prod.ext
  · change (1:ℝ) • (Wave.shiftedQuotientWave N 0*(HeckeL2.operator N p hN hpN a b hab)^1)+
      ((-2:ℝ) • (Wave.shiftedQuotientWave N (Real.log p)*(HeckeL2.operator N p hN hpN a b hab)^0)+0)=_
    simp only [one_smul,pow_one,pow_zero,mul_one,Wave.shiftedQuotientWave_zero,add_zero,
      ContinuousLinearMap.mul_def,ContinuousLinearMap.id_comp,lvDifference,neg_smul,sub_eq_add_neg]
    rfl
  · funext z
    change 1*(z.1^1*Real.cos (0*z.2))+((-2)*(z.1^0*Real.cos (Real.log p*z.2))+0)=_
    simp only [pow_one,pow_zero,zero_mul,Real.cos_zero,one_mul,mul_one,add_zero]
    ring

/-- Operator and scalar evaluations use precisely the same coefficients,
word lengths and time shifts, with no independently chosen symbol. -/
theorem eval_lvExpression (d : ℕ) :
    eval N p hN hpN a b hab (lvExpression p d)=
      (actualLVFilter N p hN hpN a b hab d,
        fun z : ℝ×ℝ => 1-(1-(z.1-2*Real.cos (Real.log p*z.2))^2/(lvBound p)^2)^d) := by
  simp only [lvExpression,lvBase,eval_append,eval_one,eval_scale,eval_power,eval_mul,eval_difference]
  apply Prod.ext
  · change (1:AutomorphicSpace N→L[ℂ]AutomorphicSpace N)+(-1:ℝ) •
      (1+(-((lvBound p)^2)⁻¹) • (lvDifference N p hN hpN a b hab*lvDifference N p hN hpN a b hab))^d=_
    simp only [neg_smul,one_smul,←sub_eq_add_neg,←pow_two]
    rfl
  · funext z
    change 1+(-1)*(1+(-((lvBound p)^2)⁻¹)*
      ((z.1-2*Real.cos (Real.log p*z.2))*(z.1-2*Real.cos (Real.log p*z.2))))^d=_
    congr 1
    ring

#print axioms lvExpression_bounds
#print axioms eval_lvExpression
end QuantitativeMaass.MixedExpansion
