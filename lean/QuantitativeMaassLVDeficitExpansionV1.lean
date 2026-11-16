module

public import QuantitativeMaassLVFiniteExpansionV1
public import QuantitativeMaassLVDeficitOperatorV1
public import QuantitativeMaassLVGeometricLowerV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
namespace QuantitativeMaass.MixedExpansion
local instance (N : ℕ) : Ring (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.ring
local instance (N : ℕ) : Algebra ℝ (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.algebra

/-- The complementary LV polynomial uses the same finite coefficients,
Hecke lengths and cosine times as its actual quotient operator. -/
def deficitExpression (p d : ℕ) : Expression := power (lvBase p) d

theorem deficitExpression_bounds (p : ℕ) [Fact p.Prime] (d : ℕ) :
    mass (deficitExpression p d)≤2*(2:ℝ)^d ∧
      Bounded (2*d) (2*(d:ℝ)*|Real.log p|) (deficitExpression p d) := by
  constructor
  · rw [deficitExpression,mass_power]
    have h := pow_le_pow_left₀ (mass_nonneg (lvBase p)) (mass_lvBase_le p) d
    have hp : 0≤(2:ℝ)^d := by positivity
    linarith
  · have hh := bounded_power (lvBase p) (bounded_lvBase p) d
    unfold deficitExpression
    convert hh using 1
    ring

theorem eval_deficitExpression (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) :
    eval N p hN hpN a b hab (deficitExpression p d)=
      (actualLVDeficit N p hN hpN a b hab d,fun z : ℝ×ℝ => 1-lvScalarSymbol p d z) := by
  have hh : eval N p hN hpN a b hab (deficitExpression p d)=
      (1:HeckeWavePair N)-eval N p hN hpN a b hab (lvExpression p d) := by
    simp only [lvExpression,eval_append,eval_one,eval_scale,neg_smul,one_smul,
      ←sub_eq_add_neg,sub_sub_cancel]
    rfl
  rw [hh,eval_lvExpression]
  rfl

#print axioms deficitExpression_bounds
#print axioms eval_deficitExpression
end QuantitativeMaass.MixedExpansion
