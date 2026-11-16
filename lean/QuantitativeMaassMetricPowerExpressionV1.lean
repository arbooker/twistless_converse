module

public import QuantitativeMaassScaledMetricPowerV1
public import AsymptoticFiniteBranchPolynomialV1
public import QuantitativeHolomorphicExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticFiniteBranch QuantitativeHolomorphic ContinuousLinearMap
namespace QuantitativeMaass

/-- Common scale depending only on finite branch data, not on a chosen
physical or regular representation. -/
def expressionMetricScale (D : Expression) : ℝ := (expressionBound D^2+1)⁻¹

theorem expressionMetricScale_pos (D : Expression) : 0<expressionMetricScale D := by
  unfold expressionMetricScale
  positivity

theorem expressionMetricScale_bound (D : Expression) {u : ℝ} (hu : 0≤u)
    (hDu : u≤expressionBound D) : expressionMetricScale D*u^2≤1 := by
  have hh := pow_le_pow_left₀ hu hDu 2
  have he : expressionMetricScale D*(expressionBound D^2+1)=1 :=
    inv_mul_cancel₀ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hh (expressionMetricScale_pos D).le]

def metricPositiveExpression (D F : Expression) : Expression :=
  scaleExpression (expressionMetricScale D:ℂ)
    (composeExpression D (composeExpression F (adjointExpression D)))

def metricPowerExpression (D F : Expression) (m : ℕ) : Expression :=
  [AsymptoticFiniteBranch.identity]++scaleExpression (-1)
    (powerExpression ([AsymptoticFiniteBranch.identity]++scaleExpression (-1) (metricPositiveExpression D F)) m)

theorem metricPositiveExpression_physical (D F : Expression) :
    holomorphicSum (metricPositiveExpression D F) 0=
      expressionMetricScale D • (holomorphicSum D 0*holomorphicSum F 0*(holomorphicSum D 0).adjoint) := by
  rw [metricPositiveExpression,holomorphicSum_scale,holomorphicSum_compose,
    holomorphicSum_compose,holomorphicSum_adjoint]
  ext x : 1
  simp only [smul_apply,comp_apply,mul_apply_eq_comp]
  exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (expressionMetricScale D)
    (holomorphicSum D 0 (holomorphicSum F 0 ((holomorphicSum D 0).adjoint x)))).symm

theorem metricPositiveExpression_regular (D F : Expression) (z : UpperHalfPlane) :
    regularSum (metricPositiveExpression D F) z=
      expressionMetricScale D • (regularSum D z*regularSum F z*(regularSum D z).adjoint) := by
  rw [metricPositiveExpression,regularSum_scale,regularSum_compose,
    regularSum_compose,regularSum_adjoint]
  ext x : 1
  simp only [smul_apply,comp_apply,mul_apply_eq_comp]
  exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (expressionMetricScale D)
    (regularSum D z (regularSum F z ((regularSum D z).adjoint x)))).symm

theorem metricPowerExpression_physical (D F : Expression) (m : ℕ) :
    holomorphicSum (metricPowerExpression D F m) 0=
      scaledMetricPowerFilter (expressionMetricScale D) (holomorphicSum D 0) (holomorphicSum F 0) m := by
  unfold metricPowerExpression
  rw [holomorphicSum_append,holomorphicSum_scale,holomorphicSum_power,
    holomorphicSum_append,holomorphicSum_scale,metricPositiveExpression_physical]
  have hi : holomorphicSum [AsymptoticFiniteBranch.identity] 0=1 := by
    simp [holomorphicSum,holomorphic_identity]
  rw [hi]
  have hn (T : AsymptoticHyperbolicSlash.Space→L[ℂ]AsymptoticHyperbolicSlash.Space) :
      (-1:ℂ) • T= -T := by
    ext x : 1
    exact neg_one_smul ℂ (T x)
  simp only [hn,←sub_eq_add_neg,scaledMetricPowerFilter]

theorem metricPowerExpression_regular (D F : Expression) (m : ℕ) (z : UpperHalfPlane) :
    regularSum (metricPowerExpression D F m) z=
      scaledMetricPowerFilter (expressionMetricScale D) (regularSum D z) (regularSum F z) m := by
  unfold metricPowerExpression
  rw [regularSum_append,regularSum_scale,regularSum_power,
    regularSum_append,regularSum_scale,metricPositiveExpression_regular]
  have hi : regularSum [AsymptoticFiniteBranch.identity] z=1 := by
    simp [regularSum,regular_identity]
  rw [hi]
  have hn (T : RegularSpace→L[ℂ]RegularSpace) : (-1:ℂ) • T= -T := by
    ext x : 1
    exact neg_one_smul ℂ (T x)
  simp only [hn,←sub_eq_add_neg,scaledMetricPowerFilter]

theorem metricPowerExpression_physical_order (D F : Expression)
    (hF : 0≤holomorphicSum F 0) (hF1 : holomorphicSum F 0≤1) (m : ℕ) :
    0≤holomorphicSum (metricPowerExpression D F m) 0 ∧
      holomorphicSum (metricPowerExpression D F m) 0≤1 := by
  rw [metricPowerExpression_physical]
  exact scaledMetricPowerFilter_order _ _ hF hF1 (expressionMetricScale_pos D).le
    (expressionMetricScale_bound D (norm_nonneg _) (holomorphicSum_norm_le D 0)) m

theorem metricPowerExpression_regular_order (D F : Expression)
    (z : UpperHalfPlane) (hF : 0≤regularSum F z) (hF1 : regularSum F z≤1) (m : ℕ) :
    0≤regularSum (metricPowerExpression D F m) z ∧ regularSum (metricPowerExpression D F m) z≤1 := by
  rw [metricPowerExpression_regular]
  exact scaledMetricPowerFilter_order _ _ hF hF1 (expressionMetricScale_pos D).le
    (expressionMetricScale_bound D (norm_nonneg _) (regularSum_norm_le D z)) m

/-- Exact coefficient-mass bound for the same common polynomial. -/
theorem metricPowerExpression_mass (D F : Expression) (m : ℕ) :
    expressionBound (metricPowerExpression D F m)=
      1+(1+expressionMetricScale D*expressionBound D^2*expressionBound F)^m := by
  simp only [metricPowerExpression,metricPositiveExpression,expressionBound_append,
    expressionBound_scale,expressionBound_power,expressionBound_compose,expressionBound_adjoint]
  have hi : expressionBound [AsymptoticFiniteBranch.identity]=1 := by simp [expressionBound,identity]
  rw [hi]
  simp only [norm_neg,norm_one,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (expressionMetricScale_pos D)]
  congr 2
  ring

#print axioms expressionMetricScale_bound
#print axioms metricPowerExpression_physical
#print axioms metricPowerExpression_regular
#print axioms metricPowerExpression_physical_order
#print axioms metricPowerExpression_regular_order
#print axioms metricPowerExpression_mass
end QuantitativeMaass
