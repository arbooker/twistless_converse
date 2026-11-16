module

public import QuantitativeMaassScalarMetricPhysicalV1
public import AsymptoticOrbitDiagonalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane ContinuousLinearMap AsymptoticFiniteBranch
open AsymptoticRegularCompactBranch (Space)
namespace QuantitativeMaass

/-- The same scalar metric acts invertibly on every rational counting orbit. -/
def ScalarCylinderMetric.regularChange {N : ℕ} (M : ScalarCylinderMetric N) (z : ℍ) : Space≃L[ℂ]Space := by
  let f : AsymptoticRationalGroup.Group→ℂ := fun a => (M.weight (a • z):ℂ)
  let d : AsymptoticRationalGroup.Group→ℂ := fun a => ((M.weight (a • z))⁻¹:ℝ)
  have hp (a : AsymptoticRationalGroup.Group) : 0<M.weight (a • z) :=
    M.lower_pos.trans_le (M.bounds _).1
  have hd (a : AsymptoticRationalGroup.Group) : ‖d a‖≤M.lower⁻¹ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hp a))]
    exact inv_anti₀ M.lower_pos (M.bounds _).1
  let T := AsymptoticOrbitDiagonal.operator f M.branch.bound_nonneg (fun a => M.complex_bound (a • z))
  let S := AsymptoticOrbitDiagonal.operator d (inv_pos.mpr M.lower_pos).le hd
  exact { toLinearMap := T.toLinearMap
          invFun := S
          left_inv := by
            intro v
            apply lp.ext
            funext a
            change d a*(f a*v a)=v a
            dsimp only [d,f]
            rw [←mul_assoc,←Complex.ofReal_mul,inv_mul_cancel₀ (hp a).ne',Complex.ofReal_one,one_mul]
          right_inv := by
            intro v
            apply lp.ext
            funext a
            change f a*(d a*v a)=v a
            dsimp only [d,f]
            rw [←mul_assoc,←Complex.ofReal_mul,mul_inv_cancel₀ (hp a).ne',Complex.ofReal_one,one_mul]
          continuous_toFun := T.continuous
          continuous_invFun := S.continuous }

theorem ScalarCylinderMetric.regularChange_apply {N : ℕ} (M : ScalarCylinderMetric N) (z : ℍ)
    (v : Space) (a : AsymptoticRationalGroup.Group) :
    M.regularChange z v a=(M.weight (a • z):ℂ)*v a := rfl

theorem ScalarCylinderMetric.regularChange_inv_apply {N : ℕ} (M : ScalarCylinderMetric N) (z : ℍ)
    (v : Space) (a : AsymptoticRationalGroup.Group) :
    (M.regularChange z).symm v a=((M.weight (a • z))⁻¹:ℝ)*v a := rfl

theorem ScalarCylinderMetric.regularChange_norm {N : ℕ} (M : ScalarCylinderMetric N) (z : ℍ) :
    ‖(M.regularChange z).toContinuousLinearMap‖≤M.upper :=
  AsymptoticOrbitDiagonal.operator_norm_le _ M.branch.bound_nonneg (fun a => M.complex_bound (a • z))

theorem ScalarCylinderMetric.regularChange_inv_norm {N : ℕ} (M : ScalarCylinderMetric N) (z : ℍ) :
    ‖(M.regularChange z).symm.toContinuousLinearMap‖≤M.lower⁻¹ :=
  AsymptoticOrbitDiagonal.operator_norm_le _ (inv_pos.mpr M.lower_pos).le (fun a => by
    rw [Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (M.lower_pos.trans_le (M.bounds (a • z)).1))]
    exact inv_anti₀ M.lower_pos (M.bounds (a • z)).1)

theorem ScalarCylinderMetric.regularChange_branch {N : ℕ} (M : ScalarCylinderMetric N) (z : ℍ) :
    regularSum [M.branch] z=(M.regularChange z).toContinuousLinearMap := by
  ext1 v
  apply lp.ext
  funext a
  simp only [regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  change (M.weight (a • z):ℂ)*v (1*a)=(M.weight (a • z):ℂ)*v a
  rw [one_mul]

#print axioms ScalarCylinderMetric.regularChange
#print axioms ScalarCylinderMetric.regularChange_branch
#print axioms ScalarCylinderMetric.regularChange_norm
#print axioms ScalarCylinderMetric.regularChange_inv_norm
end QuantitativeMaass
