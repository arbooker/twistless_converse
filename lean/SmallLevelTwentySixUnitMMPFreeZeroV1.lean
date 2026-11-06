module
public import SmallLevelTwentySixUnitMMPResidualBundleV4
public import SmallLevelTwentySixContinuationMinorMMPV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 6000
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMP
open Complex SmallLevelTwentySixContinuationMinorMMP

theorem free_zero (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (hm : minor X Y Z a≠0) : v 520=0 ∧ v 540=0 := by
  let A : ℂ:=((1)/(X^2*Z)) + ((1*Y*a)/(X^2*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + (((-1)*Y^4)/(X^2*Z)) + ((1*Y^2)/(X*Z)) + ((1*Y^3*a)/(X*Z)) + ((1*Y^4)/(X*Z)) + ((1)/(Z)) + (((-1)*X)/(Z))
  let B : ℂ:=(((-1))/(X^2*Y^2)) + (((-1))/(X^2)) + ((1*a^2)/(X^2)) + ((1*Y*a)/(X^2)) + (((-1))/(X*Y^2)) + (((-1)*a)/(X*Y)) + (((-1))/(X))
  let C : ℂ:=(((-1))/(X^2*Z)) + (((-1)*Y*a)/(X^2*Z)) + (((-2)*Y^2)/(X^2*Z)) + ((1*Y^3*a)/(X^2*Z)) + ((3*Y^4)/(X^2*Z)) + (((-1))/(X*Z)) + (((-1)*Y*a)/(X*Z)) + (((-1)*Y^2)/(X*Z)) + (((-2)*Y^4)/(X*Z)) + (((-4))/(Z)) + ((-1)) + (((-2)*Y*a)/(Z)) + ((1*Y^2)/(Z)) + (((-1)*Y^3*a)/(Z)) + (((-1)*Y^4)/(Z)) + (((-2)*X)/(Z)) + ((1*X*Y*a)/(Z)) + (((-1)*X*Y^2)/(Z))
  let D : ℂ:=((1)/(X^2*Y^2)) + ((3)/(X^2)) + (((-1)*a^2)/(X^2)) + (((-3)*Y*a)/(X^2)) + ((2)/(X*Y^2)) + ((1*a)/(X*Y)) + ((4)/(X)) + (((-1)*a^2)/(X)) + (((-1)*Y*a)/(X)) + ((4)/(Y^2)) + (2) + ((2*X)/(Y^2)) + ((2*X^2)/(Y^2))
  have h0:=residual_0 X Y Z W a b hX hY hZ hW v hv
  have h1:=residual_10 X Y Z W a b hX hY hZ hW v hv
  change A*v 520+B*v 540=0 at h0
  change C*v 520+D*v 540=0 at h1
  have hd : A*D-B*C≠0 := by
    intro hz
    have he:=minor_determinant X Y Z W a b hX hY hZ hW
    change minor X Y Z a=X^2*Y^2*Z*(A*D-B*C) at he
    rw [hz,mul_zero] at he
    exact hm he
  constructor
  · apply (mul_eq_zero.mp (show (A*D-B*C)*v 520=0 by
      linear_combination D*h0-B*h1)).resolve_left hd
  · apply (mul_eq_zero.mp (show (A*D-B*C)*v 540=0 by
      linear_combination A*h1-C*h0)).resolve_left hd

#print axioms free_zero

end SmallLevelTwentySixUnitMMP
