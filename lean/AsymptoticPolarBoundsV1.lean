module

public import AsymptoticPolarApproximationV1
public import AsymptoticFunctionalCalculusApproxV1
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPolarIsometry

open ContinuousLinearMap AsymptoticFunctionalCalculus

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem absolute_eq_positiveRoot (T : H →L[ℂ] J) :
    absolute T=positiveRoot (T.adjoint.comp T) := rfl

theorem penaltyRoot_eq_positiveRoot (T : H →L[ℂ] J) :
    penaltyRoot T=positiveRoot (absolute T) := rfl

theorem absolute_nonneg (T : H →L[ℂ] J) : 0≤absolute T := CFC.sqrt_nonneg _

theorem absolute_opNorm (T : H →L[ℂ] J) : ‖absolute T‖=‖T‖ := by
  apply le_antisymm
  · apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [← absolute_norm]
    exact T.le_opNorm x
  · apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [absolute_norm]
    exact (absolute T).le_opNorm x

theorem penaltyRoot_opNorm (T : H →L[ℂ] J) : ‖penaltyRoot T‖=Real.sqrt ‖T‖ := by
  rw [penaltyRoot,CFC.norm_sqrt (absolute T) (absolute_nonneg T),absolute_opNorm]

#print axioms absolute_eq_positiveRoot
#print axioms penaltyRoot_eq_positiveRoot
#print axioms absolute_nonneg
#print axioms absolute_opNorm
#print axioms penaltyRoot_opNorm

end AsymptoticPolarIsometry
