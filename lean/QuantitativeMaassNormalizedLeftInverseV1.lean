module

public import QuantitativeHolomorphicGramV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

open ContinuousLinearMap

namespace QuantitativeMaass

variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A terminal left inverse of raw reconstruction gives a bounded left
inverse after the exact Gram normalization. -/
def normalizedTerminalLeftInverse (R : G →L[ℂ] H) (T : H →L[ℂ] G) : H →L[ℂ] G :=
  ((R.adjoint.comp R).comp (QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R))).comp T

theorem normalizedTerminalLeftInverse_apply (R : G →L[ℂ] H) (T : H →L[ℂ] G)
    (hT : ∀ v,T (R v)=v) {κ : ℝ} (hκ : 0<κ)
    (hR : ∀ v,κ*‖v‖^2≤‖R v‖^2) (v : G) :
    normalizedTerminalLeftInverse R T (QuantitativeHolomorphic.normalizedReconstruction R v)=v := by
  have hinj : Function.Injective (QuantitativeHolomorphic.normalizedReconstruction R) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [←QuantitativeHolomorphic.normalizedReconstruction_norm R hκ hR (a-b),
      map_sub,hab,sub_self,norm_zero]
  apply hinj
  change QuantitativeHolomorphic.normalizedReconstruction R
    ((R.adjoint.comp R) (QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R)
      (T (R (QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R) v)))))=_
  rw [hT]
  exact QuantitativeHolomorphic.normalizedReconstruction_reconstruct R hκ hR
    (QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R) v)

/-- Applying the terminal left inverse preserves a scalar eigenrelation
on every vector in the normalized reconstruction range. -/
theorem normalizedTerminalLeftInverse_eigen (R : G →L[ℂ] H) (T : H →L[ℂ] G)
    (hT : ∀ v,T (R v)=v) {κ : ℝ} (hκ : 0<κ)
    (hR : ∀ v,κ*‖v‖^2≤‖R v‖^2) (B : H →L[ℂ] H) (a : ℂ) (v : G)
    (hv : B (QuantitativeHolomorphic.normalizedReconstruction R v)=
      a • QuantitativeHolomorphic.normalizedReconstruction R v) :
    normalizedTerminalLeftInverse R T
      (B (QuantitativeHolomorphic.normalizedReconstruction R v))=a • v := by
  rw [hv,map_smul,normalizedTerminalLeftInverse_apply R T hT hκ hR]

#print axioms normalizedTerminalLeftInverse_apply
#print axioms normalizedTerminalLeftInverse_eigen

end QuantitativeMaass
