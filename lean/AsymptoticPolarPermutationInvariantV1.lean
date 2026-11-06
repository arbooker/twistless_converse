module

public import AsymptoticPermutationInvariantV1
public import AsymptoticPolarBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPermutationInvariant

open AsymptoticRegularTrace AsymptoticFunctionalCalculus AsymptoticPolarIsometry
open AsymptoticObservation ContinuousLinearMap
open scoped lp

variable {ι : Type*}

theorem invariant_absolute (e : ι ≃ ι) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Invariant e T) : Invariant e (absolute T) := by
  rw [absolute_eq_positiveRoot]
  exact invariant_positiveRoot e _
    (invariant_comp e _ _ (invariant_adjoint e T hT) hT)
    (nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self T))

theorem invariant_penaltyRoot (e : ι ≃ ι) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Invariant e T) : Invariant e (penaltyRoot T) := by
  rw [penaltyRoot_eq_positiveRoot]
  exact invariant_positiveRoot e _ (invariant_absolute e T hT) (absolute_nonneg T)

theorem invariant_resolvent (e : ι ≃ ι) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Invariant e T) (n : ℕ) : Invariant e (AsymptoticPolarIsometry.resolvent T n) := by
  let L := (((n+1:ℕ):ℂ) • penaltyRoot T)
  have hL : Invariant e L := invariant_smul e _ (invariant_penaltyRoot e T hT) _
  change Invariant e (operator (1 : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) L (fun _ => le_rfl))
  rw [operator_identity_inverse L ‖normal 1 L‖ le_rfl]
  apply invariant_inverse e _ _ _ le_rfl (normal_coercive 1 L (fun _ => le_rfl))
  rw [normal_identity]
  exact invariant_add e _ _ (invariant_one e) (invariant_comp e _ _ (invariant_adjoint e L hL) hL)

/-- Polar decomposition preserves a simultaneous permutation symmetry
of the matrix coordinates. -/
theorem invariant_polar (e : ι ≃ ι) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Invariant e T) : Invariant e (polar T) := by
  apply invariant_strong_limit e (regularizedPolar T) (polar T) _ (regularizedPolar_strong_limit T)
  intro n
  exact invariant_smul e _ (invariant_comp e _ _ hT (invariant_resolvent e T hT n)) _

theorem invariant_kernelComplement (e : ι ≃ ι) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Invariant e T) : Invariant e T.kerᗮ.starProjection := by
  rw [← polar_gram]
  exact invariant_comp e _ _ (invariant_adjoint e _ (invariant_polar e T hT)) (invariant_polar e T hT)

theorem invariant_kernel (e : ι ≃ ι) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Invariant e T) : Invariant e T.ker.starProjection := by
  have he : T.ker.starProjection=1-T.kerᗮ.starProjection := by
    rw [Submodule.starProjection_orthogonal,one_def,sub_sub_cancel]
  rw [he]
  exact invariant_sub e _ _ (invariant_one e) (invariant_kernelComplement e T hT)

theorem invariant_outputProjection (e : ι ≃ ι) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Invariant e T) : Invariant e (outputSpace T).starProjection := by
  rw [← polar_cogram]
  exact invariant_comp e _ _ (invariant_polar e T hT) (invariant_adjoint e _ (invariant_polar e T hT))

#print axioms invariant_absolute
#print axioms invariant_penaltyRoot
#print axioms invariant_resolvent
#print axioms invariant_polar
#print axioms invariant_kernelComplement
#print axioms invariant_kernel
#print axioms invariant_outputProjection

end AsymptoticPermutationInvariant
