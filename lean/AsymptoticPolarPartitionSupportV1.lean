module

public import AsymptoticPartitionSupportV1
public import AsymptoticPolarBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPartitionSupport

open AsymptoticRegularTrace AsymptoticFunctionalCalculus AsymptoticPolarIsometry
open AsymptoticObservation ContinuousLinearMap
open scoped lp

variable {ι κ : Type*}

theorem supported_absolute (partition : ι → κ) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Supported partition T) : Supported partition (absolute T) := by
  rw [absolute_eq_positiveRoot]
  exact supported_positiveRoot partition _
    (supported_comp partition _ _ (supported_adjoint partition T hT) hT)
    (nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self T))

theorem supported_penaltyRoot (partition : ι → κ) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Supported partition T) : Supported partition (penaltyRoot T) := by
  rw [penaltyRoot_eq_positiveRoot]
  exact supported_positiveRoot partition _ (supported_absolute partition T hT) (absolute_nonneg T)

theorem supported_resolvent (partition : ι → κ) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Supported partition T) (n : ℕ) : Supported partition (AsymptoticPolarIsometry.resolvent T n) := by
  let L := (((n+1:ℕ):ℂ) • penaltyRoot T)
  have hL : Supported partition L := supported_smul partition _ (supported_penaltyRoot partition T hT) _
  change Supported partition (operator (1 : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) L (fun _ => le_rfl))
  rw [operator_identity_inverse L ‖normal 1 L‖ le_rfl]
  apply supported_inverse partition _ _ _ le_rfl (normal_coercive 1 L (fun _ => le_rfl))
  rw [normal_identity]
  exact supported_add partition _ _ (supported_one partition) (supported_comp partition _ _ (supported_adjoint partition L hL) hL)

/-- Polar decomposition preserves a coordinate partition, including
partitions of a coset space by a larger subgroup. -/
theorem supported_polar (partition : ι → κ) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Supported partition T) : Supported partition (polar T) := by
  apply supported_strong_limit partition (regularizedPolar T) (polar T) _ (regularizedPolar_strong_limit T)
  intro n
  exact supported_smul partition _ (supported_comp partition _ _ hT (supported_resolvent partition T hT n)) _

theorem supported_kernelComplement (partition : ι → κ) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Supported partition T) : Supported partition T.kerᗮ.starProjection := by
  rw [← polar_gram]
  exact supported_comp partition _ _ (supported_adjoint partition _ (supported_polar partition T hT)) (supported_polar partition T hT)

theorem supported_kernel (partition : ι → κ) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Supported partition T) : Supported partition T.ker.starProjection := by
  have he : T.ker.starProjection=1-T.kerᗮ.starProjection := by
    rw [Submodule.starProjection_orthogonal,one_def,sub_sub_cancel]
  rw [he]
  exact supported_sub partition _ _ (supported_one partition) (supported_kernelComplement partition T hT)

theorem supported_outputProjection (partition : ι → κ) (T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))
    (hT : Supported partition T) : Supported partition (outputSpace T).starProjection := by
  rw [← polar_cogram]
  exact supported_comp partition _ _ (supported_polar partition T hT) (supported_adjoint partition _ (supported_polar partition T hT))

#print axioms supported_absolute
#print axioms supported_penaltyRoot
#print axioms supported_resolvent
#print axioms supported_polar
#print axioms supported_kernelComplement
#print axioms supported_kernel
#print axioms supported_outputProjection

end AsymptoticPartitionSupport
