module

public import AsymptoticSubgroupSupportV1
public import AsymptoticPolarBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticSubgroupSupport

open AsymptoticRegularTrace AsymptoticFunctionalCalculus AsymptoticPolarIsometry
open AsymptoticObservation ContinuousLinearMap
open scoped lp

variable {G : Type*} [Group G]

theorem supported_absolute (S : Subgroup G) (T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hT : Supported S T) : Supported S (absolute T) := by
  rw [absolute_eq_positiveRoot]
  exact supported_positiveRoot S _
    (supported_comp S _ _ (supported_adjoint S T hT) hT)
    (nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self T))

theorem supported_penaltyRoot (S : Subgroup G) (T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hT : Supported S T) : Supported S (penaltyRoot T) := by
  rw [penaltyRoot_eq_positiveRoot]
  exact supported_positiveRoot S _ (supported_absolute S T hT) (absolute_nonneg T)

theorem supported_resolvent (S : Subgroup G) (T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hT : Supported S T) (n : ℕ) : Supported S (AsymptoticPolarIsometry.resolvent T n) := by
  let L := (((n+1:ℕ):ℂ) • penaltyRoot T)
  have hL : Supported S L := supported_smul S _ (supported_penaltyRoot S T hT) _
  change Supported S (operator (1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) L (fun _ => le_rfl))
  rw [operator_identity_inverse L ‖normal 1 L‖ le_rfl]
  apply supported_inverse S _ _ _ le_rfl (normal_coercive 1 L (fun _ => le_rfl))
  rw [normal_identity]
  exact supported_add S _ _ (supported_one S) (supported_comp S _ _ (supported_adjoint S L hL) hL)

/-- Polar decomposition preserves subgroup support, hence in particular
q-integrality once the rational q-integral subgroup has been identified. -/
theorem supported_polar (S : Subgroup G) (T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hT : Supported S T) : Supported S (polar T) := by
  apply supported_strong_limit S (regularizedPolar T) (polar T) _ (regularizedPolar_strong_limit T)
  intro n
  exact supported_smul S _ (supported_comp S _ _ hT (supported_resolvent S T hT n)) _

theorem supported_kernelComplement (S : Subgroup G) (T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hT : Supported S T) : Supported S T.kerᗮ.starProjection := by
  rw [← polar_gram]
  exact supported_comp S _ _ (supported_adjoint S _ (supported_polar S T hT)) (supported_polar S T hT)

theorem supported_kernel (S : Subgroup G) (T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hT : Supported S T) : Supported S T.ker.starProjection := by
  have he : T.ker.starProjection=1-T.kerᗮ.starProjection := by
    rw [Submodule.starProjection_orthogonal,one_def,sub_sub_cancel]
  rw [he]
  exact supported_sub S _ _ (supported_one S) (supported_kernelComplement S T hT)

theorem supported_outputProjection (S : Subgroup G) (T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hT : Supported S T) : Supported S (outputSpace T).starProjection := by
  rw [← polar_cogram]
  exact supported_comp S _ _ (supported_polar S T hT) (supported_adjoint S _ (supported_polar S T hT))

#print axioms supported_absolute
#print axioms supported_penaltyRoot
#print axioms supported_resolvent
#print axioms supported_polar
#print axioms supported_kernelComplement
#print axioms supported_kernel
#print axioms supported_outputProjection

end AsymptoticSubgroupSupport
