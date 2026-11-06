module

public import AsymptoticSubgroupOrthogonalityV1
public import AsymptoticStackPolarV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticSubgroupSupport

open AsymptoticRegularTrace AsymptoticFunctionalCalculus AsymptoticPolarIsometry
open AsymptoticObservation AsymptoticObservationStack ContinuousLinearMap InnerProductSpace
open scoped lp InnerProduct

variable {G ι : Type*} [Group G] [Fintype ι]

theorem supported_sum (S : Subgroup G) (B : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ i,Supported S (B i)) : Supported S (∑ i,B i) := by
  simpa only [tsum_fintype] using supported_tsum S B (hasSum_fintype B).summable hB

theorem supported_stackGram (S : Subgroup G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hL : ∀ i,Supported S (L i)) : Supported S ((stack L).adjoint.comp (stack L)) := by
  rw [stack_gram]
  exact supported_sum S _ (fun i => supported_comp S _ _ (supported_adjoint S _ (hL i)) (hL i))

theorem supported_stackAbsolute (S : Subgroup G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hL : ∀ i,Supported S (L i)) : Supported S (absolute (stack L)) := by
  rw [absolute_eq_positiveRoot]
  exact supported_positiveRoot S _ (supported_stackGram S L hL)
    (nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self (stack L)))

theorem supported_stackResolvent (S : Subgroup G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hL : ∀ i,Supported S (L i)) (n : ℕ) :
    Supported S (AsymptoticPolarIsometry.resolvent (stack L) n) := by
  have hr : Supported S (penaltyRoot (stack L)) := by
    rw [penaltyRoot_eq_positiveRoot]
    exact supported_positiveRoot S _ (supported_stackAbsolute S L hL) (absolute_nonneg (stack L))
  let K := (((n+1:ℕ):ℂ) • penaltyRoot (stack L))
  have hK : Supported S K := supported_smul S _ hr _
  change Supported S (operator (1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) K (fun _ => le_rfl))
  rw [operator_identity_inverse K ‖normal 1 K‖ le_rfl]
  apply supported_inverse S _ _ _ le_rfl (normal_coercive 1 K (fun _ => le_rfl))
  rw [normal_identity]
  exact supported_add S _ _ (supported_one S) (supported_comp S _ _ (supported_adjoint S K hK) hK)

/-- Every polar row of a stack retains the common subgroup support of
the original observation rows. -/
theorem supported_polarRow (S : Subgroup G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hL : ∀ i,Supported S (L i)) (i : ι) : Supported S (polarRow L i) := by
  apply supported_strong_limit S (fun n => regularizedRow L n i) _ _ (polarRow_strong_limit L i)
  intro n
  rw [regularizedRow_formula]
  exact supported_smul S _ (supported_comp S _ _ (hL i) (supported_stackResolvent S L hL n)) _

/-- The exact rooted identity used for fresh-prime mixing, now for the
constructed polar rows of the actual labelled stack. Coset separation
kills the off-diagonal terms and leaves its source support projection. -/
theorem polar_mixing_root (S : Subgroup G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hL : ∀ i,Supported S (L i)) (a : ι → ι → G)
    (hdiag : ∀ i,a i i=1) (hoff : ∀ i j,i≠j → a i j∉S) (h : G) :
    (∑ i,∑ j,⟪polarRow L i (delta h),translation (a i j) (polarRow L j (delta h))⟫_ℂ)=
      matrix (stack L).kerᗮ.starProjection h h := by
  rw [translated_root_energy S (polarRow L) (supported_polarRow S L hL) a hdiag hoff h]
  symm
  change matrixCLM h h (stack L).kerᗮ.starProjection=_
  rw [← polar_rows_gram,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [matrixCLM_apply,matrix_cross,inner_self_eq_norm_sq_to_K]
  exact (Complex.ofReal_pow _ _).symm

#print axioms supported_sum
#print axioms supported_stackGram
#print axioms supported_stackAbsolute
#print axioms supported_stackResolvent
#print axioms supported_polarRow
#print axioms polar_mixing_root

end AsymptoticSubgroupSupport
