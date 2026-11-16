module

public import QuantitativeMaassCuspidalQuotientWeightTailV1
public import QuantitativeMaassQuotientWeightGramV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson
open scoped InnerProductSpace

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

/-- The cylinder embedding's Gram is the actual orbit-weight operator on the
full automorphic space. The ambient inclusion introduces no extra projection. -/
theorem weightedQuotientEmbedding_gram_automorphic (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    (weightedQuotientEmbedding N hε hv).adjoint.comp (weightedQuotientEmbedding N hε hv)=
      quotientWeightAutomorphicMultiplier N hε hv := by
  rw [weightedQuotientEmbedding_gram]
  ext u : 1
  change (AutomorphicSpace N).subtypeL.adjoint (quotientWeightMultiplier N hε hv u.val)=
    quotientWeightAutomorphicMultiplier N hε hv u
  rw [←quotientWeightAutomorphicMultiplier_value,Submodule.adjoint_subtypeL]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _

/-- Restricting the literal cylinder embedding to cusp space gives precisely
the cuspidally projected weight as its Gram operator. The projection is retained. -/
theorem weightedQuotientEmbedding_cuspidal_gram (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) :
    ((weightedQuotientEmbedding N hε hv).comp (localCuspidalSpace N hN).subtypeL).adjoint.comp
      ((weightedQuotientEmbedding N hε hv).comp (localCuspidalSpace N hN).subtypeL)=
      (cuspidalQuotientWeight N hN hε hv).comp (localCuspidalSpace N hN).subtypeL := by
  have hg (u : AutomorphicSpace N) :
      (weightedQuotientEmbedding N hε hv).adjoint (weightedQuotientEmbedding N hε hv u)=
        quotientWeightAutomorphicMultiplier N hε hv u :=
    DFunLike.congr_fun (weightedQuotientEmbedding_gram_automorphic N hε hv) u
  rw [ContinuousLinearMap.adjoint_comp]
  ext u : 1
  change (localCuspidalSpace N hN).subtypeL.adjoint
      ((weightedQuotientEmbedding N hε hv).adjoint (weightedQuotientEmbedding N hε hv u.val))=
    (localCuspidalSpace N hN).orthogonalProjectionOnto (quotientWeightAutomorphicMultiplier N hε hv u.val)
  rw [hg,Submodule.adjoint_subtypeL]

#print axioms weightedQuotientEmbedding_gram_automorphic
#print axioms weightedQuotientEmbedding_cuspidal_gram

end QuantitativeMaass
