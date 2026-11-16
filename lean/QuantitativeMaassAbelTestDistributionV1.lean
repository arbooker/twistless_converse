module

public import QuantitativeMaassPositiveTestSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

local instance (N : ℕ) :
    ContinuousSMul ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  IsScalarTower.continuousSMul ℂ

local instance (N : ℕ) :
    LocallyConvexSpace ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  by
    convert! (NormedSpace.toLocallyConvexSpace' (E:=AutomorphicSpace N →L[ℂ] AutomorphicSpace N) ℂ) using 1

def compactAbelDistribution (N : ℕ) [NeZero N]
    (K : Compacts ℝ) (hK : (K:Set ℝ)⊆Ioi 0) :
    𝓓_{K}(ℝ,ℝ) →L[ℝ] (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  let I := positiveCompactInterval K hK
  (supportedAbelDistribution N I.left I.right I.left_pos I.right_nonneg).comp
    (ContDiffMapSupportedIn.monoCLM ℝ)

theorem compactAbelDistribution_apply (N : ℕ) [NeZero N]
    (K : Compacts ℝ) (hK : (K:Set ℝ)⊆Ioi 0) (φ : 𝓓_{K}(ℝ,ℝ)) :
    compactAbelDistribution N K hK φ=
      positiveTimeAbelOperator N (positiveSmoothTestToAbel (TestFunction.ofSupportedIn hK φ)) := by
  let I := positiveCompactInterval K hK
  change positiveTimeAbelOperator N
    (supportedPositiveTimeTest I.left I.right I.left_pos I.right_nonneg
      (ContDiffMapSupportedIn.monoCLM ℝ φ))=_
  symm
  apply positiveSmoothTestToAbel_congr
  intro t
  have hk : K≤positiveTimeCompact I.left I.right := I.subset
  have he : ((ContDiffMapSupportedIn.monoCLM ℝ φ : SupportedTimeTest I.left I.right):ℝ → ℝ)=φ := by
    rw [ContDiffMapSupportedIn.monoCLM_apply,ite_eq_left ⟨le_rfl,hk⟩]
  change (((ContDiffMapSupportedIn.monoCLM ℝ φ : SupportedTimeTest I.left I.right) t):ℂ)=(φ t:ℂ)
  rw [congrFun he t]

/-- The actual Abel test operator, now as a distribution on the whole
positive half-line with its canonical LF topology. Continuity is checked on
every compact support, using the proved first-derivative operator bound. -/
def abelTestDistribution (N : ℕ) [NeZero N] :
    PositiveSmoothTest →L[ℝ] (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  TestFunction.limitCLM ℝ
    (fun φ => positiveTimeAbelOperator N (positiveSmoothTestToAbel φ))
    (compactAbelDistribution N)
    (fun K hK φ => (compactAbelDistribution_apply N K hK φ).symm)

theorem abelTestDistribution_apply (N : ℕ) [NeZero N] (φ : PositiveSmoothTest) :
    abelTestDistribution N φ=positiveTimeAbelOperator N (positiveSmoothTestToAbel φ) := rfl

#print axioms compactAbelDistribution_apply
#print axioms abelTestDistribution
#print axioms abelTestDistribution_apply

end QuantitativeMaass
