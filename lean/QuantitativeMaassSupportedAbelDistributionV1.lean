module

public import QuantitativeMaassSupportedTimeTestV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

local instance (N : ℕ) :
    ContinuousSMul ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  IsScalarTower.continuousSMul ℂ

private theorem map_zero_of_scaledSub {E G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup G] [Module ℝ G] (A : E → G)
    (h : ∀ (f g : E) (c : ℝ),A (c • f-g)=c • A f-A g) : A 0=0 := by
  simpa only [one_smul,sub_self] using h 0 0 1

private theorem map_smul_of_scaledSub {E G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup G] [Module ℝ G] (A : E → G)
    (h : ∀ (f g : E) (c : ℝ),A (c • f-g)=c • A f-A g) (c : ℝ) (f : E) : A (c • f)=c • A f := by
  simpa only [map_zero_of_scaledSub A h,sub_zero] using h f 0 c

private theorem map_add_of_scaledSub {E G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup G] [Module ℝ G] (A : E → G)
    (h : ∀ (f g : E) (c : ℝ),A (c • f-g)=c • A f-A g) (f g : E) : A (f+g)=A f+A g := by
  have hn : A (-g)= -A g := by
    simpa only [neg_one_smul] using map_smul_of_scaledSub A h (-1) g
  simpa only [one_smul,sub_neg_eq_add,hn] using h f (-g) 1

theorem supportedTimeAbelOperator_zero (N : ℕ) [NeZero N]
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) :
    supportedTimeAbelOperator N δ R hδ hR 0=0 :=
  map_zero_of_scaledSub (supportedTimeAbelOperator N δ R hδ hR) (supportedTimeAbelOperator_scaledSub N δ R hδ hR)

theorem supportedTimeAbelOperator_smul (N : ℕ) [NeZero N]
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) (c : ℝ) (φ : SupportedTimeTest δ R) :
    supportedTimeAbelOperator N δ R hδ hR (c • φ)=
      c • supportedTimeAbelOperator N δ R hδ hR φ :=
  map_smul_of_scaledSub (supportedTimeAbelOperator N δ R hδ hR) (supportedTimeAbelOperator_scaledSub N δ R hδ hR) c φ

theorem supportedTimeAbelOperator_add (N : ℕ) [NeZero N]
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) (φ ψ : SupportedTimeTest δ R) :
    supportedTimeAbelOperator N δ R hδ hR (φ+ψ)=
      supportedTimeAbelOperator N δ R hδ hR φ+supportedTimeAbelOperator N δ R hδ hR ψ :=
  map_add_of_scaledSub (supportedTimeAbelOperator N δ R hδ hR) (supportedTimeAbelOperator_scaledSub N δ R hδ hR) φ ψ

/-- The actual geometric Abel test map is a continuous real-linear map on
fixed-support smooth tests. Its continuity is proved by the first-derivative
seminorm estimate, so it can be used in distribution and smoothing arguments. -/
def supportedAbelDistribution (N : ℕ) [NeZero N]
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) :
    SupportedTimeTest δ R →L[ℝ] (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  ContDiffMapSupportedIn.mkCLMtoNormedSpace ℝ
    (supportedTimeAbelOperator N δ R hδ hR)
    (supportedTimeAbelOperator_add N δ R hδ hR)
    (supportedTimeAbelOperator_smul N δ R hδ hR)
    ⟨{1},positiveTimeNormConstant δ R,positiveTimeNormConstant_nonneg δ R hδ,
      fun φ => by simpa only [Finset.sup_singleton] using
        supportedTimeAbelOperator_bound N δ R hδ hR φ⟩

theorem supportedAbelDistribution_apply (N : ℕ) [NeZero N]
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) (φ : SupportedTimeTest δ R) :
    supportedAbelDistribution N δ R hδ hR φ=supportedTimeAbelOperator N δ R hδ hR φ := rfl

#print axioms supportedAbelDistribution
#print axioms supportedAbelDistribution_apply

end QuantitativeMaass
