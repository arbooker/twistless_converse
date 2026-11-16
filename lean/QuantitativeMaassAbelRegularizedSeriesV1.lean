module

public import QuantitativeMaassAbelRegularizedDistributionV1
public import QuantitativeMaassDistributionExpInverseV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

/-- The actual regularized Abel distribution and its tested derivative
have an exact exponential-moment series representation by one constant
Cauchy pair. Every hypothesis of the generic inverse theorem is discharged.
The smooth-evolution integral and identification of this pair remain separate. -/
theorem regularizedAbelDistribution_series (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) :
    ∃ c : AutomorphicSpace N×AutomorphicSpace N,∀ φ : PositiveSmoothTest,
      distributionCauchyPair (regularizedAbelDistribution N ε f) φ=
        ∑' n,((-1:ℝ)^n*(n.factorial:ℝ)⁻¹) •
          ((∫ t,φ t*t^n) •
            (distributionCauchyOperator (regularizedShiftedGenerator N ε)^n) c) := by
  obtain ⟨hs,_⟩ := regularizedAbelDistribution_constant N ε hε f
  let T := distributionCauchyPair (regularizedAbelDistribution N ε f)
  let B := distributionCauchyOperator (regularizedShiftedGenerator N ε)
  refine ⟨distributionExpTransform T B hs positiveUnitTest,?_⟩
  intro φ
  obtain ⟨C,R,hC,hR,hb⟩ := abelTestDistribution_postcomp_moments N
    (abelCutoffEvaluation N ε f) ‖f‖ (norm_nonneg _) (abelCutoffEvaluation_bound N ε hε f) φ
  have hm : ∀ n,‖T (positiveTestPower n φ)‖≤C*R^n := by
    intro n
    exact max_le (hb n).1 (hb n).2
  have he : ∀ ψ,T (positiveSmoothTestDeriv ψ)=B (T ψ) :=
    distributionCauchyPair_equation _ _ (regularizedAbelDistribution_equation N ε hε f)
  exact distributionExpTransform_series_representation T B hs he φ C R hC hR hm

#print axioms regularizedAbelDistribution_series

end QuantitativeMaass
