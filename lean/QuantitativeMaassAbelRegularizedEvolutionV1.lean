module

public import QuantitativeMaassAbelRegularizedSeriesV1
public import QuantitativeMaassBoundedCauchyEvolutionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

/-- The literal regularized geometric Abel distribution is represented by
an actual differentiable bounded evolution, with one fixed pair of Cauchy
data. No representation or moment bound is assumed. -/
theorem regularizedAbelDistribution_evolution (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) :
    ∃ c : AutomorphicSpace N×AutomorphicSpace N,∀ φ : PositiveSmoothTest,
      distributionCauchyPair (regularizedAbelDistribution N ε f) φ=
        ∫ t,φ t • boundedExpEvolution
          (distributionCauchyOperator (regularizedShiftedGenerator N ε)) c t := by
  obtain ⟨c,hc⟩ := regularizedAbelDistribution_series N ε hε f
  exact ⟨c,fun φ => (hc φ).trans (boundedExpEvolution_test_integral _ c φ)⟩

/-- Both components are identified with the position and minus velocity
integrals. The sign matches the tested derivative in the Cauchy pair. -/
theorem regularizedAbelDistribution_position_velocity (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) :
    ∃ c : AutomorphicSpace N×AutomorphicSpace N,∀ φ : PositiveSmoothTest,
      regularizedAbelDistribution N ε f φ=
        (∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) ∧
      regularizedAbelDistribution N ε f (positiveSmoothTestDeriv φ)=
        -(∫ t,φ t • boundedCauchyVelocity (regularizedShiftedGenerator N ε) c t) := by
  obtain ⟨c,hc⟩ := regularizedAbelDistribution_evolution N ε hε f
  refine ⟨c,?_⟩
  intro φ
  exact ⟨(congrArg Prod.fst (hc φ)).trans (boundedCauchy_integral_fst _ c φ),
    (congrArg Prod.snd (hc φ)).trans (boundedCauchy_integral_snd _ c φ)⟩

#print axioms regularizedAbelDistribution_evolution
#print axioms regularizedAbelDistribution_position_velocity

end QuantitativeMaass
