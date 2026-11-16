module

public import QuantitativeMaassSpectralCutoffLimitV1
public import QuantitativeMaassDistributionCauchyPairV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

local instance (N : ℕ) : ContinuousSMul ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  IsScalarTower.continuousSMul ℂ

/-- Fixed-vector evaluation followed by the explicit resolvent cutoff. -/
def abelCutoffEvaluation (N : ℕ) (ε : ℝ) (f : AutomorphicSpace N) :
    (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) →ₗ[ℝ] AutomorphicSpace N :=
  ((Wave.resolventCutoffOperator (friedrichsResolvent N) ε).restrictScalars ℝ).toLinearMap.comp
    ((ContinuousLinearMap.apply ℂ (AutomorphicSpace N) f).restrictScalars ℝ).toLinearMap

theorem abelCutoffEvaluation_bound (N : ℕ) (ε : ℝ) (hε : 0<ε)
    (f : AutomorphicSpace N) (X : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    ‖abelCutoffEvaluation N ε f X‖≤‖f‖*‖X‖ := by
  let P := Wave.resolventCutoffOperator (friedrichsResolvent N) ε
  change ‖P (X f)‖≤_
  calc
    _ ≤ ‖P‖*‖X f‖ := P.le_opNorm _
    _ ≤ 1*(‖X‖*‖f‖) := mul_le_mul
      (Wave.resolventCutoffOperator_norm_le _ ε hε) (X.le_opNorm f) (norm_nonneg _) zero_le_one
    _ = _ := by ring

def regularizedAbelDistribution (N : ℕ) [NeZero N] (ε : ℝ) (f : AutomorphicSpace N) :
    PositiveSmoothTest →ₗ[ℝ] AutomorphicSpace N :=
  (abelCutoffEvaluation N ε f).comp (abelTestDistribution N).toLinearMap

def regularizedShiftedGenerator (N : ℕ) (ε : ℝ) :
    AutomorphicSpace N →L[ℝ] AutomorphicSpace N :=
  (Wave.boundedResolventOperator (friedrichsResolvent N) ε-
    (1/4:ℂ) • (1 : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)).restrictScalars ℝ

/-- The actual regularized geometric distribution satisfies a bounded
second-order equation. This follows from its full Friedrichs graph and the
proved cutoff identity, with no spectral representation hypothesis. -/
theorem regularizedAbelDistribution_equation (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) (φ : PositiveSmoothTest) :
    regularizedAbelDistribution N ε f (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ))=
      -regularizedShiftedGenerator N ε (regularizedAbelDistribution N ε f φ) := by
  let P := Wave.resolventCutoffOperator (friedrichsResolvent N) ε
  let G := Wave.boundedResolventOperator (friedrichsResolvent N) ε
  have hg := Wave.friedrichsCutoff_generator_on_graph N ε hε (abelTestDistribution_graph N φ f)
  change P ((1/4:ℂ) • abelTestDistribution N φ f-
      abelTestDistribution N (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ)) f)=
    G (P (abelTestDistribution N φ f)) at hg
  rw [map_sub,map_smul] at hg
  change P (abelTestDistribution N (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ)) f)=
    -(G (P (abelTestDistribution N φ f))-(1/4:ℂ) • P (abelTestDistribution N φ f))
  rw [← hg]
  abel

/-- The integrating factor for every actual regularized Abel distribution
is constant. Both its moment growth and its differential equation have
been proved above, rather than imposed as additional analytic premises. -/
theorem regularizedAbelDistribution_constant (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) :
    ∃ hs : ∀ φ,Summable (distributionExpTerm
      (distributionCauchyPair (regularizedAbelDistribution N ε f))
      (distributionCauchyOperator (regularizedShiftedGenerator N ε)) φ),∀ φ,
      distributionExpTransform (distributionCauchyPair (regularizedAbelDistribution N ε f))
        (distributionCauchyOperator (regularizedShiftedGenerator N ε)) hs φ=
      (∫ t,φ t) • distributionExpTransform (distributionCauchyPair (regularizedAbelDistribution N ε f))
        (distributionCauchyOperator (regularizedShiftedGenerator N ε)) hs positiveUnitTest := by
  apply distributionCauchyPair_constant
  · intro φ
    exact abelTestDistribution_postcomp_moments N (abelCutoffEvaluation N ε f) ‖f‖
      (norm_nonneg _) (abelCutoffEvaluation_bound N ε hε f) φ
  · exact regularizedAbelDistribution_equation N ε hε f

/-- Removing the explicit cutoff recovers the actual Abel distribution
strongly on every test and every quotient-L2 input vector. -/
theorem regularizedAbelDistribution_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) [NeZero N] (ε : ι → ℝ) (hε : ∀ᶠ i in l,0<ε i) (hε0 : Tendsto ε l (𝓝 0))
    (f : AutomorphicSpace N) (φ : PositiveSmoothTest) :
    Tendsto (fun i => regularizedAbelDistribution N (ε i) f φ) l (𝓝 (abelTestDistribution N φ f)) :=
  Wave.friedrichsCutoff_tendsto l N ε hε hε0 _

#print axioms abelCutoffEvaluation_bound
#print axioms regularizedAbelDistribution_equation
#print axioms regularizedAbelDistribution_constant
#print axioms regularizedAbelDistribution_tendsto

end QuantitativeMaass
