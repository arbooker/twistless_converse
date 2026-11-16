module

public import QuantitativeMaassPositiveTestSeparationV1
public import QuantitativeMaassAbelRegularizedEvolutionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

/-- A bounded generator identity for every tested integral of a continuous
curve implies the full actual Friedrichs graph at every nonnegative time. -/
theorem friedrichsGraph_of_tested_integrals (N : ℕ)
    (G : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (u : ℝ → AutomorphicSpace N) (hu : Continuous u)
    (hg : ∀ φ : PositiveSmoothTest,FriedrichsGraph N (∫ t,φ t • u t) (G (∫ t,φ t • u t))) :
    ∀ t,0≤t → FriedrichsGraph N (u t) (G (u t)) := by
  let D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N := friedrichsResolvent N*(1+G)-1
  have hd : Continuous (fun t => D (u t)) := D.continuous.comp hu
  have hz (φ : PositiveSmoothTest) : (∫ t,φ t • D (u t))=0 := by
    have he : D (∫ t,φ t • u t)=∫ t,φ t • D (u t) :=
      positiveTest_integral_map (D.restrictScalars ℝ) u hu φ
    rw [← he]
    change friedrichsResolvent N ((∫ t,φ t • u t)+G (∫ t,φ t • u t))-(∫ t,φ t • u t)=0
    exact sub_eq_zero.mpr (hg φ)
  have hzero := continuous_eq_zero_of_positiveTests (fun t => D (u t)) hd hz
  intro t ht
  have he := hzero t ht
  change friedrichsResolvent N (u t+G (u t))-u t=0 at he
  exact sub_eq_zero.mp he

/-- The position recovered from the actual regularized Abel distribution
lies in the full Friedrichs domain, including at time zero. -/
theorem regularizedAbelPosition_graph (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hc : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) :
    ∀ t,0≤t → FriedrichsGraph N
      (boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)
      (Wave.boundedResolventOperator (friedrichsResolvent N) ε
        (boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)) := by
  apply friedrichsGraph_of_tested_integrals
    N _ _ (boundedCauchyPosition_continuous _ c)
  intro φ
  rw [← hc φ]
  exact Wave.friedrichsCutoff_graph N ε hε (abelTestDistribution N φ f)

#print axioms friedrichsGraph_of_tested_integrals
#print axioms regularizedAbelPosition_graph

end QuantitativeMaass
