module

public import QuantitativeMaassBoundedExpTestIntegralV1
public import QuantitativeMaassDistributionCauchyPairV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

def boundedCauchyPosition (A : H →L[ℝ] H) (c : H×H) (t : ℝ) : H :=
  (boundedExpEvolution (distributionCauchyOperator A) c t).1

def boundedCauchyVelocity (A : H →L[ℝ] H) (c : H×H) (t : ℝ) : H :=
  -(boundedExpEvolution (distributionCauchyOperator A) c t).2

theorem boundedCauchyPosition_hasDerivAt (A : H →L[ℝ] H) (c : H×H) (t : ℝ) :
    HasDerivAt (boundedCauchyPosition A c) (boundedCauchyVelocity A c t) t := by
  convert! (boundedExpEvolution_hasDerivAt (distributionCauchyOperator A) c t).fst using 1

theorem boundedCauchyVelocity_hasDerivAt (A : H →L[ℝ] H) (c : H×H) (t : ℝ) :
    HasDerivAt (boundedCauchyVelocity A c) (-A (boundedCauchyPosition A c t)) t := by
  have h := (boundedExpEvolution_hasDerivAt (distributionCauchyOperator A) c t).snd
  change HasDerivAt (fun s => (boundedExpEvolution (distributionCauchyOperator A) c s).2)
    (-(-A (boundedExpEvolution (distributionCauchyOperator A) c t).1)) t at h
  have hh : HasDerivAt (fun s => (boundedExpEvolution (distributionCauchyOperator A) c s).2)
      (A (boundedExpEvolution (distributionCauchyOperator A) c t).1) t := by
    simpa only [neg_neg] using h
  change HasDerivAt (fun s => -(boundedExpEvolution (distributionCauchyOperator A) c s).2)
    (-A (boundedExpEvolution (distributionCauchyOperator A) c t).1) t
  exact hh.neg

theorem boundedCauchyPosition_continuous (A : H →L[ℝ] H) (c : H×H) :
    Continuous (boundedCauchyPosition A c) :=
  continuous_iff_continuousAt.mpr (fun t => (boundedCauchyPosition_hasDerivAt A c t).continuousAt)

theorem boundedCauchyVelocity_continuous (A : H →L[ℝ] H) (c : H×H) :
    Continuous (boundedCauchyVelocity A c) :=
  continuous_iff_continuousAt.mpr (fun t => (boundedCauchyVelocity_hasDerivAt A c t).continuousAt)

omit [CompleteSpace H] in
theorem boundedCauchy_initial (A : H →L[ℝ] H) (c : H×H) :
    boundedCauchyPosition A c 0=c.1 ∧ boundedCauchyVelocity A c 0= -c.2 := by
  simp only [boundedCauchyPosition,boundedCauchyVelocity,boundedExpEvolution_zero,and_self]

theorem boundedExpEvolution_test_integrable (B : H →L[ℝ] H) (c : H) (φ : PositiveSmoothTest) :
    Integrable (fun t => φ t • boundedExpEvolution B c t) :=
  (φ.continuous.smul (boundedExpEvolution_continuous B c)).integrable_of_hasCompactSupport
    φ.hasCompactSupport.smul_right

theorem boundedCauchy_integral_fst (A : H →L[ℝ] H) (c : H×H) (φ : PositiveSmoothTest) :
    (∫ t,φ t • boundedExpEvolution (distributionCauchyOperator A) c t).1=
      ∫ t,φ t • boundedCauchyPosition A c t := by
  have he := (ContinuousLinearMap.fst ℝ H H).integral_comp_comm
    (boundedExpEvolution_test_integrable (distributionCauchyOperator A) c φ)
  exact he.symm

theorem boundedCauchy_integral_snd (A : H →L[ℝ] H) (c : H×H) (φ : PositiveSmoothTest) :
    (∫ t,φ t • boundedExpEvolution (distributionCauchyOperator A) c t).2=
      -(∫ t,φ t • boundedCauchyVelocity A c t) := by
  have he : (∫ t,φ t • (boundedExpEvolution (distributionCauchyOperator A) c t).2)=
      (∫ t,φ t • boundedExpEvolution (distributionCauchyOperator A) c t).2 :=
    (ContinuousLinearMap.snd ℝ H H).integral_comp_comm
      (boundedExpEvolution_test_integrable (distributionCauchyOperator A) c φ)
  rw [← he]
  change (∫ t,φ t • (boundedExpEvolution (distributionCauchyOperator A) c t).2)=
    -(∫ t,φ t • (-(boundedExpEvolution (distributionCauchyOperator A) c t).2))
  simp only [smul_neg,integral_neg,neg_neg]

#print axioms boundedCauchyPosition_hasDerivAt
#print axioms boundedCauchyVelocity_hasDerivAt
#print axioms boundedCauchy_integral_fst
#print axioms boundedCauchy_integral_snd

end QuantitativeMaass
