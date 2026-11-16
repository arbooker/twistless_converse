module

public import QuantitativeMaassDistributionConstantV1
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

def positiveUnitSeed (t : ℝ) : ℝ :=
  Real.smoothTransition (t-1)*(1-Real.smoothTransition (t-2))

theorem positiveUnitSeed_smooth : ContDiff ℝ ∞ positiveUnitSeed := by
  unfold positiveUnitSeed
  fun_prop

theorem positiveUnitSeed_support : Function.support positiveUnitSeed⊆Icc 1 3 := by
  intro t ht
  constructor
  · by_contra hn
    exact ht (by simp [positiveUnitSeed,Real.smoothTransition.zero_of_nonpos (by linarith : t-1≤0)])
  · by_contra hn
    exact ht (by simp [positiveUnitSeed,Real.smoothTransition.one_of_one_le (by linarith : 1≤t-2)])

theorem positiveUnitSeed_compact : HasCompactSupport positiveUnitSeed :=
  isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal positiveUnitSeed_support isClosed_Icc)

theorem positiveUnitSeed_mass_pos : 0<∫ t,positiveUnitSeed t := by
  apply integral_pos_of_integrable_nonneg_nonzero positiveUnitSeed_smooth.continuous
    (positiveUnitSeed_smooth.continuous.integrable_of_hasCompactSupport positiveUnitSeed_compact)
    (fun t => mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _))) (x:=2)
  norm_num [positiveUnitSeed]

/-- An explicit unit-integral smooth test with support strictly inside
positive time; no existence or normalization premise is supplied. -/
def positiveUnitTest : PositiveSmoothTest where
  toFun t := (∫ s,positiveUnitSeed s)⁻¹*positiveUnitSeed t
  contDiff' := contDiff_const.mul positiveUnitSeed_smooth
  hasCompactSupport' := positiveUnitSeed_compact.mul_left
  tsupport_subset' := by
    have hs : Function.support (fun t => (∫ s,positiveUnitSeed s)⁻¹*positiveUnitSeed t)⊆Icc 1 3 := by
      intro t ht
      apply positiveUnitSeed_support
      intro hz
      exact ht (by simp only [hz,mul_zero])
    have hc := closure_minimal hs isClosed_Icc
    intro t ht
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (hc ht).1

theorem positiveUnitTest_mass : (∫ t,positiveUnitTest t)=1 := by
  change (∫ t,(∫ s,positiveUnitSeed s)⁻¹*positiveUnitSeed t)=1
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (ne_of_gt positiveUnitSeed_mass_pos)

/-- The complete derivative-zero statement with its constant explicitly
chosen by the constructed unit test. -/
theorem positiveDistribution_eq_constant {H : Type*} [AddCommGroup H] [Module ℝ H]
    (T : PositiveSmoothTest →ₗ[ℝ] H) (hd : ∀ φ,T (positiveSmoothTestDeriv φ)=0)
    (φ : PositiveSmoothTest) : T φ=(∫ t,φ t) • T positiveUnitTest :=
  positiveDistribution_constant T hd positiveUnitTest positiveUnitTest_mass φ

#print axioms positiveUnitTest_mass
#print axioms positiveDistribution_eq_constant

end QuantitativeMaass
