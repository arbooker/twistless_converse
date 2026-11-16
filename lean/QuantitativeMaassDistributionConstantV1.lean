module

public import QuantitativeMaassPositiveTestPrimitiveV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

/-- Derivative zero annihilates every zero-mean test, since its explicit
primitive remains a valid compact test inside the same positive interval. -/
theorem positiveDistribution_zeroMean {H : Type*} [AddCommGroup H] [Module ℝ H]
    (T : PositiveSmoothTest →ₗ[ℝ] H)
    (hd : ∀ φ,T (positiveSmoothTestDeriv φ)=0)
    (φ : PositiveSmoothTest) (hz : (∫ t,φ t)=0) : T φ=0 := by
  rw [← positiveZeroMeanPrimitive_deriv φ hz]
  exact hd _

/-- A distribution with zero derivative on positive time is constant.
A unit-integral test fixes its constant; the statement holds even for
arbitrary real-linear functionals, hence for Banach-valued distributions. -/
theorem positiveDistribution_constant {H : Type*} [AddCommGroup H] [Module ℝ H]
    (T : PositiveSmoothTest →ₗ[ℝ] H)
    (hd : ∀ φ,T (positiveSmoothTestDeriv φ)=0)
    (η : PositiveSmoothTest) (hη : (∫ t,η t)=1) (φ : PositiveSmoothTest) :
    T φ=(∫ t,φ t) • T η := by
  let c : ℝ := ∫ t,φ t
  have hz : (∫ t,(φ-c • η) t)=0 := by
    change (∫ t,φ t-c*η t)=0
    have hφi : Integrable (φ : ℝ → ℝ) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    have hηi : Integrable (η : ℝ → ℝ) := η.continuous.integrable_of_hasCompactSupport η.hasCompactSupport
    rw [integral_sub hφi (hηi.const_mul c),integral_const_mul,hη,mul_one]
    exact sub_self _
  have h := positiveDistribution_zeroMean T hd (φ-c • η) hz
  rw [map_sub,map_smul] at h
  exact sub_eq_zero.mp h

#print axioms positiveDistribution_zeroMean
#print axioms positiveDistribution_constant

end QuantitativeMaass
