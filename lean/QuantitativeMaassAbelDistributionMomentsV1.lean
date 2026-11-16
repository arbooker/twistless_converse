module

public import QuantitativeMaassTestPowerBoundsV1
public import QuantitativeMaassDistributionIntegratingFactorV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

local instance (N : ℕ) : ContinuousSMul ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  IsScalarTower.continuousSMul ℂ

/-- The actual Abel LF distribution obeys the same common-support estimate
as its geometric positive-time realization. -/
theorem abelTestDistribution_norm_common (N : ℕ) [NeZero N]
    (φ : PositiveSmoothTest) (δ R C : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hs : tsupport φ ⊆ Icc δ R)
    (hb : ∀ t,‖positiveSmoothTestDeriv φ t‖≤C) :
    ‖abelTestDistribution N φ‖≤positiveTimeNormConstant δ R*C := by
  apply positiveTimeAbelOperator_norm_common N (positiveSmoothTestToAbel φ) δ R C hδ hR
  · intro t ht
    apply hs
    apply subset_tsupport
    intro hz
    exact ht (by change (φ t:ℂ)=0; rw [hz,Complex.ofReal_zero])
  · intro t
    have he : deriv (positiveSmoothTestToAbel φ).toFun t=
        ((positiveSmoothTestDeriv φ t:ℝ):ℂ) := by
      rw [positiveSmoothTestDeriv_apply]
      exact ((φ.contDiff.differentiable (by simp) t).hasDerivAt.ofReal_comp).deriv
    rw [he,Complex.norm_real]
    exact hb t

/-- Exponential moment bounds are proved for the literal Abel operator and
its distribution derivative, with constants chosen before the moment index.
No spectral equality or assumed distribution order enters this result. -/
theorem abelTestDistribution_exponential_moments (N : ℕ) [NeZero N]
    (φ : PositiveSmoothTest) :
    ∃ C R : ℝ,0≤C ∧ 0≤R ∧ ∀ n,
      ‖abelTestDistribution N (positiveTestPower n φ)‖≤C*R^n ∧
      ‖abelTestDistribution N (positiveSmoothTestDeriv (positiveTestPower n φ))‖≤C*R^n := by
  obtain ⟨C,R,hC,hR,hb⟩ := positiveTestPower_exists_two_derivative_bound φ
  let I := positiveSmoothTestInterval φ
  let K := positiveTimeNormConstant I.left I.right
  have hK : 0≤K := positiveTimeNormConstant_nonneg _ _ I.left_pos
  refine ⟨K*C,R,mul_nonneg hK hC,hR,?_⟩
  intro n
  have hs : tsupport (positiveTestPower n φ) ⊆ Icc I.left I.right :=
    (positiveTestPower_tsupport_subset n φ).trans I.subset
  have hs' := (positiveSmoothTestDeriv_tsupport_subset (positiveTestPower n φ)).trans hs
  constructor
  · calc
      _ ≤ K*(C*R^n) := abelTestDistribution_norm_common N _ I.left I.right (C*R^n)
        I.left_pos I.right_nonneg hs (fun t => (hb n t).2.1)
      _ = _ := by ring
  · calc
      _ ≤ K*(C*R^n) := abelTestDistribution_norm_common N _ I.left I.right (C*R^n)
        I.left_pos I.right_nonneg hs' (fun t => (hb n t).2.2)
      _ = _ := by ring

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Bounded postcomposition preserves the two actual Abel moment bounds.
This will apply to bounded spectral regularizations and vector evaluation. -/
theorem abelTestDistribution_postcomp_moments (N : ℕ) [NeZero N]
    (L : (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) →ₗ[ℝ] H)
    (K : ℝ) (hK : 0≤K) (hL : ∀ x,‖L x‖≤K*‖x‖) (φ : PositiveSmoothTest) :
    ∃ C R : ℝ,0≤C ∧ 0≤R ∧ ∀ n,
      ‖L (abelTestDistribution N (positiveTestPower n φ))‖≤C*R^n ∧
      ‖L (abelTestDistribution N (positiveSmoothTestDeriv (positiveTestPower n φ)))‖≤C*R^n := by
  obtain ⟨C,R,hC,hR,hb⟩ := abelTestDistribution_exponential_moments N φ
  refine ⟨K*C,R,mul_nonneg hK hC,hR,?_⟩
  intro n
  constructor
  · calc
      _ ≤ K*‖abelTestDistribution N (positiveTestPower n φ)‖ := hL _
      _ ≤ K*(C*R^n) := mul_le_mul_of_nonneg_left (hb n).1 hK
      _ = _ := by ring
  · calc
      _ ≤ K*‖abelTestDistribution N (positiveSmoothTestDeriv (positiveTestPower n φ))‖ := hL _
      _ ≤ K*(C*R^n) := mul_le_mul_of_nonneg_left (hb n).2 hK
      _ = _ := by ring

#print axioms abelTestDistribution_norm_common
#print axioms abelTestDistribution_exponential_moments
#print axioms abelTestDistribution_postcomp_moments

end QuantitativeMaass
