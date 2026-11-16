module

public import QuantitativeMaassAbelDistributionMomentsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The distribution and its tested derivative form a genuine linear pair. -/
def distributionCauchyPair (T : PositiveSmoothTest →ₗ[ℝ] H) :
    PositiveSmoothTest →ₗ[ℝ] H×H :=
  T.prod (T.comp positiveSmoothTestDeriv.toLinearMap)

/-- Bounded first-order block operator for the tested equation T''=-A T. -/
def distributionCauchyOperator (A : H →L[ℝ] H) : H×H →L[ℝ] H×H :=
  (ContinuousLinearMap.snd ℝ H H).prod
    (-(A.comp (ContinuousLinearMap.fst ℝ H H)))

theorem distributionCauchyPair_equation (T : PositiveSmoothTest →ₗ[ℝ] H)
    (A : H →L[ℝ] H)
    (he : ∀ φ,T (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ))= -A (T φ))
    (φ : PositiveSmoothTest) :
    distributionCauchyPair T (positiveSmoothTestDeriv φ)=
      distributionCauchyOperator A (distributionCauchyPair T φ) := by
  apply Prod.ext
  · rfl
  · exact he φ

theorem distributionCauchyPair_moments (T : PositiveSmoothTest →ₗ[ℝ] H)
    (φ : PositiveSmoothTest) (C R : ℝ) (hC : 0≤C) (hR : 0≤R)
    (hm : ∀ n,‖T (positiveTestPower n φ)‖≤C*R^n ∧
      ‖T (positiveSmoothTestDeriv (positiveTestPower n φ))‖≤C*R^n) (n : ℕ) :
    ‖distributionCauchyPair T (positiveTestPower n φ)‖≤C*(n+1:ℝ)^2*R^n := by
  have hn : 1≤(n+1:ℝ)^2 := by nlinarith [show (0:ℝ)≤n by positivity]
  calc
    _ ≤ C*R^n := max_le (hm n).1 (hm n).2
    _ ≤ C*(n+1:ℝ)^2*R^n := by nlinarith [mul_nonneg hC (pow_nonneg hR n)]

/-- General bounded second-order equation: its actual convergent integrating
factor is constant. Reconstruction from this factor is a separate result. -/
theorem distributionCauchyPair_constant [CompleteSpace H]
    (T : PositiveSmoothTest →ₗ[ℝ] H) (A : H →L[ℝ] H)
    (hm : ∀ φ,∃ C R : ℝ,0≤C ∧ 0≤R ∧ ∀ n,
      ‖T (positiveTestPower n φ)‖≤C*R^n ∧
      ‖T (positiveSmoothTestDeriv (positiveTestPower n φ))‖≤C*R^n)
    (he : ∀ φ,T (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ))= -A (T φ)) :
    ∃ hs : ∀ φ,Summable (distributionExpTerm (distributionCauchyPair T)
      (distributionCauchyOperator A) φ),∀ φ,
      distributionExpTransform (distributionCauchyPair T) (distributionCauchyOperator A) hs φ=
        (∫ t,φ t) • distributionExpTransform (distributionCauchyPair T)
          (distributionCauchyOperator A) hs positiveUnitTest := by
  apply distributionExpTransform_constant_of_moments
  · intro φ
    obtain ⟨C,R,hC,hR,hb⟩ := hm φ
    exact ⟨C,R,hC,hR,distributionCauchyPair_moments T φ C R hC hR hb⟩
  · exact distributionCauchyPair_equation T A he

/-- For every bounded postcomposition of the actual Abel distribution,
the first-order integrating-factor series converges. No differential equation
or spectral identification is required for this convergence statement. -/
theorem abelCauchyPair_summable [CompleteSpace H] (N : ℕ) [NeZero N]
    (L : (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) →ₗ[ℝ] H)
    (K : ℝ) (hK : 0≤K) (hL : ∀ x,‖L x‖≤K*‖x‖)
    (A : H →L[ℝ] H) (φ : PositiveSmoothTest) :
    Summable (distributionExpTerm
      (distributionCauchyPair (L.comp (abelTestDistribution N).toLinearMap))
      (distributionCauchyOperator A) φ) := by
  obtain ⟨C,R,hC,hR,hb⟩ := abelTestDistribution_postcomp_moments N L K hK hL φ
  apply distributionExpTerm_summable _ _ φ C R hC hR
  exact distributionCauchyPair_moments _ φ C R hC hR hb

#print axioms distributionCauchyPair_equation
#print axioms distributionCauchyPair_constant
#print axioms abelCauchyPair_summable

end QuantitativeMaass
