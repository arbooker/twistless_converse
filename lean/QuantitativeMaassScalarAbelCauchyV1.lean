module

public import QuantitativeMaassScalarAbelDistributionV1
public import QuantitativeMaassAbelRegularizedEvolutionV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

/-- A bounded second-order tested equation with the proved exponential
moment bounds has an actual continuous Cauchy representation. -/
theorem distributionCauchy_representation {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [CompleteSpace H]
    (T : PositiveSmoothTest →ₗ[ℝ] H) (A : H →L[ℝ] H)
    (hm : ∀ φ,∃ C R : ℝ,0≤C ∧ 0≤R ∧ ∀ n,
      ‖T (positiveTestPower n φ)‖≤C*R^n ∧
      ‖T (positiveSmoothTestDeriv (positiveTestPower n φ))‖≤C*R^n)
    (he : ∀ φ,T (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ))= -A (T φ)) :
    ∃ c : H×H,∀ φ : PositiveSmoothTest,
      T φ=∫ t,φ t • boundedCauchyPosition A c t := by
  obtain ⟨hs,_⟩ := distributionCauchyPair_constant T A hm he
  let S := distributionCauchyPair T
  let B := distributionCauchyOperator A
  let c := distributionExpTransform S B hs positiveUnitTest
  refine ⟨c,?_⟩
  intro φ
  obtain ⟨C,R,hC,hR,hb⟩ := hm φ
  have hm' : ∀ n,‖S (positiveTestPower n φ)‖≤C*R^n :=
    fun n => max_le (hb n).1 (hb n).2
  have he' : ∀ ψ,S (positiveSmoothTestDeriv ψ)=B (S ψ) :=
    distributionCauchyPair_equation T A he
  have hh := distributionExpTransform_series_representation S B hs he' φ C R hC hR hm'
  have hv := hh.trans (boundedExpEvolution_test_integral B c φ)
  exact (congrArg Prod.fst hv).trans (boundedCauchy_integral_fst A c φ)

/-- The scalar generator associated to the classical Laplace eigenvalue e. -/
def scalarAbelGenerator (e : ℂ) : ℂ →L[ℂ] ℂ :=
  (e-1/4) • (1 : ℂ →L[ℂ] ℂ)

theorem scalarAbel_cauchy (u : ℝ×ℝ → ℂ)
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (e : ℂ)
    (he : ∀ y : ℍ,upperLaplacian u y=e*upperFunction u y) (x : ℍ) :
    ∃ c : ℂ × ℂ,∀ φ : PositiveSmoothTest,
      scalarAbelDistribution (upperFunction u) (upperFunction_continuous hu) x φ=
        ∫ t,φ t • boundedCauchyPosition ((scalarAbelGenerator e).restrictScalars ℝ) c t := by
  apply distributionCauchy_representation
  · exact scalarAbelDistribution_moments _ _ x
  · intro φ
    rw [scalarAbelDistribution_equation u hu e he x φ]
    change (1/4-e)*scalarAbelDistribution (upperFunction u) (upperFunction_continuous hu) x φ=
      -((e-1/4)*((1 : ℂ →L[ℂ] ℂ)
        (scalarAbelDistribution (upperFunction u) (upperFunction_continuous hu) x φ)))
    rw [one_apply_eq_self]
    ring

#print axioms distributionCauchy_representation
#print axioms scalarAbel_cauchy

end QuantitativeMaass
