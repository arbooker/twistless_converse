module

public import QuantitativeMaassDistributionExpSummableV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem distributionExpTerm_add (T : PositiveSmoothTest →ₗ[ℝ] H) (B : H →L[ℝ] H)
    (φ ψ : PositiveSmoothTest) (n : ℕ) :
    distributionExpTerm T B (φ+ψ) n=distributionExpTerm T B φ n+distributionExpTerm T B ψ n := by
  simp only [distributionExpTerm,map_add,smul_add]

theorem distributionExpTerm_smul (T : PositiveSmoothTest →ₗ[ℝ] H) (B : H →L[ℝ] H)
    (c : ℝ) (φ : PositiveSmoothTest) (n : ℕ) :
    distributionExpTerm T B (c • φ) n=c • distributionExpTerm T B φ n := by
  simp only [distributionExpTerm,map_smul]
  exact smul_comm _ _ _

/-- The bounded integrating factor is constructed as an actual convergent
series of polynomially weighted tests. -/
def distributionExpTransform (T : PositiveSmoothTest →ₗ[ℝ] H) (B : H →L[ℝ] H)
    (hs : ∀ φ,Summable (distributionExpTerm T B φ)) : PositiveSmoothTest →ₗ[ℝ] H where
  toFun φ := ∑' n,distributionExpTerm T B φ n
  map_add' φ ψ := by
    simp_rw [distributionExpTerm_add]
    exact (hs φ).tsum_add (hs ψ)
  map_smul' c φ := by
    simp_rw [distributionExpTerm_smul]
    exact (hs φ).tsum_const_smul c

/-- The first-order equation forces the integrating factor to have zero
distributional derivative. The finite telescoping identity and convergence
are both used explicitly. -/
theorem distributionExpTransform_deriv (T : PositiveSmoothTest →ₗ[ℝ] H)
    (B : H →L[ℝ] H) (hs : ∀ φ,Summable (distributionExpTerm T B φ))
    (hT : ∀ φ,T (positiveSmoothTestDeriv φ)=B (T φ)) (φ : PositiveSmoothTest) :
    distributionExpTransform T B hs (positiveSmoothTestDeriv φ)=0 := by
  have hsum := ((hs (positiveSmoothTestDeriv φ)).hasSum.tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  have hzero := (B.continuous.tendsto 0).comp (hs φ).tendsto_atTop_zero
  have hlast : Tendsto (fun n => B (distributionExpTerm T B φ n)) atTop (𝓝 0) := by
    simpa only [map_zero,Function.comp_def] using hzero
  have he : (fun n => ∑ k∈Finset.range (n+1),distributionExpTerm T B (positiveSmoothTestDeriv φ) k)=
      (fun n => B (distributionExpTerm T B φ n)) :=
    funext (distributionExpTerm_deriv_sum T B hT φ)
  change Tendsto (fun n => ∑ k∈Finset.range (n+1),distributionExpTerm T B (positiveSmoothTestDeriv φ) k)
    atTop (𝓝 (∑' n,distributionExpTerm T B (positiveSmoothTestDeriv φ) n)) at hsum
  rw [he] at hsum
  exact tendsto_nhds_unique hsum hlast

/-- A bounded first-order distribution equation yields a constant
integrating factor. This is a general analytic lemma; applying its moment
bound and identifying its constant for the actual Abel distribution remain
separate tasks. -/
theorem distributionExpTransform_constant (T : PositiveSmoothTest →ₗ[ℝ] H)
    (B : H →L[ℝ] H) (hs : ∀ φ,Summable (distributionExpTerm T B φ))
    (hT : ∀ φ,T (positiveSmoothTestDeriv φ)=B (T φ)) (φ : PositiveSmoothTest) :
    distributionExpTransform T B hs φ=
      (∫ t,φ t) • distributionExpTransform T B hs positiveUnitTest :=
  positiveDistribution_eq_constant _ (distributionExpTransform_deriv T B hs hT) φ

theorem distributionExpTransform_constant_of_moments [CompleteSpace H] (T : PositiveSmoothTest →ₗ[ℝ] H)
    (B : H →L[ℝ] H)
    (hm : ∀ φ,∃ C R : ℝ,0≤C ∧ 0≤R ∧ ∀ n,‖T (positiveTestPower n φ)‖≤C*(n+1:ℝ)^2*R^n)
    (hT : ∀ φ,T (positiveSmoothTestDeriv φ)=B (T φ)) :
    ∃ hs : ∀ φ,Summable (distributionExpTerm T B φ),∀ φ,
      distributionExpTransform T B hs φ=
        (∫ t,φ t) • distributionExpTransform T B hs positiveUnitTest := by
  have hs (φ : PositiveSmoothTest) : Summable (distributionExpTerm T B φ) := by
    obtain ⟨C,R,hC,hR,hb⟩ := hm φ
    exact distributionExpTerm_summable T B φ C R hC hR hb
  exact ⟨hs,distributionExpTransform_constant T B hs hT⟩

#print axioms distributionExpTransform_deriv
#print axioms distributionExpTransform_constant_of_moments

end QuantitativeMaass
