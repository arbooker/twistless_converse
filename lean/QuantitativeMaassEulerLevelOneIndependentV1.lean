module

public import QuantitativeMaassQuotientLinearV1
public import QuantitativeMaassEulerLevelOneGraphV1
public import QuantitativeMaassEulerIndependenceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- Actual quotient-integrable analytic wave of original level-one data. -/
def originalLevelOneAnalytic (r : ℝ) (σ : ℕ) (b : MaassOriginal.EulerS 1 (.principal r) σ) :
    quotientAnalyticSpace 1 :=
  ⟨principalEulerWave b.val r σ,(principalEulerSmooth b.property.polynomialGrowth r σ).property,
    fun y hy => principalEulerWave_analytic_horizontal b.property.polynomialGrowth r σ y hy,
    principalEulerPhysical_level_one_memLp r σ b.property⟩

theorem originalLevelOneAnalytic_lp_eq (r : ℝ) (σ : ℕ) (b : MaassOriginal.EulerS 1 (.principal r) σ) :
    quotientAnalyticLp 1 (originalLevelOneAnalytic r σ b)=(principalEulerLevelOneClass r σ b.property).val := rfl

/-- Simultaneous linear independence of the genuine quotient eigenfunctions
attached to all original level-one parameters and coefficients. -/
theorem originalEuler_all_level_one_independent (σ : ℕ) :
    LinearIndependent ℂ (fun rb : Σ r : {r : ℝ // 0≤r},MaassOriginal.EulerS 1 (.principal r.val) σ =>
      principalEulerLevelOneClass rb.1.val σ rb.2.property) := by
  have hs : LinearIndependent ℂ (fun rb : Σ r : {r : ℝ // 0≤r},MaassOriginal.EulerS 1 (.principal r.val) σ =>
      originalLevelOneAnalytic rb.1.val σ rb.2) := by
    apply LinearIndependent.of_comp (quotientAnalyticForget 1)
    exact originalEuler_all_principal_independent 1 σ
  have hl := hs.map' (quotientAnalyticLp 1)
    (LinearMap.ker_eq_bot.mpr (quotientAnalyticLp_injective 1))
  apply LinearIndependent.of_comp (AutomorphicSpace 1).subtype
  simpa only [Function.comp_def,originalLevelOneAnalytic_lp_eq] using! hl

theorem originalEuler_all_level_one_cusp_independent (σ : ℕ) :
    LinearIndependent ℂ (fun rb : Σ r : {r : ℝ // 0≤r},MaassOriginal.EulerS 1 (.principal r.val) σ =>
      principalEulerLevelOneCuspClass rb.1.val σ rb.2.property) := by
  apply LinearIndependent.of_comp (localCuspidalSpace 1 (by norm_num)).subtype
  exact originalEuler_all_level_one_independent σ

#print axioms originalLevelOneAnalytic
#print axioms originalLevelOneAnalytic_lp_eq
#print axioms originalEuler_all_level_one_independent
#print axioms originalEuler_all_level_one_cusp_independent

end QuantitativeMaass
