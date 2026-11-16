module

public import QuantitativeMaassWeightedLinearV1
public import QuantitativeMaassEulerIndependenceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

variable {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
  (A : FinitenessCertificate.Certificate N Q hQ) (P : FinitenessGlobalHeight.Parameters A)

def originalWeightedAnalytic (r : ℝ) (σ : ℕ) (b : MaassOriginal.EulerS N (.principal r) σ) :
    weightedAnalyticSpace P.ε (P.s+3) := by
  refine ⟨principalEulerWave b.val r σ,(principalEulerSmooth b.property.polynomialGrowth r σ).property,
    fun y hy => principalEulerWave_analytic_horizontal b.property.polynomialGrowth r σ y hy,?_⟩
  rw [weightedStripMap_eq_section]
  exact principalEulerPhysical_weighted_memLp hN A P r σ b.property

/-- The actual original family is linearly independent in one fixed weighted
Hilbert space simultaneously over all nonnegative real spectral parameters.
There is no common individual coefficient-growth hypothesis and no assumed
modularity or spectral orthogonality. -/
theorem originalEuler_all_hilbert_independent (σ : ℕ) :
    LinearIndependent ℂ (fun rb : Σ r : {r : ℝ // 0≤r},MaassOriginal.EulerS N (.principal r.val) σ =>
      weightedAnalyticLp P.ε (P.s+3) (originalWeightedAnalytic hN A P rb.1.val σ rb.2)) := by
  have hs : LinearIndependent ℂ (fun rb : Σ r : {r : ℝ // 0≤r},MaassOriginal.EulerS N (.principal r.val) σ =>
      originalWeightedAnalytic hN A P rb.1.val σ rb.2) := by
    apply LinearIndependent.of_comp (weightedAnalyticForget P.ε (P.s+3))
    exact originalEuler_all_principal_independent N σ
  exact hs.map' (weightedAnalyticLp P.ε (P.s+3))
    (LinearMap.ker_eq_bot.mpr (weightedAnalyticLp_injective P.ε P.epsilon_pos (P.s+3)))

/-- The Hilbert linear embedding is the previously constructed literal
weighted Euler class, rather than an unrelated abstract model. -/
theorem originalWeightedAnalytic_lp_eq (r : ℝ) (σ : ℕ) (b : MaassOriginal.EulerS N (.principal r) σ) :
    weightedAnalyticLp P.ε (P.s+3) (originalWeightedAnalytic hN A P r σ b)=
      principalEulerWeightedLp hN A P r σ b.property := by
  apply Lp.ext
  apply (weightedAnalyticLp_coeFn P.ε (P.s+3) (originalWeightedAnalytic hN A P r σ b)).trans
  rw [weightedStripMap_eq_section]
  exact (principalEulerWeightedLp_coeFn hN A P r σ b.property).symm

theorem originalEuler_weighted_classes_independent (σ : ℕ) :
    LinearIndependent ℂ (fun rb : Σ r : {r : ℝ // 0≤r},MaassOriginal.EulerS N (.principal r.val) σ =>
      principalEulerWeightedLp hN A P rb.1.val σ rb.2.property) := by
  have hh := originalEuler_all_hilbert_independent hN A P σ
  simpa only [originalWeightedAnalytic_lp_eq] using hh

#print axioms originalWeightedAnalytic
#print axioms originalEuler_all_hilbert_independent
#print axioms originalWeightedAnalytic_lp_eq
#print axioms originalEuler_weighted_classes_independent

end QuantitativeMaass
