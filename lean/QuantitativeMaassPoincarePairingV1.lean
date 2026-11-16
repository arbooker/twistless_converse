module

public import QuantitativeMaassQuotientLocalL2V1
public import QuantitativeMaassPoincareComplexUnfoldV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

/-- Exact complex pairing with compact Poincaré tests. The ambient product is
integrable because invariant quotient-L² representatives are locally L²;
the series/integral interchange follows from complex unfolding, not from a
formal rearrangement of the Poincaré series. -/
theorem integral_poincare_pairing {G A : Type*} [Group G] [Countable G]
    [TopologicalSpace A] [LocallyCompactSpace A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] [MulAction G A]
    [ProperlyDiscontinuousSMul G A] [ContinuousConstSMul G A]
    (μ : Measure A) [IsFiniteMeasureOnCompacts μ]
    (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (f : A → ℂ) (hf : Measurable f) (hinv : ∀ g : G, ∀ x, f (g•x)=f x)
    (hL : MemLp f 2 (μ.withDensity ρ))
    (φ : A → ℂ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => star (f x)*φ x) μ ∧
      Integrable (fun x => star (f x)*poincareSum (G := G) φ x) (μ.withDensity ρ) ∧
      (∫ x, star (f x)*poincareSum (G := G) φ x ∂μ.withDensity ρ)=
        ∫ x, star (f x)*φ x ∂μ := by
  have hloc := invariant_memLp_restrict_compact μ hmp ρ hρ hn f hf hinv hL
    (tsupport φ) hc isClosed_closure.measurableSet
  have hφL : MemLp φ 2 μ := hφ.memLp_of_hasCompactSupport hc
  have hi : Integrable (fun x => star (f x)*φ x) μ := by
    apply (integrableOn_iff_integrable_of_support_subset (s := tsupport φ) ?_).mp
    · exact hloc.star.integrable_mul (hφL.restrict _)
    · intro x hx
      apply subset_closure
      intro hz
      exact hx (by simp [hz])
  have hu := integral_poincare_unfold μ hmp ρ hρ hn
    (fun x => star (f x)*φ x) ((continuous_star.measurable.comp hf).mul hφ.measurable) hi
  have he (x : A) : (∑' g : G, star (f (g•x))*φ (g•x))=
      star (f x)*poincareSum (G := G) φ x := by
    simp_rw [hinv]
    exact tsum_mul_left
  simp_rw [he] at hu
  exact ⟨hi,hu⟩

#print axioms integral_poincare_pairing

end QuantitativeMaass
