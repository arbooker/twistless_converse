module

public import QuantitativeMaassPoincareUnfoldV1

set_option autoImplicit false
set_option maxHeartbeats 200000
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass

/-- Restriction of any invariant nonnegative density is controlled by
its quotient integral and the explicit orbit multiplicity of the set.
In particular this applies to the sum of squared gradient components,
without asserting invariance of the individual components. -/
theorem invariant_lintegral_restrict_le {G A : Type*} [Group G] [Countable G]
    [MulAction G A] [MeasurableSpace A] (μ : Measure A)
    (hmp : ∀ g : G, MeasurePreserving (fun x : A => g • x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ)
    (hn : ∀ x, ∑' g : G, ρ (g • x) = 1)
    (K : Set A) (hK : MeasurableSet K) (C : ℝ≥0∞)
    (hC : ∀ x, (∑' g : G, K.indicator (fun _ => (1 : ℝ≥0∞)) (g • x)) ≤ C)
    (F : A → ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ g : G, ∀ x, F (g • x) = F x) :
    (∫⁻ x, F x ∂μ.restrict K) ≤ C * ∫⁻ x, F x ∂μ.withDensity ρ := by
  classical
  have hu := lintegral_poincare_unfold μ hmp ρ hρ hn (K.indicator F) (hF.indicator hK)
  have he (x : A) : (∑' g : G, K.indicator F (g • x)) =
      (∑' g : G, K.indicator (fun _ => (1 : ℝ≥0∞)) (g • x)) * F x := by
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro g
    by_cases hg : g • x ∈ K
    · simp only [Set.indicator_of_mem hg, one_mul, hinv]
    · simp only [Set.indicator_of_notMem hg, zero_mul]
  rw [← lintegral_indicator hK F, ← hu]
  simp_rw [he]
  calc
    _ ≤ ∫⁻ x, C * F x ∂μ.withDensity ρ :=
      lintegral_mono (fun x => by gcongr; exact hC x)
    _ = _ := lintegral_const_mul _ hF

/-- A bound on finite orbit intersections gives the explicit multiplicity
in the nonnegative restriction estimate. No compactness is hidden in the
constant, so quantitative ball-overlap estimates can be substituted. -/
theorem orbit_indicator_tsum_le_of_overlap {G A : Type*} [Group G]
    [MulAction G A] (K : Set A) (M : ℕ)
    (hM : ∀ x : A, ∀ S : Finset G, (∀ g ∈ S, g • x ∈ K) → S.card ≤ M)
    (x : A) :
    (∑' g : G, K.indicator (fun _ => (1 : ℝ≥0∞)) (g • x)) ≤ M := by
  classical
  apply ENNReal.summable.tsum_le_of_sum_le
  intro S
  have he : (∑ g ∈ S, K.indicator (fun _ => (1 : ℝ≥0∞)) (g • x)) =
      ((S.filter (fun g => g • x ∈ K)).card : ℝ≥0∞) := by
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp
  rw [he]
  exact_mod_cast hM x (S.filter (fun g => g • x ∈ K))
    (fun g hg => (Finset.mem_filter.mp hg).2)

#print axioms invariant_lintegral_restrict_le
#print axioms orbit_indicator_tsum_le_of_overlap

end QuantitativeMaass
