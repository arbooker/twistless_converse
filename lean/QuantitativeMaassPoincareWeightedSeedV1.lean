module

public import QuantitativeMaassPoincareTruncationV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

theorem normalized_orbit_weight_le_one {G A : Type*} [Group G] [MulAction G A]
    (ρ : A → ℝ≥0∞) (hn : ∀ x, ∑' g : G, ρ (g•x)=1) (x : A) : ρ x≤1 := by
  have h := ENNReal.le_tsum (f := fun g : G => ρ (g•x)) (1:G)
  simpa only [one_smul,hn x] using h

/-- An invariant quotient-L² representative supplies an ambient L² seed
on every compact set by multiplying by the actual normalized orbit weight. -/
theorem compact_weighted_seed_memLp {G A : Type*} [Group G] [Countable G]
    [TopologicalSpace A] [MeasurableSpace A] [MulAction G A]
    [ProperlyDiscontinuousSMul G A]
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (f : A → ℂ) (hf : Measurable f) (hinv : ∀ g : G, ∀ x, f (g•x)=f x)
    (hL : MemLp f 2 (μ.withDensity ρ)) (K : Set A) (hK : IsCompact K)
    (hKm : MeasurableSet K) :
    MemLp (K.indicator (fun x => ((ρ x).toReal:ℂ)*f x)) 2 μ := by
  have hloc := invariant_memLp_restrict_compact μ hmp ρ hρ hn f hf hinv hL K hK hKm
  apply (memLp_indicator_iff_restrict hKm).mpr
  apply hloc.mono ((Complex.continuous_ofReal.measurable.comp hρ.ennreal_toReal).mul hf).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖((ρ x).toReal:ℂ)*f x‖≤‖f x‖
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact (ENNReal.toReal_mono ENNReal.one_ne_top (normalized_orbit_weight_le_one ρ hn x)).trans_eq
    ENNReal.toReal_one

/-- The literal compact seed periodizes to the retained orbit fraction
times the original invariant representative. -/
theorem poincare_compact_weighted_seed {G A : Type*} [Group G] [MulAction G A]
    (ρ : A → ℝ≥0∞) (f : A → ℂ) (hinv : ∀ g : G, ∀ x, f (g•x)=f x)
    (K : Set A) (x : A) :
    poincareSum (G := G) (K.indicator (fun y => ((ρ y).toReal:ℂ)*f y)) x=
      (orbitCutoff (G := G) ρ K x:ℂ)*f x := by
  classical
  change (∑' g : G, K.indicator (fun y => ((ρ y).toReal:ℂ)*f y) (g•x))=_
  rw [orbitCutoff,Complex.ofReal_tsum,← tsum_mul_right]
  apply tsum_congr
  intro g
  by_cases hx : g•x∈K
  · simp [hx,hinv g x]
  · simp [hx]

#print axioms compact_weighted_seed_memLp
#print axioms poincare_compact_weighted_seed

end QuantitativeMaass
