module

public import QuantitativeMaassPoincareComplexUnfoldV1
public import QuantitativeMaassQuotientLocalL2V1
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.Compactness.SigmaCompact

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

/-- The fraction of normalized orbit mass retained by a compact seed. -/
def orbitCutoff {G A : Type*} [Group G] [MulAction G A]
    (ρ : A → ℝ≥0∞) (K : Set A) (x : A) : ℝ :=
  ∑' g : G, K.indicator (fun y => (ρ y).toReal) (g•x)

theorem normalized_orbit_real_sum {G A : Type*} [Group G] [MulAction G A]
    (ρ : A → ℝ≥0∞) (hn : ∀ x, ∑' g : G, ρ (g•x)=1) (x : A) :
    Summable (fun g : G => (ρ (g•x)).toReal) ∧
      (∑' g : G, (ρ (g•x)).toReal)=1 := by
  have ht : (∑' g : G, ρ (g•x))≠∞ := by rw [hn]; exact ENNReal.one_ne_top
  refine ⟨ENNReal.summable_toReal ht,?_⟩
  rw [← ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top ht),hn,ENNReal.toReal_one]

theorem orbitCutoff_mem_Icc {G A : Type*} [Group G] [MulAction G A]
    (ρ : A → ℝ≥0∞) (hn : ∀ x, ∑' g : G, ρ (g•x)=1) (K : Set A) (x : A) :
    orbitCutoff (G := G) ρ K x∈Icc (0:ℝ) 1 := by
  classical
  obtain ⟨hs,he⟩ := normalized_orbit_real_sum ρ hn x
  have hb (g : G) : ‖K.indicator (fun y => (ρ y).toReal) (g•x)‖≤(ρ (g•x)).toReal := by
    by_cases hx : g•x∈K
    · simp [hx,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    · simp [hx,ENNReal.toReal_nonneg]
  have hi : Summable (fun g : G => K.indicator (fun y => (ρ y).toReal) (g•x)) :=
    hs.of_norm_bounded hb
  refine ⟨tsum_nonneg (fun g => ?_),?_⟩
  · exact Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) _
  · change (∑' g : G, K.indicator (fun y => (ρ y).toReal) (g•x))≤1
    rw [← he]
    exact hi.tsum_le_tsum (fun g => (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hb g)) hs

/-- Compact exhaustion captures all normalized orbit mass. The infinite
series limit is justified by dominated convergence for summable series. -/
theorem orbitCutoff_tendsto_one {G A : Type*} [Group G] [MulAction G A]
    [TopologicalSpace A] (ρ : A → ℝ≥0∞)
    (hn : ∀ x, ∑' g : G, ρ (g•x)=1) (K : CompactExhaustion A) (x : A) :
    Tendsto (fun n => orbitCutoff (G := G) ρ (K n) x) atTop (𝓝 1) := by
  classical
  obtain ⟨hs,he⟩ := normalized_orbit_real_sum ρ hn x
  have ht := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (g := fun g : G => (ρ (g•x)).toReal) (f := fun (n : ℕ) (g : G) =>
    (K n).indicator (fun y => (ρ y).toReal) (g•x)) hs
  have hc : ∀ g : G, Tendsto (fun n => (K n).indicator (fun y => (ρ y).toReal) (g•x))
      atTop (𝓝 ((ρ (g•x)).toReal)) := by
    intro g
    obtain ⟨n,hn⟩ := K.exists_mem (g•x)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hm
    exact (Set.indicator_of_mem (K.subset hm hn) (fun y => (ρ y).toReal)).symm
  have hb : ∀ᶠ n in atTop, ∀ g : G,
      ‖(K n).indicator (fun y => (ρ y).toReal) (g•x)‖≤(ρ (g•x)).toReal := by
    apply Filter.Eventually.of_forall
    intro n g
    by_cases hx : g•x∈K n
    · simp [hx,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    · simp [hx,ENNReal.toReal_nonneg]
  simpa only [he,orbitCutoff] using ht hc hb

/-- The omitted orbit mass tends to zero in the actual quotient L² energy,
uniformly dominated by the given representative's square norm. -/
theorem orbitCutoff_energy_tendsto_zero {G A : Type*} [Group G] [Countable G]
    [MulAction G A] [TopologicalSpace A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (K : CompactExhaustion A) (f : A → ℂ) (hf : Measurable f)
    (hL : MemLp f 2 (μ.withDensity ρ)) :
    Tendsto (fun n => ∫ x, ‖f x‖^2*(1-orbitCutoff (G := G) ρ (K n) x)^2
      ∂μ.withDensity ρ) atTop (𝓝 0) := by
  have hm (n : ℕ) : Measurable (orbitCutoff (G := G) ρ (K n)) :=
    Measurable.tsum (fun g : G => ((hρ.ennreal_toReal).indicator
      (K.isCompact n).isClosed.measurableSet).comp (hmp g).measurable)
  have hi : Integrable (fun x => ‖f x‖^2) (μ.withDensity ρ) :=
    (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mp hL
  have ht := tendsto_integral_of_dominated_convergence (μ := μ.withDensity ρ)
    (F := fun n x => ‖f x‖^2*(1-orbitCutoff (G := G) ρ (K n) x)^2)
    (f := fun _ => (0:ℝ)) (fun x => ‖f x‖^2)
    (fun n => ((hf.norm.pow_const 2).mul ((measurable_const.sub (hm n)).pow_const 2)).aestronglyMeasurable)
    hi ?_ ?_
  · simpa only [integral_zero] using ht
  · intro n
    apply Filter.Eventually.of_forall
    intro x
    obtain ⟨h0,h1⟩ := orbitCutoff_mem_Icc ρ hn (K n) x
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    apply mul_le_of_le_one_right (sq_nonneg _)
    nlinarith
  · apply Filter.Eventually.of_forall
    intro x
    have hc := orbitCutoff_tendsto_one ρ hn K x
    simpa using (tendsto_const_nhds (x := ‖f x‖^2)).mul
      (((tendsto_const_nhds (x := (1:ℝ))).sub hc).pow 2)

#print axioms orbitCutoff_tendsto_one
#print axioms orbitCutoff_energy_tendsto_zero

end QuantitativeMaass
