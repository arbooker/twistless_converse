module

public import QuantitativeMaassPoincareOverlapV1
public import QuantitativeMaassPoincareUnfoldV1
public import QuantitativeMaassAutomorphicL2V1
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace QuantitativeMaass

/-- Compact continuous seeds produce actual quotient L² automorphic
functions. Proper-discontinuity overlap and Tonelli unfolding establish the
norm bound; quotient integrability is not an input. -/
theorem poincareSum_memLp {G A : Type*} [Group G] [Countable G]
    [TopologicalSpace A] [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]
    [MulAction G A] [ProperlyDiscontinuousSMul G A] [ContinuousConstSMul G A]
    (μ : Measure A) [IsFiniteMeasureOnCompacts μ]
    (hmp : ∀ g : G, MeasurePreserving (fun x : A => g • x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g • x)=1)
    (f : A → ℂ) (hc : Continuous f) (hf : HasCompactSupport f) :
    MemLp (poincareSum (G := G) f) 2 (μ.withDensity ρ) := by
  have hfL : MemLp f 2 μ := hc.memLp_of_hasCompactSupport hf
  have hfI := (memLp_two_iff_integrable_sq_norm hfL.aestronglyMeasurable).mp hfL
  have hfinite : (∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ)<∞ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hfI.2
  have hm : Measurable (fun x => ENNReal.ofReal (‖f x‖^2)) :=
    (hc.norm.pow 2).measurable.ennreal_ofReal
  obtain ⟨M,hM⟩ := compact_seed_poincare_square_bound (G := G) f hf
  have hpoint (x : A) : ENNReal.ofReal (‖poincareSum (G := G) f x‖^2)≤
      (M:ℝ≥0∞)*∑' g : G, ENNReal.ofReal (‖f (g•x)‖^2) := by
    have hs : Summable (fun g : G => ‖f (g•x)‖^2) := by
      apply summable_of_hasFiniteSupport
      exact (compact_seed_point_support (G := G) f hf x).subset (fun g hg => by
        contrapose! hg
        have hz : f (g•x)=0 := by simpa only [Function.mem_support,not_not] using hg
        simp [hz])
    have hb := ENNReal.ofReal_le_ofReal (hM x)
    rwa [ENNReal.ofReal_mul (Nat.cast_nonneg M),ENNReal.ofReal_natCast,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs] at hb
  have hbound : (∫⁻ x, ENNReal.ofReal (‖poincareSum (G := G) f x‖^2) ∂μ.withDensity ρ)≤
      (M:ℝ≥0∞)*(∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ) := by
    calc
      _ ≤ ∫⁻ x, (M:ℝ≥0∞)*∑' g : G, ENNReal.ofReal (‖f (g•x)‖^2) ∂μ.withDensity ρ :=
        lintegral_mono hpoint
      _ = _ := by
        rw [lintegral_const_mul' _ _ (by simp),
          lintegral_poincare_unfold μ hmp ρ hρ hn _ hm]
  have hp := poincareSum_continuous (G := G) f hf hc
  apply (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mpr
  refine ⟨(hp.norm.pow 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mpr
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top (by simp) hfinite)

/-- The constructed series is a pointwise invariant representative in the
already defined quotient Hilbert space, for the actual whole acting group. -/
theorem poincareSum_representative {G A : Type*} [Group G] [Countable G]
    [TopologicalSpace A] [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]
    [MulAction G A] [ProperlyDiscontinuousSMul G A] [ContinuousConstSMul G A]
    (μ : Measure A) [IsFiniteMeasureOnCompacts μ]
    (hmp : ∀ g : G, MeasurePreserving (fun x : A => g • x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g • x)=1)
    (f : A → ℂ) (hc : Continuous f) (hf : HasCompactSupport f) :
    poincareSum (G := G) f ∈ AutomorphicL2.representatives (⊤ : Subgroup G) (μ.withDensity ρ) := by
  refine ⟨(poincareSum_continuous (G := G) f hf hc).measurable,?_,
    poincareSum_memLp μ hmp ρ hρ hn f hc hf⟩
  intro g x
  exact poincareSum_invariant f g.val x

#print axioms poincareSum_memLp
#print axioms poincareSum_representative

end QuantitativeMaass
