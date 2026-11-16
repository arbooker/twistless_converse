module

public import QuantitativeMaassPoincareFixedSupportV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

/-- Periodization is linear on seeds with compact support; every series
occurring here is actually finite at each point. -/
theorem poincareSum_sub_compact {G A : Type*} [Group G] [TopologicalSpace A]
    [MulAction G A] [ProperlyDiscontinuousSMul G A]
    (K : Set A) (hK : IsCompact K) (f g : A → ℂ)
    (hf : Function.support f ⊆ K) (hg : Function.support g ⊆ K) :
    poincareSum (G := G) (f-g)=poincareSum (G := G) f-poincareSum (G := G) g := by
  have hs (u : A → ℂ) (hu : Function.support u ⊆ K) (x : A) :
      Summable (fun a : G => u (a•x)) := by
    apply summable_of_hasFiniteSupport
    exact (compact_orbit_point_finite (G := G) K hK x).subset (fun _ h => hu h)
  funext x
  exact (hs f hf x).tsum_sub (hs g hg x)

/-- Compactly supported measurable L² seeds periodize into actual quotient
L². Continuity of the seed is not assumed. -/
theorem compact_poincare_memLp {G A : Type*} [Group G] [Countable G]
    [TopologicalSpace A] [MeasurableSpace A] [MulAction G A]
    [ProperlyDiscontinuousSMul G A]
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (K : Set A) (hK : IsCompact K) (f : A → ℂ) (hf : Measurable f)
    (hs : Function.support f ⊆ K) (hL : MemLp f 2 μ) :
    MemLp (poincareSum (G := G) f) 2 (μ.withDensity ρ) := by
  have hm : Measurable (poincareSum (G := G) f) :=
    Measurable.tsum (fun g : G => hf.comp (hmp g).measurable)
  obtain ⟨M,hM⟩ := compact_poincare_uniform_energy_bound μ hmp ρ hρ hn K hK
  have hi := (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mp hL
  have hfin : (∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ)<∞ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hi.2
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  refine ⟨(hm.norm.pow_const 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mpr
  exact lt_of_le_of_lt (hM f hf hs) (ENNReal.mul_lt_top (by simp) hfin)

#print axioms poincareSum_sub_compact
#print axioms compact_poincare_memLp

end QuantitativeMaass
