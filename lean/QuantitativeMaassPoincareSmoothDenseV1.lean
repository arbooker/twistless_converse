module

public import QuantitativeMaassPoincareContinuousDenseV1
public import QuantitativeMaassPoincareUniformSmoothV1
public import QuantitativeMaassPoincareUniformNormV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped ENNReal Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Actual smooth Cartesian seeds, restricted to the upper half plane and
then periodized. There is no built-in density hypothesis. -/
def smoothSeedClasses {G : Type*} [Group G] [MulAction G ℍ]
    (ν : Measure ℍ) : Set (Lp ℂ 2 ν) :=
  {v | ∃ u : Point → ℂ, ContDiff ℝ ∞ u ∧ HasCompactSupport (upperFunction u) ∧
    ∃ hP : MemLp (poincareSum (G := G) (upperFunction u)) 2 ν,
      v=hP.toLp (poincareSum (G := G) (upperFunction u))}

theorem continuousSeedClasses_subset_closure_smoothSeedClasses {G : Type*}
    [Group G] [Countable G] [MulAction G ℍ]
    [ProperlyDiscontinuousSMul G ℍ] [ContinuousConstSMul G ℍ]
    (μ : Measure ℍ) [μ.Regular]
    (hmp : ∀ g : G, MeasurePreserving (fun x : ℍ => g•x) μ μ)
    (ρ : ℍ → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1) :
    continuousSeedClasses (G := G) μ (μ.withDensity ρ) ⊆
      closure (smoothSeedClasses (G := G) (μ.withDensity ρ)) := by
  rintro v ⟨f,hf,hc,_,hP,rfl⟩
  obtain ⟨C,hC,hbound⟩ := compact_poincare_uniform_norm_bound μ hmp ρ hρ hn (tsupport f) hc
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let S : ℝ := (μ (tsupport f)).toReal+1
  have hS : 0<S := by dsimp [S]; positivity
  let δ : ℝ := ε/(2*C*S)
  have hδ : 0<δ := div_pos hε (mul_pos (mul_pos (by norm_num) hC) hS)
  obtain ⟨u,hu,-,-,huc,hus,ha⟩ := upper_seed_uniform_smooth_approx f hf hc δ hδ
  let g := upperFunction u
  have hg : Continuous g := hu.continuous.comp upperCoordinates_openEmbedding.continuous
  let hgP := poincareSum_memLp μ hmp ρ hρ hn g hg huc
  refine ⟨hgP.toLp (poincareSum (G := G) g),⟨u,hu,huc,hgP,rfl⟩,?_⟩
  have hgs : Function.support g ⊆ tsupport f := hus.trans (subset_tsupport f)
  have hs : Function.support (f-g) ⊆ tsupport f := by
    intro x hx
    by_cases hfx : f x=0
    · apply hgs
      intro hgx
      exact hx (by simp [hfx,hgx])
    · exact subset_tsupport f hfx
  let hfL : MemLp f 2 μ := hf.memLp_of_hasCompactSupport hc
  let hgL : MemLp g 2 μ := hg.memLp_of_hasCompactSupport huc
  let hd := hfL.sub hgL
  let hdP := compact_poincare_memLp μ hmp ρ hρ hn (tsupport f) hc (f-g)
    (hf.measurable.sub hg.measurable) hs hd
  have he : hP.toLp (poincareSum (G := G) f)-hgP.toLp (poincareSum (G := G) g)=
      hdP.toLp (poincareSum (G := G) (f-g)) := by
    apply Lp.ext
    filter_upwards [hP.coeFn_toLp,hgP.coeFn_toLp,hdP.coeFn_toLp,
      Lp.coeFn_sub (hP.toLp (poincareSum (G := G) f))
        (hgP.toLp (poincareSum (G := G) g))] with x hf hg hd hsub
    rw [hsub]
    simp only [Pi.sub_apply,hf,hg,hd]
    rw [poincareSum_sub_compact (tsupport f) hc f g (subset_tsupport f) hgs]
    rfl
  have hdsmall : ‖hd.toLp (f-g)‖≤δ*S := by
    apply compact_uniform_l2_norm_bound μ (tsupport f) isClosed_closure.measurableSet
      hc.measure_lt_top.ne (f-g) hd hs δ hδ.le
    intro x
    change ‖f x-upperFunction u x‖≤δ
    rw [norm_sub_rev]
    exact (ha x).le
  calc
    _ = ‖hdP.toLp (poincareSum (G := G) (f-g))‖ := by rw [dist_eq_norm,he]
    _ ≤ C*‖hd.toLp (f-g)‖ := hbound (f-g) (hf.measurable.sub hg.measurable) hs hd
    _ ≤ C*(δ*S) := mul_le_mul_of_nonneg_left hdsmall hC.le
    _ = ε/2 := by dsimp [δ]; field_simp
    _ < ε := by linarith

/-- Smooth compact Poincaré seeds are dense in the actual completed
automorphic Hilbert space. Compact exhaustion, both approximation steps,
and all operator norm estimates are proved, not assumed. -/
theorem automorphic_space_subset_closure_smoothSeedClasses {G : Type*}
    [Group G] [Countable G] [MulAction G ℍ]
    [ProperlyDiscontinuousSMul G ℍ] [ContinuousConstSMul G ℍ]
    (μ : Measure ℍ) [μ.Regular]
    (hmp : ∀ g : G, MeasurePreserving (fun x : ℍ => g•x) μ μ)
    (ρ : ℍ → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1) :
    (AutomorphicL2.space (⊤ : Subgroup G) (μ.withDensity ρ) : Set (Lp ℂ 2 (μ.withDensity ρ))) ⊆
      closure (smoothSeedClasses (G := G) (μ.withDensity ρ)) :=
  (automorphic_space_subset_closure_continuousSeedClasses μ hmp ρ hρ hn
    (default : CompactExhaustion ℍ)).trans
    (closure_minimal (continuousSeedClasses_subset_closure_smoothSeedClasses μ hmp ρ hρ hn)
      isClosed_closure)

#print axioms automorphic_space_subset_closure_smoothSeedClasses

end QuantitativeMaass
