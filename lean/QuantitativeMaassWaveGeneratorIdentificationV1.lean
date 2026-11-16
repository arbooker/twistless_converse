module

public import QuantitativeMaassWaveGeneratorV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rangeTimeDifference_symmetric (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (hi : Function.Injective A) (t : ℝ) (x y : H) :
    inner ℂ (rangeTimeDifference A t x) y=inner ℂ x (rangeTimeDifference A t y) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (rangeCosine_isSelfAdjoint A hA hd hi t) x y
  change inner ℂ (rangeCosine A t x) y=inner ℂ x (rangeCosine A t y) at hs
  unfold rangeTimeDifference
  simp only [← algebraMap_smul ℂ (2/t^2),RCLike.algebraMap_eq_ofReal,inner_smul_real_left,
    inner_smul_real_right,inner_sub_left,inner_sub_right,hs]

theorem quotientTimeDifference_symmetric (N : ℕ) (t : ℝ) (x y : AutomorphicSpace N) :
    inner ℂ (quotientTimeDifference N t x) y=inner ℂ x (quotientTimeDifference N t y) :=
  rangeTimeDifference_symmetric _ (friedrichsResolvent_isSelfAdjoint N)
    (friedrichsResolvent_denseRange N) (friedrichsResolvent_injective N) t x y

/-- Exact equality of the cosine-family generator graph with the actual
Friedrichs Laplacian graph. The reverse implication uses the proved full
adjoint-graph equality, not an assumed essential self-adjointness theorem. -/
theorem quotientWave_generator_iff (N : ℕ) (x y : AutomorphicSpace N) :
    FriedrichsGraph N x y ↔
      Tendsto (fun t => quotientTimeDifference N t x) (𝓝[≠] 0) (𝓝 (-y)) := by
  constructor
  · exact quotientWave_generator N
  · intro h
    apply (friedrichsGraph_iff_adjoint N x y).mpr
    intro f g hfg
    have hf := quotientWave_generator N hfg
    have hl := hf.inner (𝕜 := ℂ) (tendsto_const_nhds (x := x))
    have hr := (tendsto_const_nhds (x := f)).inner (𝕜 := ℂ) h
    have he : (fun t => inner ℂ (quotientTimeDifference N t f) x) =ᶠ[𝓝[≠] 0]
        (fun t => inner ℂ f (quotientTimeDifference N t x)) :=
      Filter.Eventually.of_forall (fun t => quotientTimeDifference_symmetric N t f x)
    have hlim := tendsto_nhds_unique (hl.congr' he) hr
    simp only [inner_neg_left,inner_neg_right] at hlim
    exact neg_injective hlim

#print axioms quotientWave_generator_iff

end QuantitativeMaass.Wave
