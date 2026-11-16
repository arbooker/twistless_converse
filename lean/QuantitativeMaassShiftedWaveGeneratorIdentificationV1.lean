module

public import QuantitativeMaassShiftedWaveGeneratorV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem shiftedRangeTimeDifference_symmetric (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (hi : Function.Injective A) (t : ℝ) (x y : H) :
    inner ℂ (shiftedRangeTimeDifference A t x) y=
      inner ℂ x (shiftedRangeTimeDifference A t y) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (shiftedRangeCosine_isSelfAdjoint A hA hd hi t) x y
  change inner ℂ (shiftedRangeCosine A t x) y=inner ℂ x (shiftedRangeCosine A t y) at hs
  unfold shiftedRangeTimeDifference
  simp only [← algebraMap_smul ℂ (2/t^2),RCLike.algebraMap_eq_ofReal,inner_smul_real_left,
    inner_smul_real_right,inner_sub_left,inner_sub_right,hs]

theorem shiftedQuotientTimeDifference_symmetric (N : ℕ) (t : ℝ) (x y : AutomorphicSpace N) :
    inner ℂ (shiftedQuotientTimeDifference N t x) y=
      inner ℂ x (shiftedQuotientTimeDifference N t y) :=
  shiftedRangeTimeDifference_symmetric _ (friedrichsResolvent_isSelfAdjoint N)
    (friedrichsResolvent_denseRange N) (friedrichsResolvent_injective N) t x y

omit [CompleteSpace H] in
private theorem quarter_graph_cancel (f g x y : H)
    (h : inner ℂ ((1/4 : ℂ) • f-g) x=inner ℂ f ((1/4 : ℂ) • x-y)) :
    inner ℂ g x=inner ℂ f y := by
  simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    map_div₀,map_one,map_ofNat] at h
  exact sub_right_inj.mp h

/-- The shifted wave generator graph is exactly 1/4 minus the actual
Friedrichs graph. The converse uses the already proved adjoint-graph equality. -/
theorem shiftedQuotientWave_generator_iff (N : ℕ) (x y : AutomorphicSpace N) :
    FriedrichsGraph N x y ↔
      Tendsto (fun t => shiftedQuotientTimeDifference N t x) (𝓝[≠] 0)
        (𝓝 ((1/4 : ℂ) • x-y)) := by
  constructor
  · exact shiftedQuotientWave_generator N
  · intro h
    apply (friedrichsGraph_iff_adjoint N x y).mpr
    intro f g hfg
    have hf := shiftedQuotientWave_generator N hfg
    have hl := hf.inner (𝕜 := ℂ) (tendsto_const_nhds (x := x))
    have hr := (tendsto_const_nhds (x := f)).inner (𝕜 := ℂ) h
    have he : (fun t => inner ℂ (shiftedQuotientTimeDifference N t f) x) =ᶠ[𝓝[≠] 0]
        (fun t => inner ℂ f (shiftedQuotientTimeDifference N t x)) :=
      Filter.Eventually.of_forall (fun t => shiftedQuotientTimeDifference_symmetric N t f x)
    have hlim := tendsto_nhds_unique (hl.congr' he) hr
    exact quarter_graph_cancel f g x y hlim

#print axioms shiftedQuotientWave_generator_iff

end QuantitativeMaass.Wave
