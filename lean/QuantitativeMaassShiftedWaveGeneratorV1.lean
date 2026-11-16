module

public import QuantitativeMaassShiftedWaveStrongLimitV1
public import QuantitativeMaassShiftedWaveDomainV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def shiftedRangeTimeDifference (A : H →L[ℂ] H) (t : ℝ) (x : H) : H :=
  (2/t^2 : ℝ) • (shiftedRangeCosine A t x-x)

theorem shiftedRangeTimeDifference_tendsto (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (hd : DenseRange A) (z : H) :
    Tendsto (fun t => shiftedRangeTimeDifference A t (A z)) (𝓝[≠] 0)
      (𝓝 (-(z-(5/4 : ℝ) • A z))) := by
  have h := (shiftedOneResolventGeneratorError_tendsto A hp hn hd z).sub_const
    (z-(5/4 : ℝ) • A z)
  have h' : Tendsto
      (fun t => shiftedOneResolventGeneratorError A t z-(z-(5/4 : ℝ) • A z)) (𝓝[≠] 0)
      (𝓝 (-(z-(5/4 : ℝ) • A z))) := by simpa only [zero_sub] using h
  apply h'.congr'
  filter_upwards with t
  change (shiftedOneResolventDifference A t z+(z-(5/4 : ℝ) • A z))-
    (z-(5/4 : ℝ) • A z)=shiftedRangeTimeDifference A t (A z)
  rw [add_sub_cancel_right,shiftedOneResolventDifference_formula A hp.isSelfAdjoint]
  unfold shiftedRangeTimeDifference
  rw [shiftedRangeCosine_range A hp.isSelfAdjoint hd]
  rfl

theorem shiftedRangeTimeDifference_graph (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (hd : DenseRange A) {x y : H} (hxy : A (x+y)=x) :
    Tendsto (fun t => shiftedRangeTimeDifference A t x) (𝓝[≠] 0)
      (𝓝 ((1/4 : ℂ) • x-y)) := by
  have h := shiftedRangeTimeDifference_tendsto A hp hn hd (x+y)
  rw [hxy] at h
  have he : -(x+y-(5/4 : ℝ) • x)=(1/4 : ℂ) • x-y := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal]
    push_cast
    module
  rwa [he] at h

/-- The centered second time difference of the actual shifted wave. -/
def shiftedQuotientTimeDifference (N : ℕ) (t : ℝ) (x : AutomorphicSpace N) :
    AutomorphicSpace N := shiftedRangeTimeDifference (friedrichsResolvent N) t x

/-- The shifted wave has generator 1/4 minus the Friedrichs Laplacian on its
whole operator domain, including exceptional spectral components. -/
theorem shiftedQuotientWave_generator (N : ℕ) {x y : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) :
    Tendsto (fun t => shiftedQuotientTimeDifference N t x) (𝓝[≠] 0)
      (𝓝 ((1/4 : ℂ) • x-y)) := by
  exact shiftedRangeTimeDifference_graph (friedrichsResolvent N)
    (friedrichsResolvent_isPositive N) (friedrichsResolvent_opNorm_le N)
    (friedrichsResolvent_denseRange N) hxy

theorem shiftedQuotientWave_generator_poincareSeed (N : ℕ) (u : SmoothUpperSeed) :
    Tendsto (fun t => shiftedQuotientTimeDifference N t (poincareSeedVector N u)) (𝓝[≠] 0)
      (𝓝 ((1/4 : ℂ) • poincareSeedVector N u-poincareSeedVector N u.laplacian)) :=
  shiftedQuotientWave_generator N (friedrichsGraph_poincareSeed N u)

#print axioms shiftedQuotientWave_generator
#print axioms shiftedQuotientWave_generator_poincareSeed

end QuantitativeMaass.Wave
