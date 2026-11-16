module

public import QuantitativeMaassWaveStrongLimitV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def rangeTimeDifference (A : H →L[ℂ] H) (t : ℝ) (x : H) : H :=
  (2/t^2 : ℝ) • (rangeCosine A t x-x)

theorem rangeTimeDifference_tendsto (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (hd : DenseRange A) (z : H) :
    Tendsto (fun t => rangeTimeDifference A t (A z)) (𝓝[≠] 0) (𝓝 (-(z-A z))) := by
  have h := (oneResolventGeneratorError_tendsto A hp hn hd z).sub_const (z-A z)
  have h' : Tendsto (fun t => oneResolventGeneratorError A t z-(z-A z)) (𝓝[≠] 0)
      (𝓝 (-(z-A z))) := by simpa only [zero_sub] using h
  apply h'.congr'
  filter_upwards with t
  change (oneResolventDifference A t z+(z-A z))-(z-A z)=rangeTimeDifference A t (A z)
  rw [add_sub_cancel_right,oneResolventDifference_formula A hp.isSelfAdjoint]
  unfold rangeTimeDifference
  rw [rangeCosine_range A hp.isSelfAdjoint hd]
  rfl

/-- The literal second time difference for the constructed quotient wave,
using the fixed real scalar restriction of the complex Hilbert structure. -/
def quotientTimeDifference (N : ℕ) (t : ℝ) (x : AutomorphicSpace N) : AutomorphicSpace N :=
  rangeTimeDifference (friedrichsResolvent N) t x

/-- Full-domain generator identity: every pair in the actual quotient
Friedrichs graph has the correct small-time wave limit. No smoothness or
spectral-resolution hypothesis is added. -/
theorem quotientWave_generator (N : ℕ) {x y : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) :
    Tendsto (fun t => quotientTimeDifference N t x) (𝓝[≠] 0) (𝓝 (-y)) := by
  have h := rangeTimeDifference_tendsto (friedrichsResolvent N)
    (friedrichsResolvent_isPositive N) (friedrichsResolvent_opNorm_le N)
    (friedrichsResolvent_denseRange N) (x+y)
  rw [hxy] at h
  have he : x+y-x=y := by abel
  rw [he] at h
  exact h

theorem quotientWave_generator_poincareSeed (N : ℕ) (u : SmoothUpperSeed) :
    Tendsto (fun t => quotientTimeDifference N t (poincareSeedVector N u)) (𝓝[≠] 0)
      (𝓝 (-(poincareSeedVector N u.laplacian))) :=
  quotientWave_generator N (friedrichsGraph_poincareSeed N u)

#print axioms quotientWave_generator
#print axioms quotientWave_generator_poincareSeed

end QuantitativeMaass.Wave
