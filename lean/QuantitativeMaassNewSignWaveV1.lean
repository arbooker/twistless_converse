module

public import QuantitativeMaassPacketWaveCommuteV1
public import QuantitativeMaassCompletedNewSignPacketV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace QuantitativeMaass

theorem quotientNormalizerPullback_wave (N : ℕ) (g : quotientNormalizerGroup N) (t : ℝ) :
    Commute (quotientNormalizerPullback N g).toContinuousLinearMap (Wave.shiftedQuotientWave N t) := by
  apply timePacket_commuting_wave N _ _ t
  intro f hf he hc hr R hR hs
  apply ContinuousLinearMap.ext
  intro x
  exact quotientNormalizerPullback_timePacket N g f hf he hc hr R hR hs x

/-- The actual completed new/sign projection commutes with the unsmoothed
wave because the genuine packets preserve its range and are self-adjoint. -/
theorem completedNewSignProjection_wave (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (t : ℝ) :
    Commute (completedNewSignSpace N hN χ).starProjection (Wave.shiftedQuotientWave N t) := by
  apply timePacket_commuting_wave N _ _ t
  intro f hf he hc hr R hR hs
  apply invariantSpace_projection_commute
  · exact Wave.shiftedQuotientWavePacket_isSelfAdjoint N f _ hr
  · intro x hx
    exact completedNewSignSpace_timePacket N hN χ f hf he hc hr R hR hs x hx

#print axioms quotientNormalizerPullback_wave
#print axioms completedNewSignProjection_wave

end QuantitativeMaass
