module

public import QuantitativeMaassNormalizerRadialV1
public import QuantitativeMaassCompletedGeneratorMetricV1
public import QuantitativeMaassCylinderTimePacketV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem quotientNormalizerPullback_coshWavePacket (N : ℕ) (g : quotientNormalizerGroup N)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (x : AutomorphicSpace N) :
    quotientNormalizerPullback N g (coshWavePacket N F hF R hR hs x)=
      coshWavePacket N F hF R hR hs (quotientNormalizerPullback N g x) := by
  rw [←AllLevel.abelKernelOperator_eq_coshWavePacket N F hF hc hr R hR hs]
  exact quotientNormalizerPullback_radial N g (abelProfile F) (abelProfile_smooth F hF hc)
    R hR (abelProfile_support F _ hs) x

theorem quotientNormalizerPullback_timePacket (N : ℕ) (g : quotientNormalizerGroup N)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : AutomorphicSpace N) :
    quotientNormalizerPullback N g
      (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) x)=
      Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc)
        (quotientNormalizerPullback N g x) := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let D (n : ℕ) := Wave.shiftedQuotientWavePacket N (radialShiftTime f (a n))
    (compactSmoothWaveWeight _ (radialShiftTime_smooth f hf he hc (a n) (ha n))
      (radialShiftTime_compact f R hR hs (a n) (ha n)))
  have hD : Tendsto D atTop
      (𝓝 (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc))) :=
    radialShiftTime_packet_tendsto atTop N f hf he hc R hR hs a ha ha0
  have hleft := (quotientNormalizerPullback N g).continuous.tendsto _ |>.comp
    (((ContinuousLinearMap.apply ℂ (AutomorphicSpace N) x).continuous.tendsto _).comp hD)
  have hright := ((ContinuousLinearMap.apply ℂ (AutomorphicSpace N)
    (quotientNormalizerPullback N g x)).continuous.tendsto _).comp hD
  have heq (n : ℕ) : quotientNormalizerPullback N g (D n x)=
      D n (quotientNormalizerPullback N g x) :=
    quotientNormalizerPullback_coshWavePacket N g (radialShiftApprox (evenCoshLift f) (a n))
      (radialShiftApprox_smooth _ (evenCoshLift_smoothOn f hf he hc) _ (ha n))
      (radialShiftApprox_compact _ (Real.cosh R) (evenCoshLift_zero_above f R hR hs) _ (ha n))
      (radialShiftApprox_real _ (evenCoshLift_real f hr) (a n)) R hR
      (radialShiftApprox_upper_support _ (Real.cosh R) (evenCoshLift_zero_above f R hR hs) _ (ha n)) x
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall (fun n => (heq n).symm)))

/-- All simultaneous generator eigenspaces are invariant under the actual
spectral packet, with arbitrary prescribed generator eigenvalues. -/
theorem completedGeneratorSpace_timePacket (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : AutomorphicSpace N) (hx : x∈completedGeneratorSpace N hN χ) :
    Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) x∈
      completedGeneratorSpace N hN χ := by
  intro i
  rw [quotientNormalizerPullback_timePacket N (admissibleGeneratorLift N hN i)
    f hf he hc hr R hR hs,hx i,map_smul]

#print axioms quotientNormalizerPullback_coshWavePacket
#print axioms quotientNormalizerPullback_timePacket
#print axioms completedGeneratorSpace_timePacket

end QuantitativeMaass
