module

public import QuantitativeMaassWeightedRadialIntertwiningV1
public import QuantitativeMaassCylinderTimePacketV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The weighted embedding intertwines every real even smooth compact
time packet with the genuine shifted quotient wave packet. -/
theorem weightedQuotientEmbedding_timePacket (N : ℕ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) (x : AutomorphicSpace N) :
    cylinderCappedTimePacket f hf he hc hr R hR hs ε hε v (weightedQuotientEmbedding N hε hv x)=
      weightedQuotientEmbedding N hε hv
        (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) x) := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F (n : ℕ) := radialShiftApprox (evenCoshLift f) (a n)
  have hF (n : ℕ) := radialShiftApprox_smooth _ (evenCoshLift_smoothOn f hf he hc) _ (ha n)
  have hFc (n : ℕ) := radialShiftApprox_compact _ (Real.cosh R)
    (evenCoshLift_zero_above f R hR hs) _ (ha n)
  have hFr (n : ℕ) := radialShiftApprox_real _ (evenCoshLift_real f hr) (a n)
  have hFs (n : ℕ) := radialShiftApprox_upper_support _ (Real.cosh R)
    (evenCoshLift_zero_above f R hR hs) _ (ha n)
  let B (n : ℕ) := cylinderCappedRadialOperator (abelProfile (F n))
    (abelProfile_smooth _ (hF n) (hFc n)) R hR (abelProfile_support _ _ (hFs n)) ε hε v
  let D (n : ℕ) := Wave.shiftedQuotientWavePacket N (radialShiftTime f (a n))
    (compactSmoothWaveWeight _ (radialShiftTime_smooth f hf he hc (a n) (ha n))
      (radialShiftTime_compact f R hR hs (a n) (ha n)))
  let J := weightedQuotientEmbedding N hε hv
  have hB : Tendsto B atTop (𝓝 (cylinderCappedTimePacket f hf he hc hr R hR hs ε hε v)) :=
    cylinderCappedTimePacket_shift_tendsto atTop f hf he hc hr R hR hs a ha ha0 ε hε v
  have hD : Tendsto D atTop
      (𝓝 (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc))) :=
    radialShiftTime_packet_tendsto atTop N f hf he hc R hR hs a ha ha0
  have hleft := ((ContinuousLinearMap.apply ℂ (Lp ℂ 2 (quotientMeasure 0)) (J x)).continuous.tendsto _).comp hB
  have hright := J.continuous.tendsto _ |>.comp
    (((ContinuousLinearMap.apply ℂ (AutomorphicSpace N) x).continuous.tendsto _).comp hD)
  have heq (n : ℕ) : B n (J x)=J (D n x) :=
    weightedQuotientEmbedding_coshWavePacket N (F n) (hF n) (hFc n) (hFr n) R hR (hFs n) hε hv x
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Eventually.of_forall (fun n => (heq n).symm))

#print axioms weightedQuotientEmbedding_timePacket

end QuantitativeMaass
