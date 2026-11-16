module

public import QuantitativeMaassConjugationContinuityV1
public import QuantitativeMaassCylinderZeroModeV1
public import QuantitativeMaassRadialShiftLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The actual cylinder wave packet, expressed on strip L2. -/
def cylinderTimePacket (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Lp ℂ 2 (quotientMeasure 0) →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (AutomorphicSpace 0).subtypeL.comp
    ((Wave.shiftedQuotientWavePacket 0 f (compactSmoothWaveWeight f hf hc)).comp
      cylinderAutomorphic.toContinuousLinearMap)

/-- Exact agreement of the ambient spectral packet with Abel integration. -/
theorem cylinderTimePacket_cosh (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    cylinderTimePacket (coshTimeTest F) (hF.comp Real.contDiff_cosh)
      (coshTimeTest_compact F R hR hs)=
      (radialKernelData 0 (abelProfile F) (abelProfile_smooth F hF hc)
        R hR (abelProfile_support F _ hs)).operator := by
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun B : AutomorphicSpace 0 →L[ℂ] AutomorphicSpace 0 =>
    (B (cylinderAutomorphic v)).val)
    (AllLevel.abelKernelOperator_eq_coshWavePacket 0 F hF hc hr R hR hs).symm

/-- The smooth radial approximants converge on the entire translation
cylinder, without a finite-volume or nonzero-level assumption. -/
theorem cylinderTimePacket_shift_tendsto {ι : Type*} (L : Filter ι) [L.IsCountablyGenerated]
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a L (𝓝 0)) :
    Tendsto (fun i => cylinderTimePacket (radialShiftTime f (a i))
      (radialShiftTime_smooth f hf he hc (a i) (ha i))
      (radialShiftTime_compact f R hR hs (a i) (ha i))) L
      (𝓝 (cylinderTimePacket f hf hc)) := by
  have hcont : Continuous (fun B : AutomorphicSpace 0 →L[ℂ] AutomorphicSpace 0 =>
      (AutomorphicSpace 0).subtypeL.comp (B.comp cylinderAutomorphic.toContinuousLinearMap)) := by
    fun_prop
  exact hcont.tendsto _ |>.comp (radialShiftTime_packet_tendsto L 0 f hf he hc R hR hs a ha ha0)

/-- Finite propagation for the original smooth even packet follows from
its exact smooth Abel approximants and closedness of the band condition. -/
theorem cylinderTimePacket_band (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (ε : ℝ) (hε : 0<ε) (t : ℕ) :
    LogBands.HasBandPropagation (quotientMeasure 0)
      (fun z => Real.log (cappedHeightWeight ε t z)) (cappedHeightWeight_log_measurable ε t)
      (cylinderTimePacket f hf hc) ⌈(t:ℝ)*R+1⌉₊ := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply LogBands.bandPropagation_limit _ _ _
    (fun n => cylinderTimePacket (radialShiftTime f (a n))
      (radialShiftTime_smooth f hf he hc (a n) (ha n))
      (radialShiftTime_compact f R hR hs (a n) (ha n))) _ _ _
    (cylinderTimePacket_shift_tendsto atTop f hf he hc R hR hs a ha ha0)
  intro n
  let F := radialShiftApprox (evenCoshLift f) (a n)
  have hF := radialShiftApprox_smooth _ (evenCoshLift_smoothOn f hf he hc) _ (ha n)
  have hFc := radialShiftApprox_compact _ (Real.cosh R)
    (evenCoshLift_zero_above f R hR hs) _ (ha n)
  have hFr := radialShiftApprox_real _ (evenCoshLift_real f hr) (a n)
  have hFs := radialShiftApprox_upper_support _ (Real.cosh R)
    (evenCoshLift_zero_above f R hR hs) _ (ha n)
  change LogBands.HasBandPropagation _ _ _
    (cylinderTimePacket (coshTimeTest F) _ _) _
  rw [cylinderTimePacket_cosh F hF hFc hFr R hR hFs]
  exact cylinder_radial_band_propagation _ _ R hR _ hε t _ (Nat.le_ceil _)

/-- Bounded capped-weight conjugation of an arbitrary real even smooth
compact time packet, on the full cylinder L2 space. -/
def cylinderCappedTimePacket (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (ε : ℝ) (hε : 0<ε) (t : ℕ) :=
  LogBands.boundedConjugation (quotientMeasure 0)
    (fun z => Real.log (cappedHeightWeight ε t z)) (cappedHeightWeight_log_measurable ε t)
    (cylinderTimePacket f hf hc) ⌈(t:ℝ)*R+1⌉₊
    (cylinderTimePacket_band f hf he hc hr R hR hs ε hε t)

/-- Conjugated Abel approximants converge in operator norm, even though
the inverse weight is not globally bounded. -/
theorem cylinderCappedTimePacket_shift_tendsto {ι : Type*} (L : Filter ι) [L.IsCountablyGenerated]
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a L (𝓝 0))
    (ε : ℝ) (hε : 0<ε) (t : ℕ) :
    Tendsto (fun i => cylinderCappedRadialOperator
      (abelProfile (radialShiftApprox (evenCoshLift f) (a i)))
      (abelProfile_smooth _ (radialShiftApprox_smooth _ (evenCoshLift_smoothOn f hf he hc) _ (ha i))
        (radialShiftApprox_compact _ (Real.cosh R) (evenCoshLift_zero_above f R hR hs) _ (ha i)))
      R hR (abelProfile_support _ _ (radialShiftApprox_upper_support _ (Real.cosh R)
        (evenCoshLift_zero_above f R hR hs) _ (ha i))) ε hε t) L
      (𝓝 (cylinderCappedTimePacket f hf he hc hr R hR hs ε hε t)) := by
  let T (i : ι) := cylinderTimePacket (radialShiftTime f (a i))
    (radialShiftTime_smooth f hf he hc (a i) (ha i))
    (radialShiftTime_compact f R hR hs (a i) (ha i))
  have hid (i : ι) : T i=
      (radialKernelData 0 (abelProfile (radialShiftApprox (evenCoshLift f) (a i)))
        (abelProfile_smooth _ (radialShiftApprox_smooth _ (evenCoshLift_smoothOn f hf he hc) _ (ha i))
          (radialShiftApprox_compact _ (Real.cosh R) (evenCoshLift_zero_above f R hR hs) _ (ha i)))
        R hR (abelProfile_support _ _ (radialShiftApprox_upper_support _ (Real.cosh R)
          (evenCoshLift_zero_above f R hR hs) _ (ha i)))).operator :=
    cylinderTimePacket_cosh _
      (radialShiftApprox_smooth _ (evenCoshLift_smoothOn f hf he hc) _ (ha i))
      (radialShiftApprox_compact _ (Real.cosh R) (evenCoshLift_zero_above f R hR hs) _ (ha i))
      (radialShiftApprox_real _ (evenCoshLift_real f hr) (a i)) R hR
      (radialShiftApprox_upper_support _ (Real.cosh R) (evenCoshLift_zero_above f R hR hs) _ (ha i))
  have hT (i : ι) : LogBands.HasBandPropagation (quotientMeasure 0)
      (fun z => Real.log (cappedHeightWeight ε t z)) (cappedHeightWeight_log_measurable ε t)
      (T i) ⌈(t:ℝ)*R+1⌉₊ := by
    rw [hid]
    exact cylinder_radial_band_propagation _ _ R hR _ hε t _ (Nat.le_ceil _)
  have hh := LogBands.boundedConjugation_tendsto _ _ _ T (cylinderTimePacket f hf hc) _ hT
    (cylinderTimePacket_band f hf he hc hr R hR hs ε hε t)
    (cylinderTimePacket_shift_tendsto L f hf he hc R hR hs a ha ha0)
  simpa only [hid,cylinderCappedRadialOperator,cylinderCappedTimePacket] using! hh

#print axioms cylinderTimePacket_cosh
#print axioms cylinderTimePacket_shift_tendsto
#print axioms cylinderTimePacket_band
#print axioms cylinderCappedTimePacket_shift_tendsto

end QuantitativeMaass
