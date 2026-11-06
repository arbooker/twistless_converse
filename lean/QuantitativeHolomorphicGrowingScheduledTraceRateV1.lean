module

public import QuantitativeHolomorphicGrowingScheduledGeometryV1
public import QuantitativeHolomorphicGrowingApproximationV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight AsymptoticCompactObservationCount

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

/-- The actual scheduled matrix height, closed filter complexity, lower
cutoff and upper cutoff satisfy separation and the retained trace rate at
the manuscript observation scale. Inputs are only concrete row growth. -/
theorem scheduled_retained_trace_rate (hN : 0<N) (P : Parameters A)
    (qs : Finset ι) (r : ι → Row N) (L U : ℝ) {b C s a : ℝ}
    (hb : 0≤b) (hC : 0≤C) (hs : 1≤s) (d h : ℕ) (hh : 0<h)
    (hsScale : s=Real.log (observationScale a (h+1)))
    (hL : 32≤Real.log (Real.log (h+1:ℝ)))
    (hscale : (geometryGrowthCoefficient+34+commonGeometryGrowthConstant A hN P b C)*a^2≤1/2)
    (hd : (d:ℝ)≤Real.exp (C*s^2))
    (hrowsH : (∑ i∈qs,quantifiedRowHeight hN (r i) L U)≤Real.exp (b*s^2))
    (hrowsM : (∑ i∈qs,(quantifiedRowMass hN (r i) L U
      ((AsymptoticReconstructedCount.parameters A P).s+4))^2)≤Real.exp (b*s^2))
    (hrowsL : (∑ i∈qs,(quantifiedRowLength hN (r i) L U:ℝ)^2)≤Real.exp (b*s^2)) :
    let D₀ : ℝ := 2*d+2
    let n := newtonDepth A P D₀ (Real.exp (-8*s))
    let j := reconstructionDepth A P D₀ (Real.exp (-8*s)) n
    let J := foldCutoff A P D₀ (Real.exp (-8*s)) j n
    let Y := lowerCutoff A P D₀ (Real.exp (-8*s)) n
    let H := Real.exp (16*s)
    let B := quantifiedFilterMatrixHeight A hN qs r L U j J n d
    let F := closedFilterComplexity A hN P qs r L U j J n d
    (h+1:ℝ)^(-(1/3:ℝ))*(B*(H+2))≤1 ∧
    F*uniformRetainedTraceError (B*(H+2)) Y H h (periodizationSet Y H).card≤
      Real.exp (-Real.log (h+1:ℝ)/4) := by
  let D₀ : ℝ := 2*d+2
  let n := newtonDepth A P D₀ (Real.exp (-8*s))
  let j := reconstructionDepth A P D₀ (Real.exp (-8*s)) n
  let J := foldCutoff A P D₀ (Real.exp (-8*s)) j n
  let Y := lowerCutoff A P D₀ (Real.exp (-8*s)) n
  let H := Real.exp (16*s)
  let B := quantifiedFilterMatrixHeight A hN qs r L U j J n d
  let F := closedFilterComplexity A hN P qs r L U j J n d
  let K := commonGeometryGrowthConstant A hN P b C+5
  have hB : 0≤B := quantifiedFilterMatrixHeight_nonneg A hN qs r L U j J n d
  have hF : 0≤F := by dsimp [F,closedFilterComplexity]; positivity
  have hg := growing_scheduled_geometry A hN P qs r L U hb hC hs d hd hrowsH hrowsM hrowsL
  have hK : 0≤K := by
    have hc := commonGeometryGrowthConstant_nonneg A hN P hb hC
    dsimp [K]
    linarith
  have hc : (geometryGrowthCoefficient+29+K)*a^2≤1/2 := by
    dsimp [K]
    convert hscale using 1
    ring
  apply growing_retained_trace_at_scale h hh (by positivity) hg.1
    (Real.exp_pos _) hF hK
  · exact hsScale ▸ hs
  · exact hL
  · exact hc
  · simpa only [←hsScale] using hg.2.1
  · simpa only [←hsScale] using hg.2.2.1
  · simpa only [←hsScale] using hg.2.2.2.1
  · simpa only [←hsScale] using hg.2.2.2.2

#print axioms scheduled_retained_trace_rate

end QuantitativeHolomorphic.Schedule
