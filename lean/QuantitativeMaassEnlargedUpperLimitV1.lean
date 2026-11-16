module

public import QuantitativeMaassEnlargedUpperTraceV1
public import QuantitativeMaassEnlargedIdentityLimitV1
public import QuantitativeMaassUpperTailLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand
open scoped Topology InnerProductSpace FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The actual enlarged global trace has a majorant tending to the sharp
quotient-volume coefficient under precisely the original width hypothesis. -/
theorem windowWavePacket_enlarged_upper_limit {ι : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (c : ℝ) (hc0 : 0<c) (hc1 : c<1)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcus : ∀ i,v i∈localCuspidalSpace N hN)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ U : ℝ → ℝ,Tendsto U atTop (𝓝 ((quotientMeasure N).real univ/(2*Real.pi))) ∧
      ∀ᶠ t in atTop,
        (∑' i,‖windowWavePacket N K hc (logPowerRadius c t) (logPowerRadius_pos c t)
          (t-logPowerMargin c t) (t+ε t+logPowerMargin c t) (v i)‖^2)/(t*ε t)≤U t := by
  obtain ⟨H,A,B,C,D,hH,hA,hB,hC,hD,hbound⟩ := windowWavePacket_enlarged_upper_trace (ι:=ι) N hN K he hc
  have hep : ∀ᶠ t in atTop,0<ε t := hε.mono (fun _ h => h.1)
  have htrim := logPowerMargin_trim_parameters c hc0 ε hep hproduct
  have hR := logPowerRadius_div_log c hc0 hc1
  have hheight := upperCuspHeight_admissible (logPowerRadius c) H hH hR
  let I := fun t => (windowIdentityContribution K hc (logPowerRadius c t) (logPowerRadius_pos c t)
    (t-logPowerMargin c t) (t+ε t+logPowerMargin c t)).re/(t*ε t)
  let E := fun t => C*Real.sqrt t*(ε t)^2*Real.exp (A*logPowerRadius c t)*
    (1+Real.sqrt (upperCuspHeight t))/(t*ε t)
  let F := fun t => (D*(logPowerRadius c t)^3*(ε t)^2*t*Real.sqrt t*
    Real.exp (B*logPowerRadius c t)/upperCuspHeight t)/(t*ε t)
  have hI : Tendsto I atTop (𝓝 (1/(2*Real.pi))) :=
    windowIdentityContribution_enlarged_normalized K he hc hK hm ε hε
      (logPowerMargin c) htrim.1 (logPowerRadius c) (logPowerRadius_pos c)
      (Eventually.of_forall (fun _ => le_max_left _ _)) (Eventually.of_forall htrim.2)
      (logPowerMargin_div_width c hc0 ε hep hproduct) hproduct
  have hE : Tendsto E atTop (𝓝 0) := upper_core_error_tendsto ε (logPowerRadius c) A C hA.le hC hε hR
  have hF : Tendsto F atTop (𝓝 0) := upper_tail_error_tendsto ε (logPowerRadius c) B D hB.le hD hε
    (Eventually.of_forall (fun t => (logPowerRadius_pos c t).le)) hR
  refine ⟨fun t => I t*(quotientMeasure N).real univ+E t+F t,?_,?_⟩
  · convert ((hI.mul_const ((quotientMeasure N).real univ)).add hE).add hF using 1
    congr 1
    ring
  · filter_upwards [hε,htrim.1,hheight,eventually_ge_atTop (1:ℝ)] with t het hdt hyt ht
    have hh := hbound (logPowerRadius c t) (le_max_left _ _) (ε t) (logPowerMargin c t) t
      het.1.le het.2 hdt.1 hdt.2 ht v hv hcus (upperCuspHeight t) hyt.1 hyt.2
    have hb := div_le_div_of_nonneg_right hh (mul_pos (show 0<t by linarith) het.1).le
    convert hb using 1
    dsimp [I,E,F]
    ring

#print axioms windowWavePacket_enlarged_upper_limit

end QuantitativeMaass
