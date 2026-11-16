module

public import QuantitativeMaassCorrespondenceIdentityV1
public import QuantitativeMaassParityLocalMainV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

/-- Actual original-window square kernel evaluated on a fixed integral correspondence. -/
def windowIntegralKernel (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (x : ℍ) : ℂ :=
  radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution
    (windowTimeSchwartz K hc R hR a b) (windowTimeSchwartz K hc R hR a b))))
    x (positiveIntegralGL M hM • x)

/-- Exact identity-coset split for the actual original window. -/
theorem windowIntegralKernel_split (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (x : ℍ) :
    windowIntegralKernel N M hM K hc R hR a b x=
      (if integralIdentityCoset N M then windowIdentityContribution K hc R hR a b else 0)+
        windowIntegralRemainder N M hM K hc R hR a b x := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  let f := windowTimeSchwartz K hc R hR a b
  have hBR : 0≤B*R := mul_nonneg hB.le hR.le
  apply radialIntegralKernel_identity_split N M hM _ (B*R+B*R) (add_nonneg hBR hBR)
  exact abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (add_nonneg hBR hBR)
    (timeConvolution_support f f (B*R) (B*R) (hs R hR a b) (hs R hR a b)))

/-- Actual correspondence kernel and its nonscalar remainder are continuous. -/
theorem windowIntegralKernel_continuous (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    Continuous (windowIntegralKernel N M hM K hc R hR a b) ∧
      Continuous (windowIntegralRemainder N M hM K hc R hR a b) := by
  have hp : Continuous (fun x : ℍ => (x,positiveIntegralGL M hM • x)) :=
    continuous_id.prodMk (continuous_const_smul (positiveIntegralGL M hM))
  have hk : Continuous (windowIntegralKernel N M hM K hc R hR a b) := by
    exact Continuous.comp (g := fun q : ℍ×ℍ => radialPoincareKernel N
      (abelProfile (evenCoshLift (timeConvolution (windowTimeSchwartz K hc R hR a b)
        (windowTimeSchwartz K hc R hR a b)))) q.1 q.2)
      (f := fun x : ℍ => (x,positiveIntegralGL M hM • x))
      (windowTimeSquare_kernel_continuous N K he hc R hR a b) hp
  refine ⟨hk,?_⟩
  have hh : windowIntegralRemainder N M hM K hc R hR a b=(fun x =>
      windowIntegralKernel N M hM K hc R hR a b x-
        (if integralIdentityCoset N M then windowIdentityContribution K hc R hR a b else 0)) := by
    funext x
    rw [windowIntegralKernel_split]
    ring
  rw [hh]
  exact hk.sub continuous_const

/-- Exact local correspondence main term with an absolutely integrated error. -/
theorem windowIntegralKernel_integral_error (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (s : Set ℍ) (hs : IsCompact s)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    |(∫ x in s,(windowIntegralKernel N M hM K hc R hR a b x).re ∂quotientMeasure N)-
      (quotientMeasure N).real s*
        (if integralIdentityCoset N M then (windowIdentityContribution K hc R hR a b).re else 0)|≤
      ∫ x in s,‖windowIntegralRemainder N M hM K hc R hR a b x‖ ∂quotientMeasure N := by
  let G := windowIntegralRemainder N M hM K hc R hR a b
  have hG : IntegrableOn G s (quotientMeasure N) :=
    (windowIntegralKernel_continuous N M hM K he hc R hR a b).2.continuousOn.integrableOn_compact hs
  have hh : (fun x => (windowIntegralKernel N M hM K hc R hR a b x).re)=
      (fun x => (if integralIdentityCoset N M then (windowIdentityContribution K hc R hR a b).re else 0)+(G x).re) := by
    funext x
    rw [windowIntegralKernel_split,Complex.add_re]
    split_ifs <;> rfl
  have hGi : IntegrableOn (fun x => (G x).re) s (quotientMeasure N) := hG.re
  have hci : IntegrableOn (fun _ : ℍ => if integralIdentityCoset N M then
      (windowIdentityContribution K hc R hR a b).re else 0) s (quotientMeasure N) := integrable_const _
  rw [hh,integral_add hci hGi,integral_const,
    measureReal_restrict_apply_univ,smul_eq_mul,add_sub_cancel_left]
  calc
    _ ≤ ∫ x in s,‖(G x).re‖ ∂quotientMeasure N := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := (quotientMeasure N).restrict s) (fun x => (G x).re)
    _ ≤ _ := integral_mono hG.re.norm hG.norm
      (fun x => by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (G x))

/-- Original shrinking-window asymptotic for every fixed positive integral
correspondence. The main coefficient is its concrete identity-coset indicator.
This is a geometric trace result; it does not assert the cuspidal Weyl law. -/
theorem windowIntegralKernel_interval_trace_main (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (∫ x in Metric.closedBall o (positiveWindowRadius ε t),
        (windowIntegralKernel N M hM K hc (positiveWindowRadius ε t)
          (positiveWindowRadius_pos ε t) t (t+ε t) x).re ∂quotientMeasure N)/(t*ε t))
      atTop (𝓝 (if integralIdentityCoset N M then (quotientMeasure N).real univ/(2*Real.pi) else 0)) := by
  let A := fun t => ∫ x in Metric.closedBall o (positiveWindowRadius ε t),
    (windowIntegralKernel N M hM K hc (positiveWindowRadius ε t)
      (positiveWindowRadius_pos ε t) t (t+ε t) x).re ∂quotientMeasure N
  let V := fun t => (quotientMeasure N).real (Metric.closedBall o (positiveWindowRadius ε t))
  let I := fun t => if integralIdentityCoset N M then
    (windowIdentityContribution K hc (positiveWindowRadius ε t)
      (positiveWindowRadius_pos ε t) t (t+ε t)).re else 0
  have hgeom := windowIntegralRemainder_interval_negligible N M hM K he hc o ε hε hproduct
  have herr : Tendsto (fun t => A t/(t*ε t)-V t*(I t/(t*ε t))) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hgeom
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
    rw [sub_zero,show A t/(t*ε t)-V t*(I t/(t*ε t))=(A t-V t*I t)/(t*ε t) by ring,
      Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hp ht.1)]
    exact div_le_div_of_nonneg_right (windowIntegralKernel_integral_error N M hM _
      (isCompact_closedBall o (positiveWindowRadius ε t)) K he hc _
      (positiveWindowRadius_pos ε t) t (t+ε t)) (mul_pos hp ht.1).le
  have hV := quotientMeasure_expanding_ball_limit N o (positiveWindowRadius ε)
    (positiveWindowRadius_tendsto_atTop ε hε hproduct)
  have hI : Tendsto (fun t => I t/(t*ε t)) atTop
      (𝓝 (if integralIdentityCoset N M then 1/(2*Real.pi) else 0)) := by
    by_cases hi : integralIdentityCoset N M
    · simpa only [I,ite_eq_left hi] using
        windowIdentityContribution_interval_normalized K he hc hK hm ε hε hproduct
    · simp only [I,ite_eq_right hi,zero_div]
      exact tendsto_const_nhds
  change Tendsto V atTop (𝓝 ((quotientMeasure N).real univ)) at hV
  have hh := herr.add (hV.mul hI)
  simp only [sub_add_cancel,zero_add] at hh
  convert hh using 1
  split_ifs <;> ring

#print axioms windowIntegralKernel_split
#print axioms windowIntegralKernel_continuous
#print axioms windowIntegralKernel_integral_error
#print axioms windowIntegralKernel_interval_trace_main

end QuantitativeMaass
