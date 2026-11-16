module

public import QuantitativeMaassWindowResidualPolynomialV1
public import QuantitativeMaassPositiveWindowKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped SchwartzMap Convolution

namespace QuantitativeMaass

/-- The fifth inhomogeneous moment follows from the six ordinary moments
of the actual dilated Schwartz kernel. -/
theorem scaledWindowKernel_fifth_weight_integrable (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x, 0 ≤ K x) (R : ℝ) (hR : 0 < R) :
    Integrable (fun x => (1+|x|)^5 * scaledWindowKernel K R x) := by
  have h0 := scaledWindowKernel_moment_integrable K hK R hR 0
  have h1 := scaledWindowKernel_moment_integrable K hK R hR 1
  have h2 := scaledWindowKernel_moment_integrable K hK R hR 2
  have h3 := scaledWindowKernel_moment_integrable K hK R hR 3
  have h4 := scaledWindowKernel_moment_integrable K hK R hR 4
  have h5 := scaledWindowKernel_moment_integrable K hK R hR 5
  have hi := ((((h0.add (h1.const_mul 5)).add (h2.const_mul 10)).add
    (h3.const_mul 10)).add (h4.const_mul 5)).add h5
  convert hi using 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- The squared smoothed window has a finite residual moment controlled
by the fifth kernel moment. The window can contain either or both reflected
bands. Convolution integrability and its mass formula supply Fubini without
requiring a point spectrum or an estimate hypothesis. -/
theorem smoothedWindow_residual_moment (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (R : ℝ) (hR : 0 < R) (S : Set ℝ) (hS : MeasurableSet S)
    [IsFiniteMeasure (volume.restrict S)]
    (t : ℝ) (ht : 1 ≤ t)
    (hband : ∀ u ∈ S, t ≤ |u| ∧ |u| ≤ t+1) :
    Integrable (fun r => (r^2-t^2)^2 * |r| * (smoothedWindow K R S r)^2) ∧
      (∫ r, (r^2-t^2)^2 * |r| * (smoothedWindow K R S r)^2) ≤
        18*t^3*(volume S).toReal *
          ∫ x, (1+|x|)^5 * scaledWindowKernel K R x := by
  let Q := fun x : ℝ => (1+|x|)^5 * scaledWindowKernel K R x
  let H := fun r : ℝ => ∫ u in S, Q (r-u)
  have hκ := scaledWindowKernel_integrable K R hR
  have hQ : Integrable Q := scaledWindowKernel_fifth_weight_integrable K hK R hR
  have hI : Integrable (S.indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff hS).mpr (integrable_const (1 : ℝ))
  have hconv : H = S.indicator (fun _ => (1 : ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ] Q := by
    funext r
    unfold convolution
    dsimp only [H]
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ S <;> simp [ContinuousLinearMap.mul_apply', Set.indicator, hu]
  have hH : Integrable H := by
    rw [hconv]
    exact hI.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hQ
  have hmass : (∫ r, H r) = (volume S).toReal * ∫ x, Q x := by
    rw [hconv, integral_convolution _ hI hQ, ContinuousLinearMap.mul_apply',
      integral_indicator hS, integral_const, measureReal_restrict_apply_univ]
    simp only [smul_eq_mul, mul_one, measureReal_def]
  have hW : Integrable (smoothedWindow K R S) := by
    rw [smoothedWindow_convolution K R S hS]
    exact hI.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hκ
  have hκnonneg (x : ℝ) : 0 ≤ scaledWindowKernel K R x := mul_nonneg hR.le (hK _)
  have hpoint (r : ℝ) :
      (r^2-t^2)^2 * |r| * (smoothedWindow K R S r)^2 ≤ 18*t^3*H r := by
    have hunit := smoothedWindow_mem_unit K hK hm R hR S r
    have hsq : (smoothedWindow K R S r)^2 ≤ smoothedWindow K R S r := by
      nlinarith [hunit.1, hunit.2]
    calc
      _ ≤ ((r^2-t^2)^2 * |r|) * smoothedWindow K R S r :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg (sq_nonneg _) (abs_nonneg r))
      _ = ∫ u in S, ((r^2-t^2)^2 * |r|) * scaledWindowKernel K R (r-u) :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ u in S, (18*t^3) * Q (r-u) := by
        apply setIntegral_mono_on ((hκ.comp_sub_left r).const_mul _).integrableOn
          ((hQ.comp_sub_left r).const_mul _).integrableOn hS
        intro u hu
        have hh := mul_le_mul_of_nonneg_right
          (window_residual_weight_le t r u ht (hband u hu).1 (hband u hu).2)
          (hκnonneg (r-u))
        simpa only [Q, mul_assoc] using hh
      _ = 18*t^3*H r := integral_const_mul _ _
  have hmeas : AEStronglyMeasurable
      (fun r => (r^2-t^2)^2 * |r| * (smoothedWindow K R S r)^2) :=
    (show Continuous (fun r : ℝ => (r^2-t^2)^2 * |r|) by fun_prop).aestronglyMeasurable.mul
      (hW.aestronglyMeasurable.pow 2)
  have hres : Integrable
      (fun r => (r^2-t^2)^2 * |r| * (smoothedWindow K R S r)^2) := by
    apply (hH.const_mul (18*t^3)).mono' hmeas
    filter_upwards with r
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpoint r
  refine ⟨hres, ?_⟩
  calc
    _ ≤ ∫ r, 18*t^3*H r := integral_mono hres (hH.const_mul _) hpoint
    _ = 18*t^3*(volume S).toReal * ∫ x, Q x := by
      rw [integral_const_mul, hmass]
      ring
    _ = _ := rfl

#print axioms scaledWindowKernel_fifth_weight_integrable
#print axioms smoothedWindow_residual_moment

end QuantitativeMaass
