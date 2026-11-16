module

public import QuantitativeMaassPositiveWindowKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped SchwartzMap FourierTransform

namespace QuantitativeMaass

def intervalIndicator (a b x : ℝ) : ℝ := (Icc a b).indicator (fun _ => 1) x

theorem intervalIndicator_mem_unit (a b x : ℝ) : intervalIndicator a b x∈Icc (0:ℝ) 1 := by
  by_cases hx : x∈Icc a b <;> simp [intervalIndicator,hx]

theorem intervalIndicator_measurable (a b : ℝ) : Measurable (intervalIndicator a b) :=
  measurable_const.indicator measurableSet_Icc

theorem intervalIndicator_integrable (a b : ℝ) : Integrable (intervalIndicator a b) :=
  (integrable_indicator_iff measurableSet_Icc).mpr (integrable_const (1:ℝ))

theorem intervalIndicator_integral (a b : ℝ) (hab : a≤b) :
    (∫ x,intervalIndicator a b x)=b-a := by
  simp only [intervalIndicator,integral_indicator measurableSet_Icc,integral_const,
    measureReal_restrict_apply_univ,smul_eq_mul,mul_one,Real.volume_real_Icc_of_le hab]

def endpointStrip (a u x : ℝ) : ℝ := intervalIndicator (min a (a+u)) (max a (a+u)) x

theorem endpointStrip_integral (a u : ℝ) : (∫ x,endpointStrip a u x)=|u| := by
  unfold endpointStrip
  rw [intervalIndicator_integral _ _ (min_le_max),max_sub_min_eq_abs]
  simp

theorem interval_shift_change_boundary (a b u x : ℝ)
    (hd : (x-u∈Icc a b ∧ x∉Icc a b) ∨ (x∈Icc a b ∧ x-u∉Icc a b)) :
    x∈Icc (min a (a+u)) (max a (a+u)) ∨
      x∈Icc (min b (b+u)) (max b (b+u)) := by
  by_cases hu : 0≤u
  · simp only [min_eq_left (by linarith : a≤a+u),max_eq_right (by linarith : a≤a+u),
      min_eq_left (by linarith : b≤b+u),max_eq_right (by linarith : b≤b+u)]
    rcases hd with ⟨hs,hn⟩|⟨hs,hn⟩
    · have hn' : x<a ∨ b<x := by simpa only [mem_Icc,not_and_or,not_le] using hn
      right
      rcases hn' with h|h
      · exfalso; linarith [hs.1]
      · exact ⟨h.le,by linarith [hs.2]⟩
    · have hn' : x-u<a ∨ b<x-u := by simpa only [mem_Icc,not_and_or,not_le] using hn
      left
      rcases hn' with h|h
      · exact ⟨hs.1,by linarith⟩
      · exfalso; linarith [hs.2]
  · have hu' : u≤0 := le_of_lt (lt_of_not_ge hu)
    simp only [min_eq_right (by linarith : a+u≤a),max_eq_left (by linarith : a+u≤a),
      min_eq_right (by linarith : b+u≤b),max_eq_left (by linarith : b+u≤b)]
    rcases hd with ⟨hs,hn⟩|⟨hs,hn⟩
    · have hn' : x<a ∨ b<x := by simpa only [mem_Icc,not_and_or,not_le] using hn
      left
      rcases hn' with h|h
      · exact ⟨by linarith [hs.1],h.le⟩
      · exfalso; linarith [hs.2]
    · have hn' : x-u<a ∨ b<x-u := by simpa only [mem_Icc,not_and_or,not_le] using hn
      right
      rcases hn' with h|h
      · exfalso; linarith [hs.1]
      · exact ⟨by linarith,hs.2⟩

theorem interval_shift_indicator_bound (a b u x : ℝ) :
    |intervalIndicator a b (x-u)-intervalIndicator a b x| ≤
      endpointStrip a u x+endpointStrip b u x := by
  have ha := (intervalIndicator_mem_unit (min a (a+u)) (max a (a+u)) x).1
  have hb := (intervalIndicator_mem_unit (min b (b+u)) (max b (b+u)) x).1
  change 0≤endpointStrip a u x at ha
  change 0≤endpointStrip b u x at hb
  have hboundary (hd : (x-u∈Icc a b ∧ x∉Icc a b) ∨
      (x∈Icc a b ∧ x-u∉Icc a b)) : 1≤endpointStrip a u x+endpointStrip b u x := by
    rcases interval_shift_change_boundary a b u x hd with h|h
    · have hz : endpointStrip a u x=1 := by simp [endpointStrip,intervalIndicator,h]
      linarith
    · have hz : endpointStrip b u x=1 := by simp [endpointStrip,intervalIndicator,h]
      linarith
  by_cases hs : x-u∈Icc a b <;> by_cases hx : x∈Icc a b
  · simp [intervalIndicator,hs,hx,add_nonneg ha hb]
  · simpa only [intervalIndicator,indicator_of_mem hs,indicator_of_notMem hx,
      sub_zero,abs_one] using hboundary (Or.inl ⟨hs,hx⟩)
  · simpa only [intervalIndicator,indicator_of_notMem hs,indicator_of_mem hx,
      zero_sub,abs_neg,abs_one] using hboundary (Or.inr ⟨hx,hs⟩)
  · simp [intervalIndicator,hs,hx,add_nonneg ha hb]

theorem interval_member_abs_bound (a b A x : ℝ) (ha : |a|≤A) (hb : |b|≤A)
    (hx : x∈Icc a b) : |x|≤A :=
  abs_le.mpr ⟨(abs_le.mp ha).1.trans hx.1,hx.2.trans (abs_le.mp hb).2⟩

theorem interval_shift_weighted_pointwise (a b A u x : ℝ) (hA : 0≤A)
    (ha : |a|≤A) (hb : |b|≤A) :
    (1+|x|)*|intervalIndicator a b (x-u)-intervalIndicator a b x| ≤
      (1+A+|u|)*(endpointStrip a u x+endpointStrip b u x) := by
  by_cases hz : |intervalIndicator a b (x-u)-intervalIndicator a b x|=0
  · rw [hz,mul_zero]
    exact mul_nonneg (by positivity)
      (add_nonneg (intervalIndicator_mem_unit _ _ _).1 (intervalIndicator_mem_unit _ _ _).1)
  have he : x-u∈Icc a b ∨ x∈Icc a b := by
    by_contra hn
    push Not at hn
    exact hz (by simp [intervalIndicator,hn.1,hn.2])
  have hx : |x|≤A+|u| := by
    rcases he with h|h
    · calc
        |x| = |(x-u)+u| := by ring_nf
        _ ≤ |x-u|+|u| := abs_add_le _ _
        _ ≤ _ := by linarith [interval_member_abs_bound a b A (x-u) ha hb h]
    · exact (interval_member_abs_bound a b A x ha hb h).trans (by linarith [abs_nonneg u])
  calc
    _ ≤ (1+A+|u|)*|intervalIndicator a b (x-u)-intervalIndicator a b x| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (interval_shift_indicator_bound a b u x) (by positivity)

/-- Quantitative weighted L1 translation estimate, proved from the two
endpoint strips. The constant is explicit and the translation is arbitrary. -/
theorem interval_shift_weighted_L1 (a b A u : ℝ) (hA : 0≤A)
    (ha : |a|≤A) (hb : |b|≤A) :
    Integrable (fun x => (1+|x|)*|intervalIndicator a b (x-u)-intervalIndicator a b x|) ∧
    (∫ x,(1+|x|)*|intervalIndicator a b (x-u)-intervalIndicator a b x|) ≤
      2*(1+A+|u|)*|u| := by
  let f : ℝ → ℝ := fun x => (1+|x|)*|intervalIndicator a b (x-u)-intervalIndicator a b x|
  let g : ℝ → ℝ := fun x => (1+A+|u|)*(endpointStrip a u x+endpointStrip b u x)
  have hg : Integrable g := ((intervalIndicator_integrable _ _).add
    (intervalIndicator_integrable _ _)).const_mul (1+A+|u|)
  have hfmeas : AEStronglyMeasurable f volume := by
    apply Measurable.aestronglyMeasurable
    have hm := intervalIndicator_measurable a b
    dsimp [f]
    fun_prop
  have hf0 (x : ℝ) : 0≤f x := by dsimp [f]; positivity
  have hfg (x : ℝ) : f x≤g x := interval_shift_weighted_pointwise a b A u x hA ha hb
  have hfi : Integrable f := hg.mono' hfmeas (Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (hf0 x)]
    exact hfg x))
  refine ⟨hfi,?_⟩
  calc
    _ ≤ ∫ x,g x := integral_mono hfi hg hfg
    _ = 2*(1+A+|u|)*|u| := by
      dsimp [g]
      have hia : Integrable (endpointStrip a u) := intervalIndicator_integrable _ _
      have hib : Integrable (endpointStrip b u) := intervalIndicator_integrable _ _
      rw [integral_const_mul,integral_add hia hib,endpointStrip_integral,endpointStrip_integral]
      ring

def intervalTranslationError (a b u x : ℝ) : ℝ :=
  (1+|x|)*|intervalIndicator a b (x-u)-intervalIndicator a b x|

def kernelTranslationError (a b : ℝ) (K : SchwartzMap ℝ ℝ) (R : ℝ)
    (z : ℝ × ℝ) : ℝ := intervalTranslationError a b z.1 z.2*scaledWindowKernel K R z.1

theorem kernelTranslationError_nonneg (a b : ℝ) (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (R : ℝ) (hR : 0<R) (z : ℝ × ℝ) :
    0≤kernelTranslationError a b K R z := by
  dsimp [kernelTranslationError,intervalTranslationError,scaledWindowKernel]
  exact mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) (mul_nonneg hR.le (hK _))

/-- The two-dimensional weighted error is integrable. Its bound uses the
actual first two moments of the fixed kernel with their exact scale factors. -/
theorem kernelTranslationError_integral_bound (a b A : ℝ) (hA : 0≤A)
    (ha : |a|≤A) (hb : |b|≤A) (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (R : ℝ) (hR : 0<R) :
    Integrable (kernelTranslationError a b K R) (volume.prod volume) ∧
    (∫ u,∫ x,kernelTranslationError a b K R (u,x)) ≤
      2*(1+A)*(∫ u,|u| *K u)/R+2*(∫ u,|u|^2*K u)/R^2 := by
  let F := kernelTranslationError a b K R
  let g : ℝ → ℝ := fun u => 2*(1+A)*(|u| *scaledWindowKernel K R u)+
    2*(|u|^2*scaledWindowKernel K R u)
  have hn (u x : ℝ) : 0≤F (u,x) := kernelTranslationError_nonneg a b K hK R hR _
  have hκ (u : ℝ) : 0≤scaledWindowKernel K R u := mul_nonneg hR.le (hK _)
  have hm1 : Integrable (fun u => |u| *scaledWindowKernel K R u) := by
    simpa only [pow_one] using scaledWindowKernel_moment_integrable K hK R hR 1
  have hm2 := scaledWindowKernel_moment_integrable K hK R hR 2
  have hg : Integrable g := (hm1.const_mul (2*(1+A))).add (hm2.const_mul 2)
  have hF : AEStronglyMeasurable F (volume.prod volume) := by
    apply Measurable.aestronglyMeasurable
    have hm := intervalIndicator_measurable a b
    change Measurable (fun z : ℝ × ℝ => (1+|z.2|) *
      |intervalIndicator a b (z.2-z.1)-intervalIndicator a b z.2| * (R*K (R*z.1)))
    fun_prop
  have hrow (u : ℝ) : Integrable (fun x => F (u,x)) :=
    (interval_shift_weighted_L1 a b A u hA ha hb).1.mul_const (scaledWindowKernel K R u)
  have hbound (u : ℝ) : (∫ x,F (u,x))≤g u := by
    dsimp [F,kernelTranslationError,intervalTranslationError]
    rw [integral_mul_const]
    calc
      _ ≤ (2*(1+A+|u|)*|u|)*scaledWindowKernel K R u :=
        mul_le_mul_of_nonneg_right (interval_shift_weighted_L1 a b A u hA ha hb).2 (hκ u)
      _ = g u := by dsimp [g]; ring
  have hprod : Integrable F (volume.prod volume) := by
    apply (integrable_prod_iff hF).mpr
    refine ⟨Filter.Eventually.of_forall hrow,?_⟩
    have hnorm : (fun u => ∫ x,‖F (u,x)‖)=(fun u => ∫ x,F (u,x)) := by
      funext u
      simp only [Real.norm_of_nonneg (hn u _)]
    rw [hnorm]
    apply hg.mono' hF.integral_prod_right'
    filter_upwards with u
    rw [Real.norm_of_nonneg (integral_nonneg (hn u))]
    exact hbound u
  refine ⟨hprod,?_⟩
  calc
    _ ≤ ∫ u,g u := integral_mono hprod.integral_prod_left hg hbound
    _ = _ := by
      dsimp [g]
      rw [integral_add (hm1.const_mul _) (hm2.const_mul _),integral_const_mul,integral_const_mul]
      have hm := scaledWindowKernel_moment K R hR 1
      simp only [pow_one] at hm
      rw [hm,scaledWindowKernel_moment K R hR 2]
      ring

theorem interval_smoothedWindow_integrable (a b : ℝ) (K : SchwartzMap ℝ ℝ)
    (R : ℝ) (hR : 0<R) : Integrable (smoothedWindow K R (Icc a b)) := by
  rw [smoothedWindow_convolution K R (Icc a b) measurableSet_Icc]
  exact (intervalIndicator_integrable a b).integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (scaledWindowKernel_integrable K R hR)

theorem interval_smoothedWindow_error_identity (a b : ℝ) (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) (x : ℝ) :
    smoothedWindow K R (Icc a b) x-intervalIndicator a b x =
      ∫ u,(intervalIndicator a b (x-u)-intervalIndicator a b x)*scaledWindowKernel K R u := by
  have hκ := scaledWindowKernel_integrable K R hR
  have hn (u : ℝ) : 0≤scaledWindowKernel K R u := mul_nonneg hR.le (hK _)
  have hi : Integrable (fun u => intervalIndicator a b (x-u)*scaledWindowKernel K R u) := by
    apply hκ.mono'
    · apply Measurable.aestronglyMeasurable
      have hI := intervalIndicator_measurable a b
      dsimp [scaledWindowKernel]
      fun_prop
    · filter_upwards with u
      have hI := intervalIndicator_mem_unit a b (x-u)
      rw [Real.norm_of_nonneg (mul_nonneg hI.1 (hn u))]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hI.2 (hn u)
  have hc : (∫ u,intervalIndicator a b x*scaledWindowKernel K R u)=intervalIndicator a b x := by
    rw [integral_const_mul,scaledWindowKernel_mass_one K hm R hR,mul_one]
  rw [smoothedWindow_convolution K R (Icc a b) measurableSet_Icc,convolution_mul_swap]
  change (∫ u,intervalIndicator a b (x-u)*scaledWindowKernel K R u)-intervalIndicator a b x=_
  calc
    _ = (∫ u,intervalIndicator a b (x-u)*scaledWindowKernel K R u)-
        (∫ u,intervalIndicator a b x*scaledWindowKernel K R u) := by rw [hc]
    _ = ∫ u,intervalIndicator a b (x-u)*scaledWindowKernel K R u-
        intervalIndicator a b x*scaledWindowKernel K R u := (integral_sub hi (hκ.const_mul _)).symm
    _ = _ := by congr 1; funext u; ring

theorem interval_smoothedWindow_weighted_pointwise (a b : ℝ) (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) (x : ℝ) :
    (1+|x|)*|smoothedWindow K R (Icc a b) x-intervalIndicator a b x| ≤
      ∫ u,kernelTranslationError a b K R (u,x) := by
  rw [interval_smoothedWindow_error_identity a b K hK hm R hR x]
  calc
    _ ≤ (1+|x|)*(∫ u,|(intervalIndicator a b (x-u)-intervalIndicator a b x)*
        scaledWindowKernel K R u|) :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by positivity)
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      have hn : 0≤scaledWindowKernel K R u := mul_nonneg hR.le (hK _)
      rw [abs_mul,abs_of_nonneg hn]
      dsimp [kernelTranslationError,intervalTranslationError]
      ring

/-- Weighted approximation of a literal interval by the actual positive
smoothed window, with constants independent of interval length and scale. -/
theorem interval_smoothedWindow_weighted_L1 (a b A : ℝ) (hA : 0≤A)
    (ha : |a|≤A) (hb : |b|≤A) (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) :
    Integrable (fun x => (1+|x|)*|smoothedWindow K R (Icc a b) x-intervalIndicator a b x|) ∧
    (∫ x,(1+|x|)*|smoothedWindow K R (Icc a b) x-intervalIndicator a b x|) ≤
      2*(1+A)*(∫ u,|u| *K u)/R+2*(∫ u,|u|^2*K u)/R^2 := by
  obtain ⟨hprod,hbound⟩ := kernelTranslationError_integral_bound a b A hA ha hb K hK R hR
  let f : ℝ → ℝ := fun x => (1+|x|)*|smoothedWindow K R (Icc a b) x-intervalIndicator a b x|
  have hf0 (x : ℝ) : 0≤f x := by dsimp [f]; positivity
  have hfmeas : AEStronglyMeasurable f volume := by
    have hg := (interval_smoothedWindow_integrable a b K R hR).aestronglyMeasurable
    have hi := (intervalIndicator_measurable a b).aestronglyMeasurable (μ:=volume)
    dsimp [f]
    fun_prop
  have hfg (x : ℝ) : f x≤∫ u,kernelTranslationError a b K R (u,x) :=
    interval_smoothedWindow_weighted_pointwise a b K hK hm R hR x
  have hfi : Integrable f := hprod.integral_prod_right.mono' hfmeas
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (hf0 x)]; exact hfg x))
  refine ⟨hfi,?_⟩
  calc
    _ ≤ ∫ x,∫ u,kernelTranslationError a b K R (u,x) :=
      integral_mono hfi hprod.integral_prod_right hfg
    _ = ∫ u,∫ x,kernelTranslationError a b K R (u,x) :=
      (integral_integral_swap (f:=fun u x => kernelTranslationError a b K R (u,x)) hprod).symm
    _ ≤ _ := hbound

theorem smoothedWindow_disjoint_union (K : SchwartzMap ℝ ℝ) (R : ℝ) (hR : 0<R)
    (S T : Set ℝ) (hd : Disjoint S T) (hT : MeasurableSet T) (x : ℝ) :
    smoothedWindow K R (S∪T) x=smoothedWindow K R S x+smoothedWindow K R T x := by
  have hi := (scaledWindowKernel_integrable K R hR).comp_sub_left x
  exact setIntegral_union hd hT hi.integrableOn hi.integrableOn

/-- The two disjoint intervals used in the symmetric spectral window have
the sum of their weighted errors, with no loss depending on their lengths. -/
theorem two_intervals_smoothedWindow_weighted_L1 (a b c d A : ℝ) (hA : 0≤A)
    (ha : |a|≤A) (hb : |b|≤A) (hc : |c|≤A) (hd : |d|≤A)
    (hdis : Disjoint (Icc a b) (Icc c d))
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) :
    Integrable (fun x => (1+|x|) * |smoothedWindow K R (Icc a b∪Icc c d) x-
      (Icc a b∪Icc c d).indicator (fun _ => (1:ℝ)) x|) ∧
    (∫ x,(1+|x|) * |smoothedWindow K R (Icc a b∪Icc c d) x-
      (Icc a b∪Icc c d).indicator (fun _ => (1:ℝ)) x|) ≤
      4*(1+A)*(∫ u,|u| * K u)/R+4*(∫ u,|u|^2*K u)/R^2 := by
  obtain ⟨hi1,hb1⟩ := interval_smoothedWindow_weighted_L1 a b A hA ha hb K hK hm R hR
  obtain ⟨hi2,hb2⟩ := interval_smoothedWindow_weighted_L1 c d A hA hc hd K hK hm R hR
  let f1 : ℝ → ℝ := fun x => (1+|x|) * |smoothedWindow K R (Icc a b) x-intervalIndicator a b x|
  let f2 : ℝ → ℝ := fun x => (1+|x|) * |smoothedWindow K R (Icc c d) x-intervalIndicator c d x|
  let f : ℝ → ℝ := fun x => (1+|x|) * |smoothedWindow K R (Icc a b∪Icc c d) x-
    (Icc a b∪Icc c d).indicator (fun _ => (1:ℝ)) x|
  have hsplit (x : ℝ) : smoothedWindow K R (Icc a b∪Icc c d) x=
      smoothedWindow K R (Icc a b) x+smoothedWindow K R (Icc c d) x :=
    smoothedWindow_disjoint_union K R hR _ _ hdis measurableSet_Icc x
  have hisplit (x : ℝ) : (Icc a b∪Icc c d).indicator (fun _ => (1:ℝ)) x=
      intervalIndicator a b x+intervalIndicator c d x := by
    simp only [Set.indicator_union_of_disjoint hdis,intervalIndicator]
  have hfg (x : ℝ) : f x≤f1 x+f2 x := by
    dsimp [f,f1,f2]
    rw [hsplit x,hisplit x]
    have heq : smoothedWindow K R (Icc a b) x+smoothedWindow K R (Icc c d) x-
        (intervalIndicator a b x+intervalIndicator c d x) =
        (smoothedWindow K R (Icc a b) x-intervalIndicator a b x)+
        (smoothedWindow K R (Icc c d) x-intervalIndicator c d x) := by ring
    rw [heq,← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
  have hg : AEStronglyMeasurable (smoothedWindow K R (Icc a b∪Icc c d)) volume := by
    have heq := funext hsplit
    rw [heq]
    exact (interval_smoothedWindow_integrable a b K R hR).aestronglyMeasurable.add
      (interval_smoothedWindow_integrable c d K R hR).aestronglyMeasurable
  have hfi : Integrable f := (hi1.add hi2).mono' (by
    have hI : Measurable ((Icc a b∪Icc c d).indicator (fun _ => (1:ℝ))) :=
      measurable_const.indicator (measurableSet_Icc.union measurableSet_Icc)
    dsimp [f]
    fun_prop) (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (by dsimp [f]; positivity)]
      exact hfg x))
  refine ⟨hfi,?_⟩
  have hb' := integral_mono hfi (hi1.add hi2) hfg
  change (∫ x,f x)≤∫ x,f1 x+f2 x at hb'
  rw [integral_add hi1 hi2] at hb'
  change (∫ x,f x)≤_
  convert hb'.trans (add_le_add hb1 hb2) using 1
  ring

theorem unit_square_indicator_error (z c : ℝ) (hz : z∈Icc (0:ℝ) 1)
    (hc : c=0 ∨ c=1) : |z^2-c|≤2*|z-c| := by
  rcases hc with rfl|rfl
  · rw [sub_zero,sub_zero,abs_of_nonneg (sq_nonneg _),abs_of_nonneg hz.1]
    nlinarith [hz.1,hz.2]
  · have hs : z^2≤1 := by nlinarith [hz.1,hz.2]
    rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith [hz.2])]
    nlinarith [sq_nonneg (z-1)]

/-- Squaring a smoothed indicator costs at most a factor two in its
weighted L1 approximation error. -/
theorem squared_indicator_weighted_L1_transfer (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable g volume) (hunit : ∀ x,g x∈Icc (0:ℝ) 1)
    (S : Set ℝ) (hS : MeasurableSet S) (C : ℝ)
    (hi : Integrable (fun x => (1+|x|) * |g x-S.indicator (fun _ => (1:ℝ)) x|))
    (hb : (∫ x,(1+|x|) * |g x-S.indicator (fun _ => (1:ℝ)) x|)≤C) :
    Integrable (fun x => (1+|x|) * |g x^2-S.indicator (fun _ => (1:ℝ)) x|) ∧
    (∫ x,(1+|x|) * |g x^2-S.indicator (fun _ => (1:ℝ)) x|)≤2*C := by
  let f : ℝ → ℝ := fun x => (1+|x|) * |g x^2-S.indicator (fun _ => (1:ℝ)) x|
  have hm : Measurable (S.indicator (fun _ => (1:ℝ))) := measurable_const.indicator hS
  have hbound (x : ℝ) : f x≤2*((1+|x|) * |g x-S.indicator (fun _ => (1:ℝ)) x|) := by
    have hc : S.indicator (fun _ => (1:ℝ)) x=0 ∨ S.indicator (fun _ => (1:ℝ)) x=1 := by
      by_cases hx : x∈S <;> simp [hx]
    have h := mul_le_mul_of_nonneg_left
      (unit_square_indicator_error (g x) _ (hunit x) hc) (by positivity : 0≤1+|x|)
    dsimp [f]
    nlinarith only [h]
  have hfi : Integrable f := (hi.const_mul 2).mono' (by dsimp [f]; fun_prop)
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (by dsimp [f]; positivity)]
      exact hbound x))
  refine ⟨hfi,?_⟩
  have h := integral_mono hfi (hi.const_mul 2) hbound
  rw [integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left hb (by norm_num))

/-- Quantitative weighted error for the literal squared two-interval
window used in the Weyl argument. -/
theorem two_intervals_squaredWindow_weighted_L1 (a b c d A : ℝ) (hA : 0≤A)
    (ha : |a|≤A) (hb : |b|≤A) (hc : |c|≤A) (hd : |d|≤A)
    (hdis : Disjoint (Icc a b) (Icc c d))
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) :
    Integrable (fun x => (1+|x|) * |(smoothedWindow K R (Icc a b∪Icc c d) x)^2-
      (Icc a b∪Icc c d).indicator (fun _ => (1:ℝ)) x|) ∧
    (∫ x,(1+|x|) * |(smoothedWindow K R (Icc a b∪Icc c d) x)^2-
      (Icc a b∪Icc c d).indicator (fun _ => (1:ℝ)) x|) ≤
      8*(1+A)*(∫ u,|u| * K u)/R+8*(∫ u,|u|^2*K u)/R^2 := by
  obtain ⟨hi,hb'⟩ := two_intervals_smoothedWindow_weighted_L1 a b c d A hA ha hb hc hd hdis
    K hK hm R hR
  have hg : AEStronglyMeasurable (smoothedWindow K R (Icc a b∪Icc c d)) volume := by
    have heq : smoothedWindow K R (Icc a b∪Icc c d) =
        fun x => smoothedWindow K R (Icc a b) x+smoothedWindow K R (Icc c d) x :=
      funext (smoothedWindow_disjoint_union K R hR _ _ hdis measurableSet_Icc)
    rw [heq]
    exact (interval_smoothedWindow_integrable a b K R hR).aestronglyMeasurable.add
      (interval_smoothedWindow_integrable c d K R hR).aestronglyMeasurable
  have h := squared_indicator_weighted_L1_transfer _ hg
    (smoothedWindow_mem_unit K hK hm R hR _) _
    (measurableSet_Icc.union measurableSet_Icc) _ hi hb'
  refine ⟨h.1,?_⟩
  convert h.2 using 1
  ring

/-- A weighted L1 estimate controls the integral against every measurable
weight bounded by the first absolute-moment weight. -/
theorem weighted_L1_integral_comparison (f g w : ℝ → ℝ)
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hw : AEStronglyMeasurable w volume) (hwbound : ∀ x,|w x|≤1+|x|)
    (hi : Integrable (fun x => (1+|x|) * |f x-g x|))
    (hgi : Integrable (fun x => g x*w x)) (C : ℝ)
    (hC : (∫ x,(1+|x|) * |f x-g x|)≤C) :
    Integrable (fun x => f x*w x) ∧
    |(∫ x,f x*w x)-(∫ x,g x*w x)|≤C := by
  have hb (x : ℝ) : |(f x-g x)*w x|≤(1+|x|) * |f x-g x| := by
    rw [abs_mul,mul_comm]
    exact mul_le_mul_of_nonneg_right (hwbound x) (abs_nonneg _)
  have hd : Integrable (fun x => (f x-g x)*w x) := hi.mono' (by fun_prop)
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  have hfi : Integrable (fun x => f x*w x) := by
    convert hd.add hgi using 1
    ext x
    dsimp
    ring
  refine ⟨hfi,?_⟩
  rw [← integral_sub hfi hgi]
  calc
    _ = |∫ x,(f x-g x)*w x| := by congr 1; congr 1; funext x; ring
    _ ≤ ∫ x,|(f x-g x)*w x| := abs_integral_le_integral_abs
    _ ≤ ∫ x,(1+|x|) * |f x-g x| := integral_mono hd.abs hi hb
    _ ≤ C := hC

/-- The real hyperbolic Plancherel density without its constant factor. -/
def windowPlancherelWeight (x : ℝ) : ℝ := x*Real.tanh (Real.pi*x)

theorem windowPlancherelWeight_continuous : Continuous windowPlancherelWeight := by
  have ht : Continuous Real.tanh := by
    have he : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
      funext (fun x => Real.tanh_eq_sinh_div_cosh x)
    rw [he]
    exact Real.continuous_sinh.div Real.continuous_cosh
      (fun x => ne_of_gt (Real.cosh_pos x))
  exact continuous_id.mul (ht.comp (continuous_const.mul continuous_id))

theorem windowPlancherelWeight_abs_le (x : ℝ) : |windowPlancherelWeight x|≤1+|x| := by
  have ht := (Real.abs_tanh_lt_one (Real.pi*x)).le
  dsimp [windowPlancherelWeight]
  rw [abs_mul]
  have h := mul_le_mul_of_nonneg_left ht (abs_nonneg x)
  nlinarith only [h]

/-- The squared two-interval window has its actual Plancherel integral
within the explicit moment error of the corresponding sharp window. -/
theorem two_intervals_squaredWindow_plancherel_comparison (a b c d A : ℝ) (hA : 0≤A)
    (ha : |a|≤A) (hb : |b|≤A) (hc : |c|≤A) (hd : |d|≤A)
    (hdis : Disjoint (Icc a b) (Icc c d))
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) :
    Integrable (fun x => (smoothedWindow K R (Icc a b∪Icc c d) x)^2*
      windowPlancherelWeight x) ∧
    |(∫ x,(smoothedWindow K R (Icc a b∪Icc c d) x)^2*windowPlancherelWeight x)-
      (∫ x in Icc a b∪Icc c d,windowPlancherelWeight x)| ≤
      8*(1+A)*(∫ u,|u| * K u)/R+8*(∫ u,|u|^2*K u)/R^2 := by
  obtain ⟨hi,hb'⟩ := two_intervals_squaredWindow_weighted_L1 a b c d A hA ha hb hc hd hdis
    K hK hm R hR
  have hS : MeasurableSet (Icc a b∪Icc c d) := measurableSet_Icc.union measurableSet_Icc
  have hg : AEStronglyMeasurable (smoothedWindow K R (Icc a b∪Icc c d)) volume := by
    have heq : smoothedWindow K R (Icc a b∪Icc c d) =
        fun x => smoothedWindow K R (Icc a b) x+smoothedWindow K R (Icc c d) x :=
      funext (smoothedWindow_disjoint_union K R hR _ _ hdis measurableSet_Icc)
    rw [heq]
    exact (interval_smoothedWindow_integrable a b K R hR).aestronglyMeasurable.add
      (interval_smoothedWindow_integrable c d K R hR).aestronglyMeasurable
  have hI : Measurable ((Icc a b∪Icc c d).indicator (fun _ => (1:ℝ))) :=
    measurable_const.indicator hS
  have heq : (fun x => (Icc a b∪Icc c d).indicator (fun _ => (1:ℝ)) x*
      windowPlancherelWeight x) = (Icc a b∪Icc c d).indicator windowPlancherelWeight := by
    ext x
    by_cases hx : x∈Icc a b∪Icc c d <;> simp [hx]
  have hgi : Integrable (fun x => (Icc a b∪Icc c d).indicator (fun _ => (1:ℝ)) x*
      windowPlancherelWeight x) := by
    rw [heq]
    apply (integrable_indicator_iff hS).mpr
    exact windowPlancherelWeight_continuous.continuousOn.integrableOn_compact
      (isCompact_Icc.union isCompact_Icc)
  have h := weighted_L1_integral_comparison
    (fun x => (smoothedWindow K R (Icc a b∪Icc c d) x)^2)
    ((Icc a b∪Icc c d).indicator (fun _ => (1:ℝ))) windowPlancherelWeight
    (by fun_prop) hI.aestronglyMeasurable windowPlancherelWeight_continuous.aestronglyMeasurable
    windowPlancherelWeight_abs_le hi hgi _ hb'
  rw [heq,integral_indicator hS] at h
  exact h

theorem windowPlancherelWeight_even (x : ℝ) :
    windowPlancherelWeight (-x)=windowPlancherelWeight x := by
  simp [windowPlancherelWeight,Real.tanh_neg]

/-- The difference between the hyperbolic density and the absolute-value
density is uniformly bounded; on bounded-length windows this costs O(1). -/
theorem windowPlancherelWeight_abs_error (x : ℝ) :
    |windowPlancherelWeight x - (|x|)|≤1 := by
  have hp (r : ℝ) (hr : 0≤r) : |windowPlancherelWeight r-r|≤1 := by
    have hc := Real.cosh_pos (Real.pi*r)
    have hc1 := Real.one_le_cosh (Real.pi*r)
    have he : r≤Real.exp (Real.pi*r) := by
      have h := Real.add_one_le_exp (Real.pi*r)
      have hpi : 1≤Real.pi := by linarith [Real.two_le_pi]
      nlinarith
    have he' : r*Real.exp (-(Real.pi*r))≤1 := by
      rw [Real.exp_neg,← div_eq_mul_inv]
      exact (div_le_one (Real.exp_pos _)).mpr he
    have hid : r-windowPlancherelWeight r =
        r*Real.exp (-(Real.pi*r))/Real.cosh (Real.pi*r) := by
      dsimp [windowPlancherelWeight]
      rw [Real.tanh_eq_sinh_div_cosh]
      rw [← Real.cosh_sub_sinh]
      field_simp
    have hn : 0≤r-windowPlancherelWeight r := by rw [hid]; positivity
    rw [abs_of_nonpos (by linarith)]
    have hb : r-windowPlancherelWeight r≤1 := by
      rw [hid]
      exact (div_le_one hc).mpr (he'.trans hc1)
    linarith
  by_cases hx : 0≤x
  · simpa only [abs_of_nonneg hx] using hp x hx
  · have hn : 0≤-x := by linarith
    simpa only [windowPlancherelWeight_even,abs_of_neg (lt_of_not_ge hx)] using hp (-x) hn

theorem compact_window_plancherel_error (S : Set ℝ) (hS : IsCompact S) :
    |(∫ x in S,windowPlancherelWeight x)-(∫ x in S,|x|)|≤volume.real S := by
  have hw : IntegrableOn windowPlancherelWeight S :=
    windowPlancherelWeight_continuous.continuousOn.integrableOn_compact hS
  have ha : IntegrableOn (fun x : ℝ => |x|) S :=
    continuous_abs.continuousOn.integrableOn_compact hS
  have : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hS.measure_lt_top (μ:=volume)⟩
  rw [← integral_sub hw ha]
  calc
    _ ≤ ∫ x in S,|windowPlancherelWeight x - (|x|)| := abs_integral_le_integral_abs
    _ ≤ ∫ _x in S,(1:ℝ) := integral_mono (hw.sub ha).abs (integrable_const 1)
      windowPlancherelWeight_abs_error
    _ = volume.real S := by simp

theorem symmetric_window_disjoint (a b : ℝ) (ha : 0<a) :
    Disjoint (Icc a b) (Icc (-b) (-a)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h1 := hx.1
  have h2 := hy.2
  linarith

theorem symmetric_window_abs_mass (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (∫ x in Icc a b∪Icc (-b) (-a),|x|)=b^2-a^2 := by
  have hp : (∫ x in Icc a b,|x|)=(b^2-a^2)/2 := by
    calc
      _ = ∫ x in Icc a b,x := setIntegral_congr_fun measurableSet_Icc
        (fun x hx => abs_of_nonneg (le_trans ha.le hx.1))
      _ = _ := by rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,
        integral_id]
  have hn : (∫ x in Icc (-b) (-a),|x|)=(b^2-a^2)/2 := by
    calc
      _ = ∫ x in Icc (-b) (-a),-x := setIntegral_congr_fun measurableSet_Icc
        (fun x hx => abs_of_nonpos (by linarith [hx.2]))
      _ = _ := by
        rw [integral_neg,integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (neg_le_neg hab),integral_id]
        ring
  rw [setIntegral_union (symmetric_window_disjoint a b ha) measurableSet_Icc
    (continuous_abs.continuousOn.integrableOn_compact isCompact_Icc)
    (continuous_abs.continuousOn.integrableOn_compact isCompact_Icc),hp,hn]
  ring

theorem symmetric_window_volume (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    volume.real (Icc a b∪Icc (-b) (-a))=2*(b-a) := by
  rw [measureReal_union (symmetric_window_disjoint a b ha) measurableSet_Icc
    (ne_of_lt isCompact_Icc.measure_lt_top) (ne_of_lt isCompact_Icc.measure_lt_top),
    Real.volume_real_Icc_of_le hab,Real.volume_real_Icc_of_le (neg_le_neg hab)]
  ring

/-- Explicit normalization for the actual squared symmetric window. -/
theorem symmetric_squaredWindow_plancherel_mass (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) :
    Integrable (fun x => (smoothedWindow K R (Icc a b∪Icc (-b) (-a)) x)^2*
      windowPlancherelWeight x) ∧
    |(∫ x,(smoothedWindow K R (Icc a b∪Icc (-b) (-a)) x)^2*windowPlancherelWeight x)-
      (b^2-a^2)| ≤
      8*(1+b)*(∫ u,|u| * K u)/R+8*(∫ u,|u|^2*K u)/R^2+2*(b-a) := by
  have hb : 0≤b := ha.le.trans hab
  have haa : |a|≤b := by rwa [abs_of_nonneg ha.le]
  have hbb : |b|≤b := by rw [abs_of_nonneg hb]
  have hna : |-a|≤b := by simpa only [abs_neg] using haa
  have hnb : |-b|≤b := by simpa only [abs_neg] using hbb
  obtain ⟨hi,herr⟩ := two_intervals_squaredWindow_plancherel_comparison
    a b (-b) (-a) b hb haa hbb hnb hna (symmetric_window_disjoint a b ha)
    K hK hm R hR
  refine ⟨hi,?_⟩
  have hsharp := compact_window_plancherel_error (Icc a b∪Icc (-b) (-a))
    (isCompact_Icc.union isCompact_Icc)
  rw [symmetric_window_abs_mass a b ha hab,symmetric_window_volume a b ha hab] at hsharp
  exact (abs_sub_le _ (∫ x in Icc a b∪Icc (-b) (-a),windowPlancherelWeight x) _).trans
    (add_le_add herr hsharp)

/-- The manuscript's shrunken window has the required leading mass, with
all endpoint and smoothing errors explicit and uniform in its width. -/
theorem shrunken_squaredWindow_plancherel_mass (t ε δ : ℝ) (ht : 0<t)
    (hε : ε∈Icc (0:ℝ) 1) (hδ : 0≤δ) (hδε : 2*δ≤ε)
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) :
    Integrable (fun x => (smoothedWindow K R
      (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) x)^2*windowPlancherelWeight x) ∧
    |(∫ x,(smoothedWindow K R
      (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) x)^2*windowPlancherelWeight x)-
      2*t*ε| ≤
      8*(1+t+ε)*(∫ u,|u| * K u)/R+8*(∫ u,|u|^2*K u)/R^2+4*t*δ+3 := by
  obtain ⟨hi,hb⟩ := symmetric_squaredWindow_plancherel_mass (t+δ) (t+ε-δ)
    (by linarith) (by linarith) K hK hm R hR
  refine ⟨hi,?_⟩
  have hm1 : 0≤∫ u,|u| * K u := integral_nonneg (fun u => mul_nonneg (abs_nonneg u) (hK u))
  have hwidth : 2*((t+ε-δ)-(t+δ))≤2 := by linarith [hε.2]
  have herr : |((t+ε-δ)^2-(t+δ)^2)-2*t*ε|≤4*t*δ+1 := by
    have hεsq : ε^2≤1 := by nlinarith [hε.1,hε.2]
    have hed : 0≤ε*(ε-2*δ) := mul_nonneg hε.1 (by linarith)
    have htd : 0≤t*δ := mul_nonneg ht.le hδ
    have hεδ : 0≤ε*δ := mul_nonneg hε.1 hδ
    apply abs_le.mpr
    constructor <;> nlinarith
  have hs : 8*(1+(t+ε-δ))*(∫ u,|u| * K u)/R ≤
      8*(1+t+ε)*(∫ u,|u| * K u)/R := by
    apply div_le_div_of_nonneg_right _ hR.le
    apply mul_le_mul_of_nonneg_right _ hm1
    linarith
  have h := (abs_sub_le
    (∫ x,(smoothedWindow K R
      (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) x)^2*windowPlancherelWeight x)
    ((t+ε-δ)^2-(t+δ)^2) (2*t*ε)).trans (add_le_add hb herr)
  linarith

/-- Uniform O(t*δ+1) mass normalization. The one constant is chosen from
an actually constructed even positive bandlimited probability kernel. -/
theorem exists_uniform_window_plancherel_mass :
    ∃ (K : SchwartzMap ℝ ℝ) (C : ℝ), 0<C ∧ (∀ x,0≤K x) ∧ Function.Even K ∧
      (∫ x,K x)=1 ∧ HasCompactSupport (𝓕 (fun x => (K x:ℂ))) ∧
      ∀ (t ε δ R : ℝ),1≤t → ε∈Icc (0:ℝ) 1 → 0≤δ → 2*δ≤ε →
        1≤R → 1/R≤δ →
        Integrable (fun x => (smoothedWindow K R
          (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) x)^2*windowPlancherelWeight x) ∧
        |(∫ x,(smoothedWindow K R
          (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) x)^2*windowPlancherelWeight x)/
          (4*Real.pi)-t*ε/(2*Real.pi)| ≤ C*(t*δ+1) := by
  obtain ⟨K,hK,he,hm,hband⟩ := exists_positive_bandlimited_window_kernel
  let m1 : ℝ := ∫ u,|u| * K u
  let m2 : ℝ := ∫ u,|u|^2*K u
  have hm1 : 0≤m1 := integral_nonneg (fun u => mul_nonneg (abs_nonneg u) (hK u))
  have hm2 : 0≤m2 := integral_nonneg (fun u => mul_nonneg (sq_nonneg _) (hK u))
  let C : ℝ := (24*m1+8*m2+7)/(4*Real.pi)
  have hπ : 0<4*Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine ⟨K,C,div_pos (by positivity) hπ,hK,he,hm,hband,?_⟩
  intro t ε δ R ht hε hδ hδε hR hRδ
  have ht0 : 0<t := by linarith
  have hR0 : 0<R := by linarith
  obtain ⟨hi,hb⟩ := shrunken_squaredWindow_plancherel_mass t ε δ ht0 hε hδ hδε
    K hK hm R hR0
  refine ⟨hi,?_⟩
  have hfirst : 8*(1+t+ε)*m1/R≤24*m1*(t*δ) := by
    have hcoef : 8*(1+t+ε)*m1≤24*t*m1 :=
      mul_le_mul_of_nonneg_right (by nlinarith [hε.2]) hm1
    calc
      _ ≤ (24*t*m1)/R := div_le_div_of_nonneg_right hcoef hR0.le
      _ = (24*t*m1)*(1/R) := by ring
      _ ≤ (24*t*m1)*δ := mul_le_mul_of_nonneg_left hRδ (by positivity)
      _ = _ := by ring
  have hsecond : 8*m2/R^2≤8*m2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    have hpow : 1≤R^2 := by nlinarith
    nlinarith [mul_nonneg hm2 (sub_nonneg.mpr hpow)]
  have htd : 0≤t*δ := mul_nonneg ht0.le hδ
  have herror : 8*(1+t+ε)*m1/R+8*m2/R^2+4*t*δ+3 ≤
      (24*m1+8*m2+7)*(t*δ+1) := by
    nlinarith [mul_nonneg hm2 htd]
  have hfull := hb.trans herror
  have hdiv := div_le_div_of_nonneg_right hfull hπ.le
  convert hdiv using 1
  · have hid (I : ℝ) : I/(4*Real.pi)-t*ε/(2*Real.pi) =
        (I-2*t*ε)/(4*Real.pi) := by ring
    rw [hid,abs_div,abs_of_pos hπ]
  · dsimp [C]
    ring

#print axioms exists_uniform_window_plancherel_mass

#print axioms shrunken_squaredWindow_plancherel_mass

#print axioms symmetric_window_disjoint
#print axioms symmetric_window_abs_mass
#print axioms symmetric_window_volume
#print axioms symmetric_squaredWindow_plancherel_mass

#print axioms windowPlancherelWeight_even
#print axioms windowPlancherelWeight_abs_error
#print axioms compact_window_plancherel_error

#print axioms weighted_L1_integral_comparison
#print axioms windowPlancherelWeight_continuous
#print axioms windowPlancherelWeight_abs_le
#print axioms two_intervals_squaredWindow_plancherel_comparison

#print axioms smoothedWindow_disjoint_union
#print axioms two_intervals_smoothedWindow_weighted_L1
#print axioms unit_square_indicator_error
#print axioms squared_indicator_weighted_L1_transfer
#print axioms two_intervals_squaredWindow_weighted_L1

#print axioms kernelTranslationError_nonneg
#print axioms kernelTranslationError_integral_bound
#print axioms interval_smoothedWindow_integrable
#print axioms interval_smoothedWindow_error_identity
#print axioms interval_smoothedWindow_weighted_pointwise
#print axioms interval_smoothedWindow_weighted_L1

#print axioms intervalIndicator_mem_unit
#print axioms intervalIndicator_measurable
#print axioms intervalIndicator_integrable
#print axioms intervalIndicator_integral
#print axioms endpointStrip_integral
#print axioms interval_shift_change_boundary
#print axioms interval_shift_indicator_bound
#print axioms interval_member_abs_bound
#print axioms interval_shift_weighted_pointwise
#print axioms interval_shift_weighted_L1

end QuantitativeMaass
