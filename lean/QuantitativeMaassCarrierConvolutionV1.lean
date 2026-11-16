module

public import QuantitativeMaassWindowCarrierV1
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap Convolution

namespace QuantitativeMaass

def timeFunctionConvolution (f g : ℝ → ℂ) : ℝ → ℂ :=
  f ⋆[ContinuousLinearMap.mul ℝ ℂ] g

def timeFrequencyShift (t : ℝ) (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  Complex.exp ((t*s:ℝ)*Complex.I)*f s

theorem timeFunctionConvolution_apply (f g : ℝ → ℂ) (s : ℝ) :
    timeFunctionConvolution f g s=∫ u,f u*g (s-u) := rfl

theorem timeConvolution_eq_function (f g : SchwartzMap ℝ ℂ) :
    (timeConvolution f g : ℝ → ℂ)=timeFunctionConvolution f g := by
  funext s
  simp only [timeConvolution,SchwartzMap.convolution_apply,
    timeFunctionConvolution,convolution_def,ContinuousLinearMap.mul_apply']

theorem timeFrequencyShift_norm (t : ℝ) (f : ℝ → ℂ) (s : ℝ) :
    ‖timeFrequencyShift t f s‖=‖f s‖ := by
  rw [timeFrequencyShift,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]

theorem timeFrequencyShift_smooth (t : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (timeFrequencyShift t f) := by
  have hr : ContDiff ℝ ∞ (fun s : ℝ => ((t*s:ℝ):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  change ContDiff ℝ ∞ (fun s => Complex.exp ((t*s:ℝ)*Complex.I)*f s)
  fun_prop

theorem timeFrequencyShift_compact (t : ℝ) (f : ℝ → ℂ) (hc : HasCompactSupport f) :
    HasCompactSupport (timeFrequencyShift t f) := hc.mul_left

theorem timeFrequencyShift_zero (f : ℝ → ℂ) : timeFrequencyShift 0 f=f := by
  funext s
  simp only [timeFrequencyShift,zero_mul,Complex.ofReal_zero,Complex.exp_zero,one_mul]

/-- A phase shift is moved entirely to the second factor inside the amplitude. -/
theorem timeFunctionConvolution_shift (f g : ℝ → ℂ) (t v : ℝ) :
    timeFunctionConvolution (timeFrequencyShift t f) (timeFrequencyShift v g)=
      timeFrequencyShift t (timeFunctionConvolution f (timeFrequencyShift (v-t) g)) := by
  funext s
  simp only [timeFunctionConvolution_apply,timeFrequencyShift]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  have he : Complex.exp ((t*u:ℝ)*Complex.I)*Complex.exp ((v*(s-u):ℝ)*Complex.I)=
      Complex.exp ((t*s:ℝ)*Complex.I)*Complex.exp (((v-t)*(s-u):ℝ)*Complex.I) := by
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (Complex.exp ((t*u:ℝ)*Complex.I)*Complex.exp ((v*(s-u):ℝ)*Complex.I))*(f u*g (s-u)) := by ring
    _ = _ := by rw [he];ring

theorem time_iteratedDeriv_compact (f : ℝ → ℂ) (hc : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem time_iteratedDeriv_smooth (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using (contDiff_infty_iff_deriv.mp ih).2

/-- Every derivative may be taken on the first, unmodulated factor. -/
theorem timeFunctionConvolution_iteratedDeriv (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hg : Continuous g) (n : ℕ) :
    iteratedDeriv n (timeFunctionConvolution f g)=timeFunctionConvolution (iteratedDeriv n f) g := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext s
    simpa only [timeFunctionConvolution,iteratedDeriv_succ] using
      ((time_iteratedDeriv_compact f hc n).hasDerivAt_convolution_left (μ:=volume)
      (ContinuousLinearMap.mul ℝ ℂ) ((time_iteratedDeriv_smooth f hf n).of_le (by simp))
      hg.locallyIntegrable s).deriv

theorem time_iteratedDeriv_support (f : ℝ → ℂ) (L : ℝ)
    (hs : Function.support f⊆Icc (-L) L) (n : ℕ) :
    Function.support (iteratedDeriv n f)⊆Icc (-L) L := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hs
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact support_deriv_subset.trans (closure_minimal ih isClosed_Icc)

/-- Support length times two sup norms gives an explicit convolution bound. -/
theorem timeFunctionConvolution_norm_bound (f g : ℝ → ℂ) (L C D : ℝ) (hL : 0≤L)
    (hs : Function.support f⊆Icc (-L) L) (hf : ∀ u,‖f u‖≤C) (hg : ∀ u,‖g u‖≤D)
    (s : ℝ) : ‖timeFunctionConvolution f g s‖≤2*L*C*D := by
  have hC : 0≤C := (norm_nonneg (f 0)).trans (hf 0)
  have he : timeFunctionConvolution f g s=∫ u in Icc (-L) L,f u*g (s-u) := by
    rw [timeFunctionConvolution_apply]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hz : f u=0 := by
      by_contra hn
      exact hu (hs hn)
    rw [hz,zero_mul]
  rw [he]
  have hb : ‖∫ u in Icc (-L) L,f u*g (s-u)‖≤C*D*(volume.restrict (Icc (-L) L)).real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards with u
    rw [norm_mul]
    exact mul_le_mul (hf u) (hg (s-u)) (norm_nonneg _) hC
  rw [measureReal_restrict_apply_univ,Real.volume_real_Icc_of_le (by linarith)] at hb
  convert hb using 1
  ring

theorem timeFunctionConvolution_support (f g : ℝ → ℂ) (L : ℝ)
    (hf : Function.support f⊆Icc (-L) L) (hg : Function.support g⊆Icc (-L) L) :
    Function.support (timeFunctionConvolution f g)⊆Icc (-(2*L)) (2*L) := by
  intro s hs
  by_contra hn
  apply hs
  rw [timeFunctionConvolution_apply]
  apply integral_eq_zero_of_ae
  filter_upwards with u
  change f u*g (s-u)=0
  by_cases hu : f u=0
  · rw [hu,zero_mul]
  by_cases hv : g (s-u)=0
  · rw [hv,mul_zero]
  have hfu := hf hu
  have hgv := hg hv
  exact False.elim (hn ⟨by linarith [hfu.1,hgv.1],by linarith [hfu.2,hgv.2]⟩)

/-- The carrier amplitude of one frequency sign in a convolution square. -/
def carrierSquareAmplitude (f g : ℝ → ℂ) (v : ℝ) : ℝ → ℂ :=
  timeFunctionConvolution f (f+timeFrequencyShift v g)

theorem carrierSquareAmplitude_smooth (f g : ℝ → ℂ) (v : ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (carrierSquareAmplitude f g v) :=
  hfc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hf
    (hf.continuous.add (timeFrequencyShift_smooth v g hg).continuous).locallyIntegrable

theorem carrierSquareAmplitude_compact (f g : ℝ → ℂ) (v : ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (carrierSquareAmplitude f g v) :=
  hf.convolution (ContinuousLinearMap.mul ℝ ℂ) (hf.add (timeFrequencyShift_compact v g hg))

/-- Quantitative derivatives of the convolution amplitude, uniform in the
frequency hidden in the SECOND factor. -/
theorem carrierSquareAmplitude_derivative_bound (f g : ℝ → ℂ) (L C : ℝ) (hL : 0≤L)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g)
    (hs : Function.support f⊆Icc (-L) L) (n : ℕ)
    (hf0 : ∀ u,‖f u‖≤C) (hfn : ∀ u,‖iteratedDeriv n f u‖≤C) (hg0 : ∀ u,‖g u‖≤C)
    (v s : ℝ) : ‖iteratedDeriv n (carrierSquareAmplitude f g v) s‖≤4*L*C^2 := by
  have he : carrierSquareAmplitude f g v=timeFunctionConvolution f (f+timeFrequencyShift v g) := rfl
  rw [he,timeFunctionConvolution_iteratedDeriv f _ hf hc
    (hf.continuous.add (timeFrequencyShift_smooth v g hg).continuous)]
  have hb : ∀ u,‖(f+timeFrequencyShift v g) u‖≤2*C := by
    intro u
    have hn := norm_add_le (f u) (timeFrequencyShift v g u)
    rw [timeFrequencyShift_norm] at hn
    change ‖f u+timeFrequencyShift v g u‖≤_
    linarith [hf0 u,hg0 u]
  have h := timeFunctionConvolution_norm_bound (iteratedDeriv n f) _ L C (2*C) hL
    (time_iteratedDeriv_support f L hs n) hfn hb s
  convert h using 1
  ring

theorem timeFunctionConvolution_add_right (f g h : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hg : Continuous g) (hh : Continuous h) :
    timeFunctionConvolution f (g+h)=timeFunctionConvolution f g+timeFunctionConvolution f h :=
  (hc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ) hf hg.locallyIntegrable).distrib_add
    (hc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ) hf hh.locallyIntegrable)

theorem timeFunctionConvolution_add_left (f g h : ℝ → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hh : Continuous h) :
    timeFunctionConvolution (f+g) h=timeFunctionConvolution f h+timeFunctionConvolution g h :=
  (hfc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ) hf hh.locallyIntegrable).add_distrib
    (hgc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ) hg hh.locallyIntegrable)

theorem carrierSquareAmplitude_support (f g : ℝ → ℂ) (v L : ℝ)
    (hf : Function.support f⊆Icc (-L) L) (hg : Function.support g⊆Icc (-L) L) :
    Function.support (carrierSquareAmplitude f g v)⊆Icc (-(2*L)) (2*L) := by
  apply timeFunctionConvolution_support f _ L hf
  intro s hs
  by_cases hfs : f s=0
  · apply hg
    intro hgs
    apply hs
    change f s+Complex.exp ((v*s:ℝ)*Complex.I)*g s=0
    rw [hfs,hgs,mul_zero,add_zero]
  · exact hf hfs

/-- The two-carrier convolution square, including the mixed signs, is an
exact identity of actual convolutions. -/
theorem timeFunctionConvolution_pair_square (f g : ℝ → ℂ) (t : ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    timeFunctionConvolution (timeFrequencyShift t f+timeFrequencyShift (-t) g)
      (timeFrequencyShift t f+timeFrequencyShift (-t) g)=
      timeFrequencyShift t (carrierSquareAmplitude f g (-2*t))+
      timeFrequencyShift (-t) (carrierSquareAmplitude g f (2*t)) := by
  have hF := (timeFrequencyShift_smooth t f hf).continuous
  have hFc := timeFrequencyShift_compact t f hfc
  have hG := (timeFrequencyShift_smooth (-t) g hg).continuous
  have hGc := timeFrequencyShift_compact (-t) g hgc
  rw [timeFunctionConvolution_add_left _ _ _ hF hFc hG hGc (hF.add hG),
    timeFunctionConvolution_add_right _ _ _ hF hFc hF hG,
    timeFunctionConvolution_add_right _ _ _ hG hGc hF hG]
  simp only [timeFunctionConvolution_shift,sub_self,timeFrequencyShift_zero,
    show -t-t=-2*t by ring,show t-(-t)=2*t by ring]
  unfold carrierSquareAmplitude
  rw [timeFunctionConvolution_add_right f f _ hf.continuous hfc hf.continuous
      (timeFrequencyShift_smooth (-2*t) g hg).continuous,
    timeFunctionConvolution_add_right g g _ hg.continuous hgc hg.continuous
      (timeFrequencyShift_smooth (2*t) f hf).continuous]
  funext s
  simp only [Pi.add_apply,timeFrequencyShift]
  ring

#print axioms timeFunctionConvolution_add_right
#print axioms timeFunctionConvolution_add_left
#print axioms carrierSquareAmplitude_support
#print axioms timeFunctionConvolution_pair_square

#print axioms timeFunctionConvolution_apply
#print axioms timeConvolution_eq_function
#print axioms timeFrequencyShift_norm
#print axioms timeFrequencyShift_smooth
#print axioms timeFrequencyShift_compact
#print axioms timeFrequencyShift_zero
#print axioms timeFunctionConvolution_shift
#print axioms time_iteratedDeriv_compact
#print axioms time_iteratedDeriv_smooth
#print axioms timeFunctionConvolution_iteratedDeriv
#print axioms time_iteratedDeriv_support
#print axioms timeFunctionConvolution_norm_bound
#print axioms timeFunctionConvolution_support
#print axioms carrierSquareAmplitude_smooth
#print axioms carrierSquareAmplitude_compact
#print axioms carrierSquareAmplitude_derivative_bound

end QuantitativeMaass
