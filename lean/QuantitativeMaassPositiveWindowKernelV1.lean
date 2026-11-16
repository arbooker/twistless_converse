module

public import QuantitativeMaassMovingWindowsV1
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff Convolution ComplexConjugate

namespace QuantitativeMaass

/-- The squared Fourier amplitude is itself a real Schwartz function. -/
def spectralSquare (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.pairing (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ((𝓕 f : SchwartzMap ℝ ℂ)) ((𝓕 f : SchwartzMap ℝ ℂ))

theorem spectralSquare_apply (f : SchwartzMap ℝ ℂ) (r : ℝ) :
    spectralSquare f r = ‖(𝓕 f : SchwartzMap ℝ ℂ) r‖^2 := by
  change inner ℝ ((𝓕 f : SchwartzMap ℝ ℂ) r) ((𝓕 f : SchwartzMap ℝ ℂ) r)=_
  exact real_inner_self_eq_norm_sq _

theorem spectralSquare_nonneg (f : SchwartzMap ℝ ℂ) (r : ℝ) :
    0≤spectralSquare f r := by rw [spectralSquare_apply]; positivity

theorem schwartz_fourier_even (f : SchwartzMap ℝ ℂ) (he : Function.Even f) :
    Function.Even ((𝓕 f : SchwartzMap ℝ ℂ)) := by
  intro r
  have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ)
    (f : ℝ → ℂ) r
  have hid : (f : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = f := by
    funext x
    exact he x
  rw [hid] at h
  exact h.symm

theorem spectralSquare_even (f : SchwartzMap ℝ ℂ) (he : Function.Even f) :
    Function.Even (spectralSquare f) := by
  intro r
  rw [spectralSquare_apply,spectralSquare_apply,schwartz_fourier_even f he r]

theorem schwartz_fourier_real (f : SchwartzMap ℝ ℂ)
    (he : Function.Even f) (hr : ∀ x,star (f x)=f x) (r : ℝ) :
    star ((𝓕 f : SchwartzMap ℝ ℂ) r)=(𝓕 f : SchwartzMap ℝ ℂ) r := by
  have hh : star ((𝓕 f : SchwartzMap ℝ ℂ) r)=(𝓕 f : SchwartzMap ℝ ℂ) (-r) := by
    change star (𝓕 (f : ℝ → ℂ) r)=𝓕 (f : ℝ → ℂ) (-r)
    rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
    change conj (∫ v : ℝ,Complex.exp (↑(-2*Real.pi*v*r)*Complex.I)*f v)=_
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    simp only [map_mul,← Complex.exp_conj,Complex.conj_ofReal,Complex.conj_I,
      show conj (f x)=f x from hr x]
    congr 2
    push_cast
    ring
  exact hh.trans (schwartz_fourier_even f he r)

theorem spectralSquare_mass_pos (f : SchwartzMap ℝ ℂ) (h0 : (∫ x,f x)≠0) :
    0<∫ r,spectralSquare f r := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (spectralSquare f).continuous (spectralSquare f).integrable (spectralSquare_nonneg f)
      (x:=0)
  rw [spectralSquare_apply]
  apply pow_ne_zero
  apply norm_ne_zero_iff.mpr
  simpa [SchwartzMap.fourier_coe,Real.fourier_eq] using h0

/-- A compact time profile witnesses the band limit of the positive square. -/
theorem spectralSquare_compact_fourier (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (hr : ∀ x,star (f x)=f x) :
    HasCompactSupport (𝓕 (fun r => (spectralSquare f r:ℂ))) := by
  let ψ := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f f
  have hψ : HasCompactSupport (ψ : ℝ → ℂ) := by
    have hid : (ψ : ℝ → ℂ) = (f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] f := by
      funext x
      exact SchwartzMap.convolution_apply _ f f x
    rw [hid]
    exact hc.convolution (ContinuousLinearMap.mul ℂ ℂ) hc
  have hs : (fun r => (spectralSquare f r:ℂ)) = ((𝓕 ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    funext r
    rw [spectralSquare_apply]
    have hz := schwartz_fourier_real f he hr r
    have him : ((𝓕 f : SchwartzMap ℝ ℂ) r).im=0 := by
      have h := congrArg Complex.im hz
      change -((𝓕 f : SchwartzMap ℝ ℂ) r).im=((𝓕 f : SchwartzMap ℝ ℂ) r).im at h
      linarith
    simp only [ψ,SchwartzMap.fourier_convolution,SchwartzMap.pairing_apply_apply,
      ContinuousLinearMap.mul_apply',Complex.sq_norm]
    apply Complex.ext <;> simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,him]
  rw [hs]
  have hid : 𝓕 ((𝓕 ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) = fun x => ψ (-x) := by
    funext x
    have h := congrFun (ψ.continuous.fourierInv_fourier_eq ψ.integrable
      (𝓕 ψ : SchwartzMap ℝ ℂ).integrable) (-x)
    rw [Real.fourierInv_eq_fourier_neg,neg_neg] at h
    exact h
  rw [hid]
  exact hψ.comp_homeomorph (Homeomorph.neg ℝ)

def normalizedSpectralSquare (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  (∫ r,spectralSquare f r)⁻¹ • spectralSquare f

theorem normalizedSpectralSquare_nonneg (f : SchwartzMap ℝ ℂ) (r : ℝ) :
    0≤normalizedSpectralSquare f r := by
  change 0≤(∫ r,spectralSquare f r)⁻¹*spectralSquare f r
  exact mul_nonneg (inv_nonneg.mpr (integral_nonneg (spectralSquare_nonneg f)))
    (spectralSquare_nonneg f r)

theorem normalizedSpectralSquare_mass_one (f : SchwartzMap ℝ ℂ)
    (h0 : (∫ x,f x)≠0) : (∫ r,normalizedSpectralSquare f r)=1 := by
  change (∫ r,(∫ u,spectralSquare f u)⁻¹*spectralSquare f r)=1
  rw [integral_const_mul,inv_mul_cancel₀ (spectralSquare_mass_pos f h0).ne']

theorem normalizedSpectralSquare_even (f : SchwartzMap ℝ ℂ) (he : Function.Even f) :
    Function.Even (normalizedSpectralSquare f) := by
  intro r
  change (∫ u,spectralSquare f u)⁻¹*spectralSquare f (-r)=
    (∫ u,spectralSquare f u)⁻¹*spectralSquare f r
  rw [spectralSquare_even f he r]

theorem normalizedSpectralSquare_compact_fourier (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (hr : ∀ x,star (f x)=f x) :
    HasCompactSupport (𝓕 (fun r => (normalizedSpectralSquare f r:ℂ))) := by
  let c : ℂ := (((∫ u,spectralSquare f u):ℝ):ℂ)⁻¹
  have hid : 𝓕 (fun r => (normalizedSpectralSquare f r:ℂ)) =
      fun x => c*𝓕 (fun r => (spectralSquare f r:ℂ)) x := by
    funext x
    rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
    simp only [normalizedSpectralSquare,smul_apply,smul_eq_mul,Complex.ofReal_mul,
      Complex.ofReal_inv]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [c]
    ring
  rw [hid]
  exact (spectralSquare_compact_fourier f hc he hr).mul_left

/-- The positive bandlimited probability kernel used for the moving windows
is constructed from a normalized compact smooth even bump. -/
theorem exists_positive_bandlimited_window_kernel :
    ∃ K : SchwartzMap ℝ ℝ, (∀ r,0≤K r) ∧ Function.Even K ∧
      (∫ r,K r)=1 ∧ HasCompactSupport (𝓕 (fun r => (K r:ℂ))) := by
  let b : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
  let φ : ℝ → ℂ := fun x => (b.normed volume x:ℂ)
  have hc : HasCompactSupport φ :=
    (b.hasCompactSupport_normed (μ:=volume)).comp_left (g:=Complex.ofReal) (by simp)
  have hφ : ContDiff ℝ ∞ φ := by
    have hb : ContDiff ℝ ∞ (b.normed volume) := b.contDiff_normed
    exact Complex.ofRealCLM.contDiff.comp hb
  let f : SchwartzMap ℝ ℂ := hc.toSchwartzMap hφ
  have he : Function.Even f := by
    intro x
    change (b.normed volume (-x):ℂ)=(b.normed volume x:ℂ)
    rw [b.normed_neg]
  have hr : ∀ x,star (f x)=f x := by intro x; change star (b.normed volume x:ℂ)=(b.normed volume x:ℂ); simp
  have h0 : (∫ x,f x)≠0 := by
    change (∫ x,(b.normed volume x:ℂ))≠0
    rw [integral_complex_ofReal,b.integral_normed]
    norm_num
  refine ⟨normalizedSpectralSquare f,normalizedSpectralSquare_nonneg f,
    normalizedSpectralSquare_even f he,normalizedSpectralSquare_mass_one f h0,?_⟩
  exact normalizedSpectralSquare_compact_fourier f hc he hr

/-- Probability-preserving dilation of the fixed spectral kernel. -/
def scaledWindowKernel (K : SchwartzMap ℝ ℝ) (R x : ℝ) : ℝ := R*K (R*x)

theorem scaledWindowKernel_integrable (K : SchwartzMap ℝ ℝ) (R : ℝ) (hR : 0<R) :
    Integrable (scaledWindowKernel K R) :=
  (K.integrable.comp_mul_left' hR.ne').const_mul R

theorem scaledWindowKernel_moment (K : SchwartzMap ℝ ℝ) (R : ℝ) (hR : 0<R) (k : ℕ) :
    (∫ x,|x|^k*scaledWindowKernel K R x) = (∫ x,|x|^k*K x)/R^k := by
  have hid (x : ℝ) : |x|^k*scaledWindowKernel K R x =
      (R/R^k)*((|R*x|^k)*K (R*x)) := by
    simp only [scaledWindowKernel,abs_mul,abs_of_pos hR,mul_pow]
    field_simp
  simp_rw [hid]
  rw [integral_const_mul,Measure.integral_comp_mul_left (fun x => |x|^k*K x) R,
    abs_inv,abs_of_pos hR,smul_eq_mul]
  field_simp

theorem scaledWindowKernel_mass_one (K : SchwartzMap ℝ ℝ) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 0<R) : (∫ x,scaledWindowKernel K R x)=1 := by
  simpa only [pow_zero,one_mul,div_one,hm] using scaledWindowKernel_moment K R hR 0

theorem scaledWindowKernel_moment_integrable (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (R : ℝ) (hR : 0<R) (k : ℕ) :
    Integrable (fun x => |x|^k*scaledWindowKernel K R x) := by
  have hi := K.integrable_pow_mul volume k
  have heq : (fun x => ‖x‖^k*‖K x‖)=(fun x => |x|^k*K x) := by
    funext x
    rw [Real.norm_eq_abs,Real.norm_of_nonneg (hK x)]
  rw [heq] at hi
  have hj := (hi.comp_mul_left' hR.ne').const_mul (R/R^k)
  convert hj using 1
  funext x
  simp only [scaledWindowKernel,abs_mul,abs_of_pos hR,mul_pow]
  field_simp

def smoothedWindow (K : SchwartzMap ℝ ℝ) (R : ℝ) (S : Set ℝ) (x : ℝ) : ℝ :=
  ∫ u in S,scaledWindowKernel K R (x-u)

theorem smoothedWindow_mem_unit (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) (S : Set ℝ) (x : ℝ) :
    smoothedWindow K R S x∈Icc (0:ℝ) 1 := by
  have hn (u : ℝ) : 0≤scaledWindowKernel K R (x-u) := mul_nonneg hR.le (hK _)
  constructor
  · exact integral_nonneg hn
  · have hi := (scaledWindowKernel_integrable K R hR).comp_sub_left x
    have hb := setIntegral_le_integral (s:=S) hi (Filter.Eventually.of_forall hn)
    rw [integral_sub_left_eq_self _ volume x,scaledWindowKernel_mass_one K hm R hR] at hb
    exact hb

theorem smoothedWindow_square_mem_unit (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) (S : Set ℝ) (x : ℝ) :
    (smoothedWindow K R S x)^2∈Icc (0:ℝ) 1 := by
  have h := smoothedWindow_mem_unit K hK hm R hR S x
  constructor
  · positivity
  · nlinarith [h.1,h.2]

theorem smoothedWindow_convolution (K : SchwartzMap ℝ ℝ) (R : ℝ)
    (S : Set ℝ) (hS : MeasurableSet S) :
    smoothedWindow K R S = S.indicator (fun _ => (1:ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ]
      scaledWindowKernel K R := by
  funext x
  unfold smoothedWindow convolution
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t∈S <;> simp [ContinuousLinearMap.mul_apply',Set.indicator,ht]

/-- Smoothing preserves the literal length of every finite measurable window. -/
theorem smoothedWindow_mass (K : SchwartzMap ℝ ℝ) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 0<R) (S : Set ℝ) (hS : MeasurableSet S)
    [IsFiniteMeasure (volume.restrict S)] :
    (∫ x,smoothedWindow K R S x)=volume.real S := by
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff hS).mpr (integrable_const (1:ℝ))
  rw [smoothedWindow_convolution K R S hS,
    integral_convolution _ hi (scaledWindowKernel_integrable K R hR),
    ContinuousLinearMap.mul_apply',scaledWindowKernel_mass_one K hm R hR,
    mul_one,integral_indicator hS,integral_const,measureReal_restrict_apply_univ]
  simp only [smul_eq_mul,mul_one]

/-- Dilation preserves probability mass and scales the Fourier support by R. -/
theorem scaledWindowKernel_fourier (K : SchwartzMap ℝ ℝ) (R : ℝ) (hR : 0<R) (y : ℝ) :
    𝓕 (fun x => (scaledWindowKernel K R x:ℂ)) y =
      𝓕 (fun x => (K x:ℂ)) (y/R) := by
  rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul,scaledWindowKernel]
  let g : ℝ → ℂ := fun u => Complex.exp (↑(-2*Real.pi*u*(y/R))*Complex.I)*(K u:ℂ)
  have hid (x : ℝ) : -2*Real.pi*(R*x)*(y/R) = -2*Real.pi*x*y := by
    field_simp
  have hi (x : ℝ) :
      Complex.exp (↑(-2*Real.pi*x*y)*Complex.I)*(↑(R*K (R*x)):ℂ) =
      (R:ℂ)*g (R*x) := by
    dsimp [g]
    rw [hid]
    simp only [Complex.ofReal_mul]
    ring
  simp_rw [hi]
  rw [integral_const_mul]
  have hs := Measure.integral_comp_mul_left g R
  rw [abs_inv,abs_of_pos hR,Complex.real_smul,Complex.ofReal_inv] at hs
  rw [hs,← mul_assoc,mul_inv_cancel₀ (by exact_mod_cast hR.ne'),one_mul]

theorem scaledWindowKernel_fourier_support (K : SchwartzMap ℝ ℝ) (A : ℝ)
    (hs : Function.support (𝓕 (fun x => (K x:ℂ))) ⊆ Icc (-A) A)
    (R : ℝ) (hR : 0<R) :
    Function.support (𝓕 (fun x => (scaledWindowKernel K R x:ℂ))) ⊆ Icc (-(A*R)) (A*R) := by
  intro y hy
  have hn : 𝓕 (fun x => (K x:ℂ)) (y/R)≠0 := by
    simpa only [Function.mem_support,scaledWindowKernel_fourier K R hR] using hy
  have hb := hs hn
  constructor
  · have h := (le_div_iff₀ hR).mp hb.1
    linarith
  · exact (div_le_iff₀ hR).mp hb.2

/-- A single actual kernel and a single bandwidth constant work for all
positive dilation scales. This supplies the quantitative propagation scale. -/
theorem exists_positive_window_kernel_uniform_bandwidth :
    ∃ (K : SchwartzMap ℝ ℝ) (A : ℝ), 0<A ∧ (∀ r,0≤K r) ∧ Function.Even K ∧
      (∫ r,K r)=1 ∧ ∀ R : ℝ,0<R →
      Function.support (𝓕 (fun x => (scaledWindowKernel K R x:ℂ))) ⊆
        Icc (-(A*R)) (A*R) := by
  obtain ⟨K,hK,he,hm,hc⟩ := exists_positive_bandlimited_window_kernel
  obtain ⟨A,hA,hb⟩ := hc.isCompact.isBounded.subset_closedBall_lt 0 (0:ℝ)
  refine ⟨K,A,hA,hK,he,hm,?_⟩
  apply scaledWindowKernel_fourier_support K A
  intro y hy
  have h := hb (subset_tsupport _ hy)
  have ha : |y|≤A := by simpa [Metric.mem_closedBall,Real.dist_eq] using h
  exact abs_le.mp ha

#print axioms scaledWindowKernel_fourier
#print axioms scaledWindowKernel_fourier_support
#print axioms exists_positive_window_kernel_uniform_bandwidth

#print axioms scaledWindowKernel_integrable
#print axioms scaledWindowKernel_moment
#print axioms scaledWindowKernel_mass_one
#print axioms scaledWindowKernel_moment_integrable
#print axioms smoothedWindow_mem_unit
#print axioms smoothedWindow_square_mem_unit
#print axioms smoothedWindow_convolution
#print axioms smoothedWindow_mass

#print axioms spectralSquare_apply
#print axioms spectralSquare_nonneg
#print axioms schwartz_fourier_even
#print axioms spectralSquare_even
#print axioms schwartz_fourier_real
#print axioms spectralSquare_mass_pos
#print axioms spectralSquare_compact_fourier
#print axioms normalizedSpectralSquare_nonneg
#print axioms normalizedSpectralSquare_mass_one
#print axioms normalizedSpectralSquare_even
#print axioms normalizedSpectralSquare_compact_fourier
#print axioms exists_positive_bandlimited_window_kernel

end QuantitativeMaass
