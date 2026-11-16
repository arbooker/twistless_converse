module

public import QuantitativeMaassAbelDiagonalTimeV1
public import QuantitativeMaassSineSinhIntegralV1
public import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology FourierTransform SchwartzMap ContDiff Convolution ComplexConjugate

namespace QuantitativeMaass

/-- Absolute joint integrability needed for the spherical transform. -/
theorem spherical_sine_pair_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fun p : ℝ × ℝ => h p.1*(p.1:ℂ)*
      ((Real.sin (p.1*p.2)/Real.sinh (p.2/2):ℝ):ℂ))
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hm := (h.integrable_pow_mul volume 2).mul_prod time_sinh_half_integrable
  apply hm.mono' ((show Measurable _ from by fun_prop).aestronglyMeasurable)
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (self_mem_ae_restrict measurableSet_Ioi)] with p hp
  have hs : 0<Real.sinh (p.2/2) := Real.sinh_pos_iff.mpr (div_pos hp (by norm_num))
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hs]
  calc
    _ ≤ ‖h p.1‖*|p.1| *(|p.1*p.2|/Real.sinh (p.2/2)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right Real.abs_sin_le_abs hs.le) (by positivity)
    _ = _ := by rw [abs_mul, abs_of_pos hp]; ring

/-- Fubini and the exact sine transform identify the spherical density. -/
theorem spherical_sine_fubini (h : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ in Ioi 0, ∫ r : ℝ, h r*(r:ℂ)*
      ((Real.sin (r*t)/Real.sinh (t/2):ℝ):ℂ)) =
      (Real.pi:ℂ)*(∫ r : ℝ, h r*((r*Real.tanh (Real.pi*r):ℝ):ℂ)) := by
  have hi : Integrable (Function.uncurry (fun t r : ℝ => h r*(r:ℂ)*
      ((Real.sin (r*t)/Real.sinh (t/2):ℝ):ℂ)))
      ((volume.restrict (Ioi 0)).prod volume) := (spherical_sine_pair_integrable h).swap
  rw [integral_integral_swap hi]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  rw [integral_const_mul, integral_complex_ofReal, sine_sinh_half_integral]
  simp only [Complex.ofReal_mul]
  ring

/-- The Fourier transform with angular frequency, as a genuine Schwartz map. -/
def angularFourier (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ
      (Units.mk0 ((2*Real.pi)⁻¹) (inv_ne_zero (by positivity)))) (𝓕 f)

theorem angularFourier_apply (f : SchwartzMap ℝ ℂ) (r : ℝ) :
    angularFourier f r = (𝓕 f : SchwartzMap ℝ ℂ) (r/(2*Real.pi)) := by
  rfl

/-- The cosine transform of a Schwartz function is the symmetric Fourier transform. -/
theorem schwartz_cosinePacket_fourier (f : SchwartzMap ℝ ℂ) (r : ℝ) :
    cosinePacket f r = ((𝓕 f : SchwartzMap ℝ ℂ) (-r/(2*Real.pi))+
      (𝓕 f : SchwartzMap ℝ ℂ) (r/(2*Real.pi)))/2 := by
  let p := fun s t : ℝ => Complex.exp ((t*s:ℝ)*Complex.I)*f t
  have hi (s : ℝ) : Integrable (p s) := by
    apply f.integrable.norm.mono' (by dsimp [p]; fun_prop)
    filter_upwards with t
    simp only [p, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  have hfourier (s : ℝ) : (∫ t,p s t)=(𝓕 f : SchwartzMap ℝ ℂ) (-s/(2*Real.pi)) := by
    change _=𝓕 (f : ℝ → ℂ) (-s/(2*Real.pi))
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with t
    have he : -2*Real.pi*t*(-s/(2*Real.pi))=t*s := by field_simp
    simp only [p,he,smul_eq_mul]
  have hp (t : ℝ) : f t*(Real.cos (t*r):ℂ)=(p r t+p (-r) t)/2 := by
    rw [Complex.ofReal_cos]
    dsimp [Complex.cos,p]
    rw [mul_neg,Complex.ofReal_neg]
    ring
  unfold cosinePacket
  simp_rw [hp]
  rw [integral_div,integral_add (hi r) (hi (-r)),hfourier r,hfourier (-r),neg_neg]

theorem cosinePacket_eq_angularFourier (f : SchwartzMap ℝ ℂ) (he : Function.Even f)
    (r : ℝ) : cosinePacket f r=angularFourier f r := by
  rw [schwartz_cosinePacket_fourier, neg_div, schwartz_fourier_even f he, angularFourier_apply]
  ring

theorem angularFourier_even (f : SchwartzMap ℝ ℂ) (he : Function.Even f) :
    Function.Even (angularFourier f) := by
  intro r
  simp only [angularFourier_apply, neg_div]
  exact schwartz_fourier_even f he _

/-- Fourier inversion in exactly the normalization used by the wave packets. -/
theorem cosinePacket_angularFourier (f : SchwartzMap ℝ ℂ) (he : Function.Even f)
    (t : ℝ) : cosinePacket (angularFourier f) t=(2*Real.pi:ℂ)*f t := by
  let F : SchwartzMap ℝ ℂ := 𝓕 f
  have hinv (x : ℝ) : (𝓕 F : SchwartzMap ℝ ℂ) x=f (-x) := by
    have h := congrFun (f.continuous.fourierInv_fourier_eq f.integrable F.integrable) (-x)
    rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h
    exact h
  have hd := Measure.integral_comp_div (fun u : ℝ => F u*(Real.cos (u*((2*Real.pi)*t)):ℂ)) (2*Real.pi)
  have hc : cosinePacket (angularFourier f) t=(2*Real.pi:ℂ)*cosinePacket F ((2*Real.pi)*t) := by
    unfold cosinePacket
    simp only [abs_of_pos (by positivity : 0<2*Real.pi), Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_ofNat] at hd
    rw [← hd]
    apply integral_congr_ae
    filter_upwards with r
    rw [angularFourier_apply]
    congr 2
    field_simp
  rw [hc, schwartz_cosinePacket_fourier, hinv, hinv]
  have hp : -(-((2*Real.pi)*t)/(2*Real.pi))=t := by field_simp
  have hm : -(((2*Real.pi)*t)/(2*Real.pi))= -t := by field_simp
  rw [hp,hm,he t]
  ring

theorem schwartz_cosinePacket_integrable (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    Integrable (fun r : ℝ => f r*(Real.cos (r*t):ℂ)) := by
  apply f.integrable.norm.mono' (by fun_prop)
  filter_upwards with r
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)

/-- Differentiation of the actual cosine packet, with an integrable first moment. -/
theorem schwartz_cosinePacket_hasDerivAt (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    HasDerivAt (cosinePacket f)
      (-(∫ r : ℝ, f r*(r:ℂ)*(Real.sin (r*t):ℂ))) t := by
  let F : ℝ → ℝ → ℂ := fun t r => f r*(Real.cos (r*t):ℂ)
  let D : ℝ → ℝ → ℂ := fun t r => f r*((-Real.sin (r*t)*r:ℝ):ℂ)
  have hd (r x : ℝ) : HasDerivAt (fun t => F t r) (D x r) x := by
    have hc := (Real.hasDerivAt_cos (r*x)).comp x ((hasDerivAt_id x).const_mul r)
    have hz := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hc
    simpa only [F, D, Function.comp_def, Complex.ofRealCLM_apply, mul_one] using hz.const_mul (f r)
  have hb : ∀ᵐ r : ℝ, ∀ x ∈ (univ : Set ℝ), ‖D x r‖≤‖r‖*‖f r‖ := by
    filter_upwards with r
    intro x _
    simp only [D, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    calc
      _ ≤ ‖f r‖*(1*|r|) := by gcongr; exact Real.abs_sin_le_one _
      _ = _ := by ring
  have hi : Integrable (fun r : ℝ => ‖r‖*‖f r‖) := by
    simpa only [pow_one] using f.integrable_pow_mul volume 1
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (s := univ) (bound := fun r : ℝ => ‖r‖*‖f r‖)
    (Filter.univ_mem : (univ : Set ℝ) ∈ 𝓝 t)
    (Eventually.of_forall (fun x => by dsimp [F]; fun_prop))
    (schwartz_cosinePacket_integrable f t) (by dsimp [D]; fun_prop) hb hi
    (Eventually.of_forall (fun r x _ => hd r x))
  have heq : (∫ r, D t r)= -(∫ r, f r*(r:ℂ)*(Real.sin (r*t):ℂ)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with r
    simp only [D, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [heq] at h
  exact h.2

/-- The derivative of an even Schwartz function is its inverse sine transform. -/
theorem schwartz_deriv_sine_inversion (f : SchwartzMap ℝ ℂ) (he : Function.Even f)
    (t : ℝ) : deriv f t= -(1/(2*Real.pi):ℂ)*
      (∫ r : ℝ, angularFourier f r*(r:ℂ)*(Real.sin (r*t):ℂ)) := by
  have h₁ := schwartz_cosinePacket_hasDerivAt (angularFourier f) t
  have hfun : cosinePacket (angularFourier f)=fun t => (2*Real.pi:ℂ)*f t :=
    funext (cosinePacket_angularFourier f he)
  rw [hfun] at h₁
  have h₂ := (f.differentiable t).hasDerivAt.const_mul (2*Real.pi:ℂ)
  have h := h₁.unique h₂
  have hn : (2*Real.pi:ℂ)≠0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  calc
    deriv f t= -(∫ r : ℝ, angularFourier f r*(r:ℂ)*(Real.sin (r*t):ℂ))/(2*Real.pi:ℂ) := by
      apply (eq_div_iff hn).mpr
      linear_combination -h
    _ = _ := by ring

/-- Fourier evaluation of the diagonal time functional, with no transform premise. -/
theorem schwartz_diagonal_time_fourier (f : SchwartzMap ℝ ℂ) (he : Function.Even f) :
    (∫ t : ℝ in Ioi 0, deriv f t/(Real.sinh (t/2):ℂ)) =
      -(1/2:ℂ)*(∫ r : ℝ, angularFourier f r*((r*Real.tanh (Real.pi*r):ℝ):ℂ)) := by
  have hb : (∫ t : ℝ in Ioi 0,
      (∫ r : ℝ, angularFourier f r*(r:ℂ)*(Real.sin (r*t):ℂ))/(Real.sinh (t/2):ℂ)) =
      (Real.pi:ℂ)*(∫ r : ℝ, angularFourier f r*((r*Real.tanh (Real.pi*r):ℝ):ℂ)) := by
    rw [← spherical_sine_fubini (angularFourier f)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards with r
    simp only [Complex.ofReal_div]
    ring
  calc
    _ = -(1/(2*Real.pi):ℂ)*(∫ t : ℝ in Ioi 0,
        (∫ r : ℝ, angularFourier f r*(r:ℂ)*(Real.sin (r*t):ℂ))/(Real.sinh (t/2):ℂ)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [schwartz_deriv_sine_inversion f he t]
      ring
    _ = _ := by
      rw [hb]
      have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp
      simp only [mul_comm Real.pi]

/-- Absolute integrability of the genuine spherical density. -/
theorem schwartz_spherical_density_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fun r : ℝ => h r*((r*Real.tanh (Real.pi*r):ℝ):ℂ)) := by
  have hi : Integrable (fun r : ℝ => ‖r‖*‖h r‖) := by
    simpa only [pow_one] using h.integrable_pow_mul volume 1
  apply hi.mono' ((show Measurable _ from by
    simp only [Real.tanh_eq_sinh_div_cosh]
    fun_prop).aestronglyMeasurable)
  filter_upwards with r
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ‖h r‖*(|r| *1) := by gcongr; exact (Real.abs_tanh_lt_one _).le
    _ = _ := by ring

theorem compact_cosinePacket_spherical_integrable (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) :
    Integrable (fun r : ℝ => cosinePacket f r*((r*Real.tanh (Real.pi*r):ℝ):ℂ)) := by
  let F : SchwartzMap ℝ ℂ := hc.toSchwartzMap hf
  have hF : Function.Even F := he
  have hcos (r : ℝ) : angularFourier F r=cosinePacket f r :=
    (cosinePacket_eq_angularFourier F hF r).symm
  simpa only [hcos] using schwartz_spherical_density_integrable (angularFourier F)

/-- Exact spherical Plancherel density for the original compact even time packet.
The radial profile is the genuine one-sided cosh lift. -/
theorem abelProfile_evenCoshLift_fourier (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) :
    abelProfile (evenCoshLift f) 1 =
      (1/(4*Real.pi):ℂ)*(∫ r : ℝ, cosinePacket f r*((r*Real.tanh (Real.pi*r):ℝ):ℂ)) := by
  let F : SchwartzMap ℝ ℂ := hc.toSchwartzMap hf
  have hF : Function.Even F := he
  have ht := schwartz_diagonal_time_fourier F hF
  have hcos (r : ℝ) : angularFourier F r=cosinePacket f r :=
    (cosinePacket_eq_angularFourier F hF r).symm
  simp only [hcos] at ht
  change (∫ t : ℝ in Ioi 0, deriv f t/(Real.sinh (t/2):ℂ)) = _ at ht
  rw [abelProfile_evenCoshLift_one f hf he hc, ht]
  ring

/-- Ordinary time convolution, retaining its Schwartz structure. -/
def timeConvolution (f g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g

theorem timeConvolution_compact (f g : SchwartzMap ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) (hg : HasCompactSupport (g : ℝ → ℂ)) :
    HasCompactSupport (timeConvolution f g : ℝ → ℂ) := by
  have heq : (timeConvolution f g : ℝ → ℂ)=
      (f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] g := by
    funext t
    exact SchwartzMap.convolution_apply _ f g t
  rw [heq]
  exact hf.convolution (ContinuousLinearMap.mul ℂ ℂ) hg

theorem timeConvolution_even (f g : SchwartzMap ℝ ℂ)
    (hf : Function.Even f) (hg : Function.Even g) : Function.Even (timeConvolution f g) := by
  intro t
  simp only [timeConvolution, SchwartzMap.convolution_apply]
  exact convolution_neg_of_neg_eq (ContinuousLinearMap.mul ℂ ℂ)
    (Eventually.of_forall hf) (Eventually.of_forall hg)

theorem angularFourier_timeConvolution (f g : SchwartzMap ℝ ℂ) (r : ℝ) :
    angularFourier (timeConvolution f g) r=angularFourier f r*angularFourier g r := by
  simp only [angularFourier_apply, timeConvolution, SchwartzMap.fourier_convolution,
    SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply']

theorem cosinePacket_timeConvolution (f g : SchwartzMap ℝ ℂ)
    (hf : Function.Even f) (hg : Function.Even g) (r : ℝ) :
    cosinePacket (timeConvolution f g) r=cosinePacket f r*cosinePacket g r := by
  rw [cosinePacket_eq_angularFourier _ (timeConvolution_even f g hf hg),
    angularFourier_timeConvolution, cosinePacket_eq_angularFourier f hf,
    cosinePacket_eq_angularFourier g hg]

/-- The exact identity contribution of a time convolution is the product density. -/
theorem abelProfile_timeConvolution_diagonal (f g : SchwartzMap ℝ ℂ)
    (hf : Function.Even f) (hg : Function.Even g)
    (hfc : HasCompactSupport (f : ℝ → ℂ)) (hgc : HasCompactSupport (g : ℝ → ℂ)) :
    abelProfile (evenCoshLift (timeConvolution f g)) 1=(1/(4*Real.pi):ℂ)*
      (∫ r : ℝ, (cosinePacket f r*cosinePacket g r)*((r*Real.tanh (Real.pi*r):ℝ):ℂ)) := by
  rw [abelProfile_evenCoshLift_fourier _ ((timeConvolution f g).smooth ⊤)
    (timeConvolution_even f g hf hg) (timeConvolution_compact f g hfc hgc)]
  simp_rw [cosinePacket_timeConvolution f g hf hg]

/-- For real even packets the convolution diagonal is the positive squared
spectral density. This does not yet identify it with radial squared energy. -/
theorem abelProfile_timeSquare_diagonal (f : SchwartzMap ℝ ℂ)
    (hf : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (hc : HasCompactSupport (f : ℝ → ℂ)) :
    abelProfile (evenCoshLift (timeConvolution f f)) 1=(1/(4*Real.pi):ℂ)*
      (∫ r : ℝ, ((‖cosinePacket f r‖^2*r*Real.tanh (Real.pi*r):ℝ):ℂ)) := by
  rw [abelProfile_timeConvolution_diagonal f f hf hf hc hc]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  have hz : conj (cosinePacket f r)=cosinePacket f r := by
    rw [cosinePacket_eq_angularFourier f hf, angularFourier_apply]
    exact schwartz_fourier_real f hf hr _
  have hs : cosinePacket f r*cosinePacket f r=(‖cosinePacket f r‖^2:ℝ) := by
    calc
      _ = cosinePacket f r*conj (cosinePacket f r) := by rw [hz]
      _ = _ := by rw [Complex.mul_conj']; norm_cast
  rw [hs]
  simp only [Complex.ofReal_mul]
  ring

end QuantitativeMaass

#print axioms QuantitativeMaass.spherical_sine_pair_integrable
#print axioms QuantitativeMaass.spherical_sine_fubini
#print axioms QuantitativeMaass.angularFourier_apply
#print axioms QuantitativeMaass.schwartz_cosinePacket_fourier
#print axioms QuantitativeMaass.cosinePacket_eq_angularFourier
#print axioms QuantitativeMaass.angularFourier_even
#print axioms QuantitativeMaass.cosinePacket_angularFourier
#print axioms QuantitativeMaass.schwartz_cosinePacket_integrable
#print axioms QuantitativeMaass.schwartz_cosinePacket_hasDerivAt
#print axioms QuantitativeMaass.schwartz_deriv_sine_inversion
#print axioms QuantitativeMaass.schwartz_diagonal_time_fourier
#print axioms QuantitativeMaass.schwartz_spherical_density_integrable
#print axioms QuantitativeMaass.compact_cosinePacket_spherical_integrable
#print axioms QuantitativeMaass.abelProfile_evenCoshLift_fourier
#print axioms QuantitativeMaass.timeConvolution_compact
#print axioms QuantitativeMaass.timeConvolution_even
#print axioms QuantitativeMaass.angularFourier_timeConvolution
#print axioms QuantitativeMaass.cosinePacket_timeConvolution
#print axioms QuantitativeMaass.abelProfile_timeConvolution_diagonal
#print axioms QuantitativeMaass.abelProfile_timeSquare_diagonal
