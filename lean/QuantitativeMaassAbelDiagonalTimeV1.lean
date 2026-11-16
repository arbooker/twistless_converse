module

public import QuantitativeMaassEvenPacketEnergyBoundsV1
public import QuantitativeMaassAbelNormalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Exact half-line substitution, valid for an arbitrary integrand under
Bochner's conventions. No global smooth extension is required. -/
theorem abelIntegral_one_time_general (g : ℝ → ℂ) :
    abelIntegral g 1=(Real.sqrt 2/2:ℂ)*
      ∫ t in Ioi (0:ℝ),(Real.cosh (t/2):ℂ)*g (Real.cosh t) := by
  have hp : 0<Real.sqrt 2 := by positivity
  have him : abelTimeCoordinate '' Ioi (0:ℝ)=Ioi (0:ℝ) := by
    ext s
    constructor
    · rintro ⟨t,ht,rfl⟩
      change 0<Real.sqrt 2*Real.sinh (t/2)
      exact mul_pos hp (Real.sinh_pos_iff.mpr (div_pos ht (by norm_num)))
    · intro hs
      refine ⟨2*Real.arsinh (s/Real.sqrt 2),?_,?_⟩
      · exact mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (div_pos hs hp))
      · simp only [abelTimeCoordinate,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0),Real.sinh_arsinh]
        exact mul_div_cancel₀ s hp.ne'
  have hinj : InjOn abelTimeCoordinate (Ioi (0:ℝ)) := by
    intro t _ u _ h
    have h1 : Real.sinh (t/2)=Real.sinh (u/2) := mul_left_cancel₀ hp.ne' h
    have h2 := Real.sinh_injective h1
    linarith
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (abelTimeCoordinate_hasDerivAt t).hasDerivWithinAt) hinj (fun s : ℝ => g (1+s^2))
  rw [him] at h
  change abelIntegral g 1=_ at h
  rw [h,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [abelTimeCoordinate_sq,abs_of_pos (by positivity : 0<Real.sqrt 2/2*Real.cosh (t/2))]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  ring

/-- The ordinary derivative of the radial lift at cosh(t), strictly away
from the boundary, is the time derivative divided by sinh(t). -/
theorem evenCoshLift_deriv_cosh (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (t : ℝ) (ht : 0<t) :
    deriv (evenCoshLift f) (Real.cosh t)=deriv f t/(Real.sinh t:ℂ) := by
  have hq : 1<Real.cosh t := Real.one_lt_cosh.mpr ht.ne'
  have hd := (((evenCoshLift_smoothOn f hf he hc) _ hq.le).contDiffAt
    (Ici_mem_nhds hq)).differentiableAt (by simp)
  have h := (hd.hasDerivAt.scomp t (Real.hasDerivAt_cosh t)).deriv
  have heq : (fun x => evenCoshLift f (Real.cosh x))=f := funext (evenCoshLift_time f he)
  change deriv (fun x => evenCoshLift f (Real.cosh x)) t=
    (Real.sinh t) • deriv (evenCoshLift f) (Real.cosh t) at h
  rw [heq,Complex.real_smul] at h
  have hn : (Real.sinh t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr ht).ne'
  apply (eq_div_iff hn).mpr
  rw [h,mul_comm]

/-- Exact identity contribution in time coordinates. The coefficient is
proved; identifying its Fourier-side Plancherel density is a separate step. -/
theorem abelProfile_evenCoshLift_one (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) :
    abelProfile (evenCoshLift f) 1= -(1/(2*Real.pi):ℂ)*
      ∫ t in Ioi (0:ℝ),deriv f t/(Real.sinh (t/2):ℂ) := by
  rw [abelProfile,abelIntegral_one_time_general]
  have heq : (∫ t in Ioi (0:ℝ),(Real.cosh (t/2):ℂ)*deriv (evenCoshLift f) (Real.cosh t))=
      (1/2:ℂ)*∫ t in Ioi (0:ℝ),deriv f t/(Real.sinh (t/2):ℂ) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [evenCoshLift_deriv_cosh f hf he hc t ht]
    have hst : Real.sinh t=2*Real.sinh (t/2)*Real.cosh (t/2) := by
      have h := Real.sinh_two_mul (t/2)
      rw [show 2*(t/2)=t by ring] at h
      exact h
    have hs : (Real.sinh (t/2):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
      (Real.sinh_pos_iff.mpr (div_pos ht (by norm_num))).ne'
    have hcos : (Real.cosh (t/2):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
    rw [hst]
    simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
    field_simp
  rw [heq]
  have hsqrt : (Real.sqrt 2:ℂ)^2=2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination - (∫ t in Ioi (0:ℝ),deriv f t/(Real.sinh (t/2):ℂ))*hsqrt


/-- The identity-term integral is absolutely integrable. Evenness removes
the apparent singularity at zero, via f'(t)=t Df(t) and sinh(t/2)>=t/2. -/
theorem evenTime_diagonal_integrable (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) :
    IntegrableOn (fun t => deriv f t/(Real.sinh (t/2):ℂ)) (Ioi (0:ℝ)) := by
  obtain ⟨C,hC⟩ := (evenRadialDerivative_compact f hf he hc).exists_bound_of_continuous
    (evenRadialDerivative_smooth f hf hc).continuous
  have hC0 : 0≤C := (norm_nonneg (evenRadialDerivative f 0)).trans (hC 0)
  obtain ⟨A,hA,hAs⟩ := hc.deriv.isCompact.isBounded.subset_closedBall_lt 0 (0:ℝ)
  let bound : ℝ → ℝ := (Icc 0 A).indicator (fun _ => 2*C)
  have hi : Integrable bound := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hm : Measurable (fun t => deriv f t/(Real.sinh (t/2):ℂ)) := by
    apply (contDiff_infty_iff_deriv.mp hf).2.continuous.measurable.div
    exact (Complex.continuous_ofReal.comp (Real.continuous_sinh.comp (continuous_id.div_const 2))).measurable
  apply hi.integrableOn.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  by_cases hta : t∈Icc (0:ℝ) A
  · simp only [bound,indicator_of_mem hta]
    have hsh : 0<Real.sinh (t/2) := Real.sinh_pos_iff.mpr (div_pos ht (by norm_num))
    rw [← evenRadialDerivative_identity f hf he t,norm_div,norm_smul,
      Real.norm_eq_abs,abs_of_pos ht,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsh]
    apply (div_le_iff₀ hsh).mpr
    have hn := mul_le_mul_of_nonneg_left (hC t) ht.le
    have hh : t/2≤Real.sinh (t/2) := Real.self_le_sinh_iff.mpr (div_nonneg ht.le (by norm_num))
    nlinarith
  · have hz : deriv f t=0 := by
      by_contra hn
      have hb := hAs (subset_tsupport (deriv f) hn)
      have hab : |t|≤A := by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hb
      exact hta ⟨ht.le,(le_abs_self t).trans hab⟩
    simp only [bound,indicator_of_notMem hta,hz,zero_div,norm_zero,le_refl]

#print axioms evenTime_diagonal_integrable

#print axioms abelIntegral_one_time_general
#print axioms evenCoshLift_deriv_cosh
#print axioms abelProfile_evenCoshLift_one

end QuantitativeMaass
