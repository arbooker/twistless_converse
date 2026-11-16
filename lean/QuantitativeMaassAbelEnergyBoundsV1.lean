module

public import QuantitativeMaassAbelCutoffDerivativeBoundV1
public import QuantitativeMaassAbelIntertwiningV1
public import QuantitativeMaassAbelPositiveProfileV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Squared radial energy retains the full support-width gain. -/
theorem abelProfile_square_energy_bound (F : ℝ → ℂ) (B C : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) (hb : ∀ q,‖deriv F q‖≤C) :
    (2*Real.pi)*(∫ q in Ioi (1:ℝ),‖abelProfile F q‖^2) ≤
      (2*Real.pi)*((Real.sqrt 2/Real.pi)*(C*Real.sqrt (B-1)))^2*(B-1) := by
  have he : (∫ q in Ioi (1:ℝ),‖abelProfile F q‖^2)=
      ∫ q in Ioc (1:ℝ) B,‖abelProfile F q‖^2 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ h => h.1)
    intro q hq
    have hhigh : B<q := by
      by_contra hn
      exact hq.2 ⟨hq.1,le_of_not_gt hn⟩
    have hz : abelProfile F q=0 := by
      by_contra hn
      exact (not_le_of_gt hhigh) (abelProfile_support F B hs hn)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Ioc (1:ℝ) B)
    (f:=fun q => ‖abelProfile F q‖^2) (by simp) (fun q hq => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (abelProfile_small_radius_bound F B C hB hs hb q hq.1.le) 2)
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _)),
    Real.volume_real_Ioc_of_le hB] at h
  rw [he]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (by positivity : 0≤2*Real.pi)

/-- The unnormalized shrinking cutoff has uniformly bounded radial energy:
its reciprocal-width derivative is cancelled by the squared support gain. -/
theorem abelCutoff_square_energy_bound (D : ℝ) (hD : 0≤D)
    (hDb : ∀ q,|deriv Real.smoothTransition q|≤D)
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) :
    (2*Real.pi)*(∫ q in Ioi (1:ℝ),‖abelProfile (abelCutoff a) q‖^2) ≤
      (2*Real.pi)*(Real.sqrt 2/Real.pi)^2*(2*D)^2 := by
  have h := abelProfile_square_energy_bound (abelCutoff a) (1+a) (2*D/a)
    (by linarith) (abelCutoff_support a ha)
    (abelCutoff_derivative_bound D hD hDb a ha ha1)
  apply h.trans_eq
  rw [show (1+a)-1=a by ring,mul_pow,mul_pow,Real.sq_sqrt ha.le,div_pow]
  field_simp [ha.ne',Real.pi_ne_zero]

theorem abelCutoff_square_energy_uniform :
    ∃ C : ℝ,0<C ∧ ∀ a : ℝ,0<a → a≤1 →
      (2*Real.pi)*(∫ q in Ioi (1:ℝ),‖abelProfile (abelCutoff a) q‖^2)≤C := by
  obtain ⟨D,hD,hDb⟩ := smoothTransition_deriv_bounded
  refine ⟨(2*Real.pi)*(Real.sqrt 2/Real.pi)^2*(2*D)^2+1,by positivity,?_⟩
  intro a ha ha1
  exact (abelCutoff_square_energy_bound D hD hDb a ha ha1).trans (by linarith)

/-- The central half of a short time cutoff has a fixed positive height. -/
theorem abelCutoff_time_core_lower (R t : ℝ) (hR : 0<R) (ht : |t|≤R/2) :
    1-Real.smoothTransition (1/2) ≤ abelCutoffReal (Real.cosh R-1) (Real.cosh t) := by
  have hcos : Real.cosh t≤Real.cosh (R/2) := Real.cosh_le_cosh.mpr (by
    rwa [abs_of_pos (half_pos hR)])
  have hdouble := Real.cosh_two_mul (R/2)
  rw [show 2*(R/2)=R by ring] at hdouble
  have hid := Real.cosh_sq_sub_sinh_sq (R/2)
  have hhalf := Real.one_le_cosh (R/2)
  have ha : 0<Real.cosh R-1 := sub_pos.mpr (Real.one_lt_cosh.mpr hR.ne')
  have harg : (Real.cosh t-1)/(Real.cosh R-1)≤1/2 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith [sq_nonneg (Real.cosh (R/2)-1)]
  unfold abelCutoffReal
  rw [Real.smoothTransition.one_of_one_le
    (by linarith [Real.one_le_cosh t] : 1≤Real.cosh t+1),one_mul]
  exact sub_le_sub_left (Real.smoothTransition.monotone harg) 1

/-- A quantitative lower bound for the full time mass, uniform as R tends
to zero. The positive constant is fixed independently of the radius. -/
theorem abelCutoff_time_mass_lower (R : ℝ) (hR : 0<R) :
    (1-Real.smoothTransition (1/2))*R ≤
      ∫ t,abelCutoffReal (Real.cosh R-1) (Real.cosh t) := by
  let w : ℝ → ℝ := fun t => abelCutoffReal (Real.cosh R-1) (Real.cosh t)
  have hc : Continuous w := (abelCutoffReal_smooth _).continuous.comp Real.continuous_cosh
  have hs : Function.support w⊆Icc (-R) R := by
    intro t ht
    apply coshTimeTest_support (abelCutoff (Real.cosh R-1)) R hR.le
      (abelCutoff_radius_support R hR)
    simpa only [Function.mem_support,coshTimeTest,abelCutoff,w,ne_eq,Complex.ofReal_eq_zero] using ht
  have hi : Integrable w := hc.integrable_of_hasCompactSupport
    ((isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset isClosed_closure
      (closure_minimal hs isClosed_Icc))
  have hle : -R/2≤R/2 := by linarith
  calc
    _ = ∫ _t in Ioc (-R/2) (R/2),(1-Real.smoothTransition (1/2)) := by
      rw [setIntegral_const,Real.volume_real_Ioc_of_le hle,smul_eq_mul]
      ring
    _ ≤ ∫ t in Ioc (-R/2) (R/2),w t := by
      apply setIntegral_mono_on (integrableOn_const (by simp)) hi.integrableOn measurableSet_Ioc
      intro t ht
      exact abelCutoff_time_core_lower R t hR (abs_le.mpr ⟨by linarith [ht.1],ht.2⟩)
    _ ≤ _ := setIntegral_le_integral hi (Eventually.of_forall (fun t => abelCutoffReal_nonneg _ _))

theorem abelCutoff_time_mass_uniform_lower :
    ∃ c : ℝ,0<c ∧ ∀ R : ℝ,0<R →
      c*R≤∫ t,abelCutoffReal (Real.cosh R-1) (Real.cosh t) :=
  ⟨1-Real.smoothTransition (1/2),sub_pos.mpr
    (Real.smoothTransition.lt_one_of_lt_one (by norm_num)),abelCutoff_time_mass_lower⟩

#print axioms abelProfile_square_energy_bound
#print axioms abelCutoff_square_energy_bound
#print axioms abelCutoff_square_energy_uniform
#print axioms abelCutoff_time_core_lower
#print axioms abelCutoff_time_mass_lower
#print axioms abelCutoff_time_mass_uniform_lower

end QuantitativeMaass
