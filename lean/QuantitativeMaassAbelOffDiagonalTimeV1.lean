module

public import QuantitativeMaassPacketDiagonalV1
public import QuantitativeMaassAbelDiagonalTimeV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The change from radial distance to the quadratic Abel variable. -/
def abelRadiusTimeCoordinate (d u : ℝ) : ℝ :=
  Real.sqrt (Real.cosh u-Real.cosh d)

theorem cosh_sub_pos_of_nonneg_lt (d u : ℝ) (hd : 0≤d) (hu : d<u) :
    0<Real.cosh u-Real.cosh d := by
  apply sub_pos.mpr
  apply Real.cosh_lt_cosh.mpr
  simpa only [abs_of_nonneg hd,abs_of_pos (lt_of_le_of_lt hd hu)] using hu

theorem abelRadiusTimeCoordinate_pos (d u : ℝ) (hd : 0≤d) (hu : d<u) :
    0<abelRadiusTimeCoordinate d u :=
  Real.sqrt_pos.mpr (cosh_sub_pos_of_nonneg_lt d u hd hu)

theorem abelRadiusTimeCoordinate_sq (d u : ℝ) (hd : 0≤d) (hu : d<u) :
    Real.cosh d+(abelRadiusTimeCoordinate d u)^2=Real.cosh u := by
  rw [abelRadiusTimeCoordinate,Real.sq_sqrt
    (cosh_sub_pos_of_nonneg_lt d u hd hu).le]
  ring

theorem abelRadiusTimeCoordinate_hasDerivAt (d u : ℝ) (hd : 0≤d) (hu : d<u) :
    HasDerivAt (abelRadiusTimeCoordinate d)
      (Real.sinh u/(2*abelRadiusTimeCoordinate d u)) u := by
  exact ((Real.hasDerivAt_cosh u).sub_const (Real.cosh d)).sqrt
    (cosh_sub_pos_of_nonneg_lt d u hd hu).ne'

theorem abelRadiusTimeCoordinate_image (d : ℝ) (hd : 0≤d) :
    abelRadiusTimeCoordinate d '' Ioi d=Ioi (0:ℝ) := by
  ext s
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact abelRadiusTimeCoordinate_pos d u hd hu
  · intro hs
    have hq : 1≤Real.cosh d+s^2 := by nlinarith [Real.one_le_cosh d,sq_nonneg s]
    refine ⟨Real.arcosh (Real.cosh d+s^2),?_,?_⟩
    · change d<Real.arcosh (Real.cosh d+s^2)
      have hc : Real.cosh d<Real.cosh (Real.arcosh (Real.cosh d+s^2)) := by
        rw [Real.cosh_arcosh hq]
        nlinarith [sq_pos_of_pos hs]
      have hh := Real.cosh_lt_cosh.mp hc
      simpa only [abs_of_nonneg hd,abs_of_nonneg (Real.arcosh_nonneg hq)] using hh
    · simp only [abelRadiusTimeCoordinate,Real.cosh_arcosh hq,add_sub_cancel_left,
        Real.sqrt_sq (le_of_lt hs)]

theorem abelRadiusTimeCoordinate_injOn (d : ℝ) (hd : 0≤d) :
    InjOn (abelRadiusTimeCoordinate d) (Ioi d) := by
  intro u hu v hv huv
  apply Real.cosh_injOn (hd.trans hu.le) (hd.trans hv.le)
  rw [← abelRadiusTimeCoordinate_sq d u hd hu,
    ← abelRadiusTimeCoordinate_sq d v hd hv,huv]

/-- Exact substitution for any complex integrand, with Bochner's convention
for nonintegrable functions. Absolute integrability is proved separately below. -/
theorem abelIntegral_cosh_time_general (g : ℝ → ℂ) (d : ℝ) (hd : 0≤d) :
    abelIntegral g (Real.cosh d)=
      ∫ u in Ioi d,(Real.sinh u/(2*abelRadiusTimeCoordinate d u):ℝ) • g (Real.cosh u) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u hu => (abelRadiusTimeCoordinate_hasDerivAt d u hd hu).hasDerivWithinAt)
    (abelRadiusTimeCoordinate_injOn d hd) (fun s : ℝ => g (Real.cosh d+s^2))
  rw [abelRadiusTimeCoordinate_image d hd] at h
  change abelIntegral g (Real.cosh d)=_ at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [abelRadiusTimeCoordinate_sq d u hd hu,abs_of_pos
    (div_pos (Real.sinh_pos_iff.mpr (lt_of_le_of_lt hd hu))
      (mul_pos (by norm_num) (abelRadiusTimeCoordinate_pos d u hd hu)))]

/-- Cancellation of the Jacobian against the derivative of the radial lift. -/
theorem abelRadiusTimeCoordinate_lift_deriv (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f)
    (d u : ℝ) (hd : 0≤d) (hu : d<u) :
    (Real.sinh u/(2*abelRadiusTimeCoordinate d u):ℝ) •
      deriv (evenCoshLift f) (Real.cosh u)=
      (1/2:ℂ)*(deriv f u/(abelRadiusTimeCoordinate d u:ℂ)) := by
  rw [evenCoshLift_deriv_cosh f hf he hc u (lt_of_le_of_lt hd hu),Complex.real_smul]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hs : (Real.sinh u:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sinh_pos_iff.mpr (lt_of_le_of_lt hd hu)).ne'
  have hr : (abelRadiusTimeCoordinate d u:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (abelRadiusTimeCoordinate_pos d u hd hu).ne'
  field_simp

/-- Exact off-diagonal Abel formula, including d=0, for the original smooth
compact even time function. There is no assumed transform identity. -/
theorem abelProfile_evenCoshLift_cosh (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (d : ℝ) (hd : 0≤d) :
    abelProfile (evenCoshLift f) (Real.cosh d)=
      -(Real.sqrt 2/(2*Real.pi):ℂ)*
        ∫ u in Ioi d,deriv f u/(Real.sqrt (Real.cosh u-Real.cosh d):ℂ) := by
  rw [abelProfile,abelIntegral_cosh_time_general _ d hd]
  have h : (∫ u in Ioi d,(Real.sinh u/(2*abelRadiusTimeCoordinate d u):ℝ) •
      deriv (evenCoshLift f) (Real.cosh u))=
      (1/2:ℂ)*∫ u in Ioi d,deriv f u/(abelRadiusTimeCoordinate d u:ℂ) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact abelRadiusTimeCoordinate_lift_deriv f hf he hc d u hd hu
  rw [h]
  dsimp only [abelRadiusTimeCoordinate]
  ring

/-- Absolute integrability of the physical quadratic Abel derivative follows
from one-sided smoothness and an upper support bound. -/
theorem physical_quadratic_derivative_integrable (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) (q : ℝ) (hq : 1≤q) :
    IntegrableOn (fun s : ℝ => deriv F (q+s^2)) (Ioi (0:ℝ)) := by
  obtain ⟨C,hC0,hC⟩ := physical_derivative_bound F hF B hs
  have hd : Function.support (deriv F)⊆Iic B :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Iic)
  let bound : ℝ → ℝ := (Icc 0 (B+1)).indicator (fun _ => C)
  have hi : Integrable bound := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hm : Measurable (fun s : ℝ => deriv F (q+s^2)) :=
    (measurable_deriv F).comp (by fun_prop)
  apply hi.integrableOn.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0
  by_cases hsB : s∈Icc (0:ℝ) (B+1)
  · simp only [bound,indicator_of_mem hsB]
    exact hC _ (by nlinarith [sq_pos_of_pos hs0])
  · have hlarge : B+1<s := by
      by_contra hn
      exact hsB ⟨hs0.le,le_of_not_gt hn⟩
    have hz : deriv F (q+s^2)=0 := by
      by_contra hn
      have hh : q+s^2≤B := hd hn
      nlinarith [sq_nonneg (s-1)]
    simp only [bound,indicator_of_notMem hsB,hz,norm_zero,le_refl]

/-- The singular time integral in the off-diagonal formula is absolutely
integrable for every d>=0, without any additional vanishing assumption at d. -/
theorem evenTime_offDiagonal_integrable (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (d : ℝ) (hd : 0≤d) :
    IntegrableOn (fun u => deriv f u/(Real.sqrt (Real.cosh u-Real.cosh d):ℂ))
      (Ioi d) := by
  obtain ⟨R,hR,hRs⟩ := hc.isCompact.isBounded.subset_closedBall_lt 0 (0:ℝ)
  have hsup : Function.support f⊆Icc (-R) R := by
    intro u hu
    have hh := hRs (subset_tsupport f hu)
    have hab : |u|≤R := by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hh
    exact abs_le.mp hab
  have hi := physical_quadratic_derivative_integrable (evenCoshLift f)
    (evenCoshLift_smoothOn f hf he hc) (Real.cosh R) (Real.one_le_cosh R)
    (evenCoshLift_support_of_time_support f R hR.le hsup) (Real.cosh d) (Real.one_le_cosh d)
  have hh := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun u hu => (abelRadiusTimeCoordinate_hasDerivAt d u hd hu).hasDerivWithinAt)
    (abelRadiusTimeCoordinate_injOn d hd)
    (fun s : ℝ => deriv (evenCoshLift f) (Real.cosh d+s^2))
  rw [abelRadiusTimeCoordinate_image d hd] at hh
  have hj := (hh.mp hi).const_mul (2:ℂ)
  apply hj.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [abelRadiusTimeCoordinate_sq d u hd hu,abs_of_pos
    (div_pos (Real.sinh_pos_iff.mpr (lt_of_le_of_lt hd hu))
      (mul_pos (by norm_num) (abelRadiusTimeCoordinate_pos d u hd hu))),
    abelRadiusTimeCoordinate_lift_deriv f hf he hc d u hd hu]
  dsimp only [abelRadiusTimeCoordinate]
  ring

#print axioms cosh_sub_pos_of_nonneg_lt
#print axioms abelRadiusTimeCoordinate_pos
#print axioms abelRadiusTimeCoordinate_sq
#print axioms abelRadiusTimeCoordinate_hasDerivAt
#print axioms abelRadiusTimeCoordinate_image
#print axioms abelRadiusTimeCoordinate_injOn
#print axioms abelIntegral_cosh_time_general
#print axioms abelRadiusTimeCoordinate_lift_deriv
#print axioms abelProfile_evenCoshLift_cosh
#print axioms physical_quadratic_derivative_integrable
#print axioms evenTime_offDiagonal_integrable

end QuantitativeMaass
