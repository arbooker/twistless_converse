module

public import QuantitativeMaassPhysicalAbelDerivativeV1
public import QuantitativeMaassAbelOffDiagonalTimeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The second physical derivative of the cosh lift, expressed entirely in
the original time function. -/
theorem evenCoshLift_second_deriv_cosh (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (u : ℝ) (hu : 0<u) :
    deriv (deriv (evenCoshLift f)) (Real.cosh u)=
      deriv (deriv f) u/(Real.sinh u:ℂ)^2-
        deriv f u*(Real.cosh u:ℂ)/(Real.sinh u:ℂ)^3 := by
  have hq : 1<Real.cosh u := Real.one_lt_cosh.mpr hu.ne'
  have hF := evenCoshLift_smoothOn f hf he hc
  have hFc : ContDiffAt ℝ ∞ (evenCoshLift f) (Real.cosh u) :=
    (hF _ hq.le).contDiffAt (Ici_mem_nhds hq)
  have hFdc : ContDiffAt ℝ 1 (deriv (evenCoshLift f)) (Real.cosh u) :=
    hFc.derivWithin (by simp)
  have hl := (hFdc.differentiableAt (by norm_num)).hasDerivAt.scomp u (Real.hasDerivAt_cosh u)
  have hfd := ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)).differentiableAt.hasDerivAt (x:=u)
  have hn : (Real.sinh u:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hu).ne'
  have hr := hfd.div (Real.hasDerivAt_sinh u).ofReal_comp hn
  have heq : (fun x => deriv (evenCoshLift f) (Real.cosh x))=ᶠ[𝓝 u]
      (fun x => deriv f x/(Real.sinh x:ℂ)) := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    exact evenCoshLift_deriv_cosh f hf he hc x hx
  simp only [Function.comp_def] at hl
  change HasDerivAt (fun x => deriv f x/(Real.sinh x:ℂ)) _ u at hr
  have hh := heq.deriv_eq
  rw [hl.deriv,hr.deriv,Complex.real_smul] at hh
  apply (mul_left_cancel₀ hn)
  rw [hh]
  field_simp

/-- Exact interior radial derivative of the original even-time Abel profile. -/
theorem abelProfile_evenCoshLift_radial_deriv (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (d : ℝ) (hd : 0<d) :
    deriv (fun r => abelProfile (evenCoshLift f) (Real.cosh r)) d=
      -(Real.sqrt 2/(2*Real.pi):ℂ)*(Real.sinh d:ℂ)*
        ∫ u in Ioi d,
          (deriv (deriv f) u/(Real.sinh u:ℂ)-
            deriv f u*(Real.cosh u:ℂ)/(Real.sinh u:ℂ)^2)/
            (Real.sqrt (Real.cosh u-Real.cosh d):ℂ) := by
  obtain ⟨L,hL,hsL⟩ := hc.isCompact.isBounded.subset_closedBall_lt 0 (0:ℝ)
  have hs : Function.support f⊆Icc (-L) L := by
    intro u hu
    exact abs_le.mp (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hsL (subset_tsupport f hu))
  have hF := evenCoshLift_smoothOn f hf he hc
  have hFs := evenCoshLift_support_of_time_support f L hL.le hs
  have hh := (abelProfile_hasDerivAt_physical (evenCoshLift f) hF (Real.cosh L)
    (Real.one_le_cosh L) hFs (Real.cosh d) (Real.one_lt_cosh.mpr hd.ne')).scomp d (Real.hasDerivAt_cosh d)
  simp only [Function.comp_def] at hh
  rw [hh.deriv,Complex.real_smul,abelProfile,abelIntegral_cosh_time_general _ d hd.le]
  have heq : (∫ u in Ioi d,(Real.sinh u/(2*abelRadiusTimeCoordinate d u):ℝ) •
      deriv (deriv (evenCoshLift f)) (Real.cosh u))=
      (1/2:ℂ)*∫ u in Ioi d,
        (deriv (deriv f) u/(Real.sinh u:ℂ)-deriv f u*(Real.cosh u:ℂ)/(Real.sinh u:ℂ)^2)/
          (Real.sqrt (Real.cosh u-Real.cosh d):ℂ) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hp := hd.trans hu
    dsimp only
    rw [evenCoshLift_second_deriv_cosh f hf he hc u hp,Complex.real_smul]
    dsimp only [abelRadiusTimeCoordinate]
    have hn : (Real.sinh u:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hp).ne'
    have hr : (Real.sqrt (Real.cosh u-Real.cosh d):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (abelRadiusTimeCoordinate_pos d u hd.le hu).ne'
    simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
    field_simp
  rw [heq]
  ring

#print axioms evenCoshLift_second_deriv_cosh
#print axioms abelProfile_evenCoshLift_radial_deriv

end QuantitativeMaass
