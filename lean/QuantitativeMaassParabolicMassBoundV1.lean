module

public import QuantitativeMaassParabolicLineCompactV1
public import QuantitativeMaassSublevelIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- The off-diagonal hyperbolic bound has an integrable horizontal
singularity of order one half. -/
theorem parabolicLineProfile_inverse_sqrt_bound (g : ℝ→ℂ) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d))
    (u : ℝ) (hu : u≠0) : ‖parabolicLineProfile g 1 u‖≤C/Real.sqrt |u| := by
  have hq : 1<1+u^2/2 := by nlinarith [sq_pos_of_ne_zero hu]
  have hroot : |u|≤Real.sqrt ((1+u^2/2)^2-1) := by
    apply (Real.le_sqrt (abs_nonneg u) (by nlinarith [sq_nonneg u])).mpr
    nlinarith [sq_abs u,sq_nonneg (u^2)]
  have hh := hb (Real.arcosh (1+u^2/2)) (Real.arcosh_pos hq)
  rw [Real.cosh_arcosh hq.le,Real.sinh_arcosh hq.le] at hh
  have he : parabolicLineProfile g 1 u=g (1+u^2/2) := by simp only [parabolicLineProfile,one_pow,mul_one]
  rw [he]
  exact hh.trans (div_le_div_of_nonneg_left hC
    (Real.sqrt_pos.mpr (abs_pos.mpr hu)) (Real.sqrt_le_sqrt hroot))

/-- Explicit absolute horizontal mass bound; the constant depends only
on propagation and the off-diagonal amplitude. -/
theorem parabolicLineProfile_mass_bound (g : ℝ→ℂ) (B C : ℝ) (hC : 0≤C)
    (hs : Function.support g⊆Iic B)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    ‖∫ u,parabolicLineProfile g 1 u‖≤C*(Real.pi*(2*(2*(|B|+1)+1)+2)) := by
  let D := 2*(|B|+1)+1
  have hD : 0≤D := by dsimp only [D];positivity
  have hsupport : Function.support (parabolicLineProfile g 1)⊆Icc (-D) D := by
    intro u hu
    have hh : 1+u^2/2≤B := by simpa only [parabolicLineProfile,one_pow,mul_one,mem_Iic] using hs hu
    have hsq : u^2≤2*(|B|+1) := by nlinarith [le_abs_self B]
    have hab : |u|≤D := by
      dsimp only [D]
      nlinarith [sq_abs u,sq_nonneg (|u|-1),abs_nonneg B,abs_nonneg u]
    exact abs_le.mp hab
  have hsub (r : ℝ) (_hr : 0<r) :
      (volume.restrict (Icc (-D) D)) {x : ℝ | |x|<r}≤ENNReal.ofReal (2*r) := by
    apply (Measure.restrict_apply_le _ _).trans
    have he : {x : ℝ | |x|<r}=Ioo (-r) r := by
      ext x
      simpa only [mem_ofPred_eq,mem_Ioo] using (abs_lt (a:=x) (b:=r))
    rw [he,Real.volume_Ioo]
    simp only [sub_neg_eq_add,←two_mul,le_refl]
  obtain ⟨hi,hib⟩ := inverse_sqrt_integrable_of_sublevel
    (volume.restrict (Icc (-D) D)) (fun x : ℝ => |x|) continuous_abs.measurable abs_nonneg
    (2*D) 2 (by positivity) (by norm_num) (by
      rw [Measure.restrict_apply_univ,Real.volume_Icc]
      simp only [sub_neg_eq_add,two_mul,le_refl]) hsub
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Icc (-D) D)
    (fun x hx => by by_contra hn; exact hx (hsupport hn))]
  calc
    _≤∫ u in Icc (-D) D,C*(1/Real.sqrt |u|) := by
      apply norm_integral_le_of_norm_le (hi.const_mul C)
      have hz : ∀ᵐ u : ℝ ∂volume,u≠0 := by simp [ae_iff]
      filter_upwards [ae_restrict_of_ae hz] with u hu
      simpa only [mul_one_div] using parabolicLineProfile_inverse_sqrt_bound g C hC hb u hu
    _=C*(∫ u in Icc (-D) D,1/Real.sqrt |u|) := integral_const_mul _ _
    _≤_ := mul_le_mul_of_nonneg_left hib hC

#print axioms parabolicLineProfile_inverse_sqrt_bound
#print axioms parabolicLineProfile_mass_bound

end QuantitativeMaass
