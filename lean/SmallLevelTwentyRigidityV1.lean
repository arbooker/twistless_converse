module

public import SmallLevelTwentyDefectV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelTwenty

open Matrix UpperHalfPlane ModularGroup
open scoped MatrixGroups ModularForm Manifold

theorem ellipticReal_det : (GeneralLinearGroup.det ellipticReal : ℝ)=1 := by
  simp [ellipticReal]

theorem ellipticReal_denom (z : ℍ) : denom ellipticReal z= -5*(z:ℂ)-1/3 := by
  norm_num [denom, ellipticReal, elliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]
  ring

theorem ellipticReal_point (z : ℍ) :
    ((ellipticReal • z : ℍ):ℂ)=(2*(z:ℂ)+1/3)/(-5*(z:ℂ)-1/3) := by
  rw [coe_smul_of_det_pos (by rw [ellipticReal_det]; norm_num)]
  norm_num [num, denom, ellipticReal, elliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]
  ring

theorem invariant_zero {k : ℕ} (hk : 0<k) (H : ℍ → ℂ)
    (hhol : MDiff H) (he : H ∣[(k:ℤ)] ellipticReal=H) : H=0 := by
  let F : ℂ → ℂ := H ∘ ofComplex
  have hr (w : ℍ) : H w=F (w:ℂ) := by simp [F]
  have ha : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hhol).analyticOnNhd isOpen_upperHalfPlaneSet
  have htrans (z : ℂ) (hz : 0<z.im) :
      F ((2*z+1/3)/(-5*z-1/3))=(-5*z-1/3)^k*F z := by
    let w : ℍ := ⟨z,hz⟩
    have hh := congrFun he w
    rw [ModularForm.slash_apply] at hh
    have hs : σ ellipticReal=ContinuousAlgEquiv.refl ℝ ℂ := by
      simp only [σ, ellipticReal_det]; norm_num
    rw [hs, ellipticReal_det, ellipticReal_denom] at hh
    norm_num only [ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one,
      one_zpow, mul_one, zpow_neg, zpow_natCast] at hh
    rw [hr, hr, ellipticReal_point] at hh
    change F ((2*z+1/3)/(-5*z-1/3))*((-5*z-1/3)^k)⁻¹=F z at hh
    have hd : (-5*z-1/3:ℂ)≠0 := by
      simpa only [ellipticReal_denom] using denom_ne_zero ellipticReal w
    have hx := congrArg (fun v : ℂ => v*(-5*z-1/3)^k) hh
    simp only [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hd), mul_one] at hx
    simpa only [mul_comm] using hx
  funext z
  rw [hr]
  exact elliptic_defect_zero ha hk htrans z z.im_pos

theorem scaled_holomorphic {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 20 k f) :
    MDiff (SmallLevelEvenScale.scaledFunction k f) := by
  obtain ⟨τ, _, hg⟩ := hf.growth
  intro z
  have hd : DifferentiableAt ℂ (SmallLevelEvenScale.scaledFourier k f) (z:ℂ) :=
    (FinitenessFourierConstruction.holomorphic
      (FinitenessOriginalFourier.polynomial_bound hf.zero hg k)
      (z := (z:ℂ)/2) (by simpa using div_pos z.im_pos (by norm_num : (0:ℝ)<2))).comp
      (z:ℂ) (differentiableAt_id.div_const 2)
  exact hd.mdifferentiableAt.comp z (mdifferentiable_coe z)

theorem original_A (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 20 (2*m) f) :
    SmallLevelEvenScale.scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A=
      SmallLevelEvenScale.scaledFunction (2*m) f := by
  have hhol := scaled_holomorphic hf
  have hd := (hhol.slash ((2*m:ℕ):ℤ) (SpecialLinearGroup.mapGL ℝ A)).sub hhol
  exact sub_eq_zero.mp (invariant_zero (by omega : 0<2*m) _ hd (actual_defect_elliptic m hf))

#print axioms invariant_zero
#print axioms original_A

end SmallLevelTwenty
