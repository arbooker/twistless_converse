module

public import QuantitativeArithmeticSmallLevelTwentyTwoDefectV1
public import SmallLevelAnalyticRigidityTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix ModularGroup Complex Filter Set UpperHalfPlane
open scoped MatrixGroups Topology ModularForm Manifold

namespace Zsquare

def elliptic : SL(2,ℚ) := ⟨!![-91/25,-76/75;66/5,17/5],by norm_num [det_fin_two]⟩
def fixedPoint : ℂ := ⟨-4/15,Real.sqrt 154/165⟩

theorem fixedPoint_positive : 0<fixedPoint.im := by
  change 0<Real.sqrt 154/165
  positivity

theorem fixedPoint_denom : (66/5:ℂ)*fixedPoint+(17/5)≠0 := by
  intro h
  have hh:=congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : ((-91/25)*fixedPoint+(-76/75))/((66/5)*fixedPoint+(17/5))=fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 154)^2=154 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint,Complex.mul_re,Complex.mul_im] <;> nlinarith

theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F (((-91/25)*z+(-76/75))/((66/5)*z+(17/5)))=((66/5)*z+(17/5))^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (-6/25:ℚ)≠m := by
    intro hm
    have hh : (25:ℚ)*m=-6 := by rw [← hm]; norm_num
    have hi : (25:ℤ)*m=-6 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F (((-91/25)*z+(-76/75))/((66/5)*z+(17/5)))=((66/5)*z+(17/5))^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    exact he z hz
  have hh:=SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=-91/25) (b:=-76/75) (c:=66/5) (d:=17/5) (t:=(-6/25:ℚ))
    (by norm_num) fixedPoint_denom fixedPoint_fixed hk (by norm_num) hnon heq
  exact fun z hz => hh hz

def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem ellipticReal_det : (GeneralLinearGroup.det ellipticReal:ℝ)=1 := by simp [ellipticReal]
theorem ellipticReal_denom (z : ℍ) : denom ellipticReal z=(66/5)*(z:ℂ)+(17/5) := by
  norm_num [denom,ellipticReal,elliptic,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
theorem ellipticReal_point (z : ℍ) :
    ((ellipticReal • z:ℍ):ℂ)=((-91/25)*(z:ℂ)+(-76/75))/((66/5)*(z:ℂ)+(17/5)) := by
  rw [coe_smul_of_det_pos (by rw [ellipticReal_det]; norm_num)]
  norm_num [num,denom,ellipticReal,elliptic,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]

theorem invariant_zero {k : ℕ} (hk : 0<k) (H : ℍ → ℂ)
    (hhol : MDiff H) (he : H ∣[(k:ℤ)] ellipticReal=H) : H=0 := by
  let F : ℂ → ℂ := H ∘ ofComplex
  have hr (w : ℍ) : H w=F (w:ℂ) := by simp [F]
  have ha : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hhol).analyticOnNhd isOpen_upperHalfPlaneSet
  have htrans (z : ℂ) (hz : 0<z.im) :
      F (((-91/25)*z+(-76/75))/((66/5)*z+(17/5)))=((66/5)*z+(17/5))^k*F z := by
    let w : ℍ := ⟨z,hz⟩
    have hh:=congrFun he w
    rw [ModularForm.slash_apply] at hh
    have hs : σ ellipticReal=ContinuousAlgEquiv.refl ℝ ℂ := by
      simp only [σ,ellipticReal_det]; norm_num
    rw [hs,ellipticReal_det,ellipticReal_denom] at hh
    norm_num only [ContinuousAlgEquiv.refl_apply,abs_one,Complex.ofReal_one,
      one_zpow,mul_one,zpow_neg,zpow_natCast] at hh
    rw [hr,hr,ellipticReal_point] at hh
    change F (((-91/25)*z+(-76/75))/((66/5)*z+(17/5)))*(((66/5)*z+(17/5))^k)⁻¹=F z at hh
    have hd : ((66/5)*z+(17/5):ℂ)≠0 := by
      simpa only [ellipticReal_denom] using denom_ne_zero ellipticReal w
    have hx:=congrArg (fun v : ℂ => v*((66/5)*z+(17/5))^k) hh
    simp only [mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hd),mul_one] at hx
    simpa only [mul_comm] using hx
  funext z
  rw [hr]
  exact elliptic_defect_zero ha hk htrans z z.im_pos

#print axioms invariant_zero
end Zsquare

namespace Vsquare

def elliptic : SL(2,ℚ) := ⟨!![1/9,1/3;-11/3,-2],by norm_num [det_fin_two]⟩
def fixedPoint : ℂ := ⟨-19/66,Real.sqrt 35/66⟩

theorem fixedPoint_positive : 0<fixedPoint.im := by
  change 0<Real.sqrt 35/66
  positivity

theorem fixedPoint_denom : (-11/3:ℂ)*fixedPoint+(-2)≠0 := by
  intro h
  have hh:=congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : ((1/9)*fixedPoint+(1/3))/((-11/3)*fixedPoint+(-2))=fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint,Complex.mul_re,Complex.mul_im] <;> nlinarith

theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F (((1/9)*z+(1/3))/((-11/3)*z+(-2)))=((-11/3)*z+(-2))^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (-17/9:ℚ)≠m := by
    intro hm
    have hh : (9:ℚ)*m=-17 := by rw [← hm]; norm_num
    have hi : (9:ℤ)*m=-17 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F (((1/9)*z+(1/3))/((-11/3)*z+(-2)))=((-11/3)*z+(-2))^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    exact he z hz
  have hh:=SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=1/9) (b:=1/3) (c:=-11/3) (d:=-2) (t:=(-17/9:ℚ))
    (by norm_num) fixedPoint_denom fixedPoint_fixed hk (by norm_num) hnon heq
  exact fun z hz => hh hz

def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem ellipticReal_det : (GeneralLinearGroup.det ellipticReal:ℝ)=1 := by simp [ellipticReal]
theorem ellipticReal_denom (z : ℍ) : denom ellipticReal z=(-11/3)*(z:ℂ)+(-2) := by
  norm_num [denom,ellipticReal,elliptic,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
theorem ellipticReal_point (z : ℍ) :
    ((ellipticReal • z:ℍ):ℂ)=((1/9)*(z:ℂ)+(1/3))/((-11/3)*(z:ℂ)+(-2)) := by
  rw [coe_smul_of_det_pos (by rw [ellipticReal_det]; norm_num)]
  norm_num [num,denom,ellipticReal,elliptic,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]

theorem invariant_zero {k : ℕ} (hk : 0<k) (H : ℍ → ℂ)
    (hhol : MDiff H) (he : H ∣[(k:ℤ)] ellipticReal=H) : H=0 := by
  let F : ℂ → ℂ := H ∘ ofComplex
  have hr (w : ℍ) : H w=F (w:ℂ) := by simp [F]
  have ha : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hhol).analyticOnNhd isOpen_upperHalfPlaneSet
  have htrans (z : ℂ) (hz : 0<z.im) :
      F (((1/9)*z+(1/3))/((-11/3)*z+(-2)))=((-11/3)*z+(-2))^k*F z := by
    let w : ℍ := ⟨z,hz⟩
    have hh:=congrFun he w
    rw [ModularForm.slash_apply] at hh
    have hs : σ ellipticReal=ContinuousAlgEquiv.refl ℝ ℂ := by
      simp only [σ,ellipticReal_det]; norm_num
    rw [hs,ellipticReal_det,ellipticReal_denom] at hh
    norm_num only [ContinuousAlgEquiv.refl_apply,abs_one,Complex.ofReal_one,
      one_zpow,mul_one,zpow_neg,zpow_natCast] at hh
    rw [hr,hr,ellipticReal_point] at hh
    simp only [← neg_div] at hh
    change F (((1/9)*z+(1/3))/((-11/3)*z+(-2)))*(((-11/3)*z+(-2))^k)⁻¹=F z at hh
    have hd : ((-11/3)*z+(-2):ℂ)≠0 := by
      simpa only [ellipticReal_denom] using denom_ne_zero ellipticReal w
    have hx:=congrArg (fun v : ℂ => v*((-11/3)*z+(-2))^k) hh
    simp only [mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hd),mul_one] at hx
    simpa only [mul_comm] using hx
  funext z
  rw [hr]
  exact elliptic_defect_zero ha hk htrans z z.im_pos

#print axioms invariant_zero
end Vsquare
end QuantitativeArithmeticSmallLevelTwentyTwo
