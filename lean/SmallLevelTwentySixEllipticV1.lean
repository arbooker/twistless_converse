module

public import SmallLevelTwentySixFirstHyperbolicV1
public import SmallLevelAnalyticRigidityTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Matrix ModularGroup Complex Filter Set UpperHalfPlane
open scoped MatrixGroups Topology ModularForm Manifold

namespace EllipticSquare

def elliptic : SL(2,ℚ) := ⟨!![-25/18,7/18;-91/9,19/9],by norm_num [det_fin_two]⟩
def fixedPoint : ℂ := ⟨9/52,Real.sqrt 23/52⟩

theorem fixedPoint_positive : 0<fixedPoint.im := by
  change 0<Real.sqrt 23/52
  positivity

theorem fixedPoint_denom : (-91/9:ℂ)*fixedPoint+(19/9)≠0 := by
  intro h
  have hh:=congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : ((-25/18)*fixedPoint+(7/18))/((-91/9)*fixedPoint+(19/9))=fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 23)^2=23 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint,Complex.mul_re,Complex.mul_im] <;> nlinarith

theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F (((-25/18)*z+(7/18))/((-91/9)*z+(19/9)))=((-91/9)*z+(19/9))^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (13/18:ℚ)≠m := by
    intro hm
    have hh : (18:ℚ)*m=13 := by rw [← hm]; norm_num
    have hi : (18:ℤ)*m=13 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F (((-25/18)*z+(7/18))/((-91/9)*z+(19/9)))=((-91/9)*z+(19/9))^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    exact he z hz
  have hh:=SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:=-25/18) (b:=7/18) (c:=-91/9) (d:=19/9) (t:=(13/18:ℚ))
    (by norm_num) fixedPoint_denom fixedPoint_fixed hk (by norm_num) hnon heq
  exact fun z hz => hh hz

def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem ellipticReal_det : (GeneralLinearGroup.det ellipticReal:ℝ)=1 := by simp [ellipticReal]
theorem ellipticReal_denom (z : ℍ) : denom ellipticReal z=(-91/9)*(z:ℂ)+(19/9) := by
  norm_num [denom,ellipticReal,elliptic,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
theorem ellipticReal_point (z : ℍ) :
    ((ellipticReal • z:ℍ):ℂ)=((-25/18)*(z:ℂ)+(7/18))/((-91/9)*(z:ℂ)+(19/9)) := by
  rw [coe_smul_of_det_pos (by rw [ellipticReal_det]; norm_num)]
  norm_num [num,denom,ellipticReal,elliptic,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]

theorem invariant_zero {k : ℕ} (hk : 0<k) (H : ℍ → ℂ)
    (hhol : MDiff H) (he : H ∣[(k:ℤ)] ellipticReal=H) : H=0 := by
  let F : ℂ → ℂ := H ∘ ofComplex
  have hr (w : ℍ) : H w=F (w:ℂ) := by simp [F]
  have ha : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hhol).analyticOnNhd isOpen_upperHalfPlaneSet
  have htrans (z : ℂ) (hz : 0<z.im) :
      F (((-25/18)*z+(7/18))/((-91/9)*z+(19/9)))=((-91/9)*z+(19/9))^k*F z := by
    let w : ℍ := ⟨z,hz⟩
    have hh:=congrFun he w
    rw [ModularForm.slash_apply] at hh
    have hs : σ ellipticReal=ContinuousAlgEquiv.refl ℝ ℂ := by
      simp only [σ,ellipticReal_det]; norm_num
    rw [hs,ellipticReal_det,ellipticReal_denom] at hh
    norm_num only [ContinuousAlgEquiv.refl_apply,abs_one,Complex.ofReal_one,
      one_zpow,mul_one,zpow_neg,zpow_natCast] at hh
    rw [hr,hr,ellipticReal_point] at hh
    have hhe : F (((-25/18)*z+(7/18))/((-91/9)*z+(19/9)))*(((-91/9)*z+(19/9))^k)⁻¹=F z := by
      simpa only [neg_div] using hh
    have hd : ((-91/9)*z+(19/9):ℂ)≠0 := by
      simpa only [ellipticReal_denom,neg_div] using denom_ne_zero ellipticReal w
    have hx:=congrArg (fun v : ℂ => v*((-91/9)*z+(19/9))^k) hhe
    simp only [mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hd),mul_one] at hx
    simpa only [mul_comm] using hx
  funext z
  rw [hr]
  exact elliptic_defect_zero ha hk htrans z z.im_pos

#print axioms invariant_zero
end EllipticSquare


/-- Squaring removes the possible negative sign in the elliptic eigenlaw. -/
theorem elliptic_word_square :
    (hyperM*P)*(hyperM*P)=EllipticSquare.ellipticReal := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperM,P,EllipticSquare.ellipticReal,EllipticSquare.elliptic,
      SmallLevelNormalized.matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

theorem elliptic_word_eigen_zero {k : ℕ} (hk : 0<k) (H : ℍ→ℂ) (hhol : MDiff H)
    (χ : ℂ) (hχ : χ=1 ∨ χ= -1) (he : H ∣[(k:ℤ)] (hyperM*P)=χ • H) : H=0 := by
  have hd : (GeneralLinearGroup.det (hyperM*P):ℝ)=1 := by
    simp only [map_mul,Units.val_mul,P_det]
    rw [show (GeneralLinearGroup.det hyperM:ℝ)=1 from SmallLevelNormalized.matrix_det _ _ _ _ _]
    norm_num
  have hh : H ∣[(k:ℤ)] ((hyperM*P)*(hyperM*P))=H := by
    rw [SlashAction.slash_mul,he,SmallLevelNormalized.det_one_smul _ hd,he,smul_smul]
    rcases hχ with rfl|rfl <;> simp
  rw [elliptic_word_square] at hh
  exact EllipticSquare.invariant_zero hk H hhol hh

#print axioms elliptic_word_eigen_zero
end SmallLevelTwentySix
