module

public import QuantitativeMaassAffineCovarianceV1
public import QuantitativeMaassAllCuspConstantV1
public import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 200000
@[expose] public noncomputable section

open Set Matrix UpperHalfPlane
open scoped ContDiff MatrixGroups

namespace QuantitativeMaass
open MaassDifferential

/-- An explicit Cartesian integral cusp chart. The Bruhat decomposition is
used only to make its actual differential covariance transparent. -/
def integralCuspChart (s : SL(2,ℤ)) : Point → Point :=
  if (s 1 0 : ℝ)=0 then affineChart ((s 0 0 : ℝ)^2) ((s 0 0 : ℝ)*s 0 1)
  else affineChart (((s 1 0 : ℝ)^2)⁻¹) ((s 0 0 : ℝ)/s 1 0) ∘
    (fun Z => F 1 Z.1 Z.2) ∘ affineChart 1 ((s 1 1 : ℝ)/s 1 0)

theorem integralCuspChart_det (s : SL(2,ℤ)) :
    (s 0 0 : ℝ)*(s 1 1 : ℝ)-(s 0 1 : ℝ)*(s 1 0 : ℝ)=1 := by
  have h := s.property
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

theorem integralCuspChart_pos (s : SL(2,ℤ)) (Z : Point) (hZ : 0<Z.2) :
    0<(integralCuspChart s Z).2 := by
  unfold integralCuspChart
  split_ifs with hc
  · have ha : (s 0 0 : ℝ)≠0 := by
      intro ha
      have h := integralCuspChart_det s
      simp [ha,hc] at h
    exact mul_pos (sq_pos_of_ne_zero ha) hZ
  · exact mul_pos (inv_pos.mpr (sq_pos_of_ne_zero hc))
      (F_height_pos (by norm_num) (by simpa [affineChart] using hZ))

theorem integralCuspChart_pullback_smooth (s : SL(2,ℤ)) {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) :
    ContDiffOn ℝ ∞ (u ∘ integralCuspChart s) {Z | 0<Z.2} := by
  unfold integralCuspChart
  split_ifs with hc
  · have ha : (s 0 0 : ℝ)≠0 := by
      intro ha
      have h := integralCuspChart_det s
      simp [ha,hc] at h
    exact affine_pullback_smooth hu (sq_pos_of_ne_zero ha) _
  · exact affine_pullback_smooth
      (pullback_contDiffOn (affine_pullback_smooth hu
        (inv_pos.mpr (sq_pos_of_ne_zero hc)) _) (by norm_num : (0:ℝ)<1))
      (by norm_num : (0:ℝ)<1) _

theorem hyperbolic_integralCuspChart (s : SL(2,ℤ)) {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (x y : ℝ) (hy : 0<y) :
    hyperbolic (u ∘ integralCuspChart s) (x,y)=
      hyperbolic u (integralCuspChart s (x,y)) := by
  unfold integralCuspChart
  split_ifs with hc
  · have ha : (s 0 0 : ℝ)≠0 := by
      intro ha
      have h := integralCuspChart_det s
      simp [ha,hc] at h
    exact hyperbolic_affine hu (sq_pos_of_ne_zero ha) _ x y hy
  · have huA := affine_pullback_smooth hu (inv_pos.mpr (sq_pos_of_ne_zero hc))
      ((s 0 0 : ℝ)/s 1 0)
    have huF := pullback_contDiffOn huA (by norm_num : (0:ℝ)<1)
    change hyperbolic (pullback 1 (u ∘ affineChart (((s 1 0 : ℝ)^2)⁻¹)
        ((s 0 0 : ℝ)/s 1 0)) ∘ affineChart 1 ((s 1 1 : ℝ)/s 1 0)) (x,y)=_
    rw [hyperbolic_affine huF (by norm_num) _ x y hy]
    simp only [affineChart,one_mul,Function.comp_apply]
    change hyperbolic (pullback 1 (u ∘ affineChart (((s 1 0 : ℝ)^2)⁻¹)
        ((s 0 0 : ℝ)/s 1 0))) (x+(s 1 1 : ℝ)/s 1 0,y)=_
    rw [hyperbolic_pullback huA (by norm_num) hy]
    exact hyperbolic_affine hu (inv_pos.mpr (sq_pos_of_ne_zero hc)) _ _ _
      (F_height_pos (by norm_num) hy)

/-- The Cartesian chart is the literal integral matrix action on ℍ. -/
theorem integralCuspChart_action (s : SL(2,ℤ)) (x y : ℝ) (hy : 0<y) :
    integralCuspChart s (x,y) =
      ((SpecialLinearGroup.mapGL ℝ s • horocyclePoint x y hy).re,
       (SpecialLinearGroup.mapGL ℝ s • horocyclePoint x y hy).im) := by
  have hdet := integralCuspChart_det s
  have hg : (SpecialLinearGroup.mapGL ℝ s).det.val=1 := by
    change (((s.val).map (Int.castRingHom ℝ)).det)=1
    simpa [Matrix.det_fin_two] using hdet
  have hcoe := UpperHalfPlane.coe_smul_of_det_pos
    (g := SpecialLinearGroup.mapGL ℝ s) (by rw [hg]; norm_num) (horocyclePoint x y hy)
  have hre := congrArg Complex.re hcoe
  have him := congrArg Complex.im hcoe
  change (SpecialLinearGroup.mapGL ℝ s • horocyclePoint x y hy).re = _ at hre
  change (SpecialLinearGroup.mapGL ℝ s • horocyclePoint x y hy).im = _ at him
  rw [hre,him]
  change integralCuspChart s (x,y) =
    (((((s 0 0:ℝ):ℂ)*(⟨x,y⟩:ℂ)+(s 0 1:ℝ))/
       (((s 1 0:ℝ):ℂ)*(⟨x,y⟩:ℂ)+(s 1 1:ℝ))).re,
     ((((s 0 0:ℝ):ℂ)*(⟨x,y⟩:ℂ)+(s 0 1:ℝ))/
       (((s 1 0:ℝ):ℂ)*(⟨x,y⟩:ℂ)+(s 1 1:ℝ))).im)
  simp only [Complex.div_re,Complex.div_im,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.normSq_apply,zero_mul,sub_zero,add_zero]
  unfold integralCuspChart
  split_ifs with hc
  · have ha : (s 0 0:ℝ)≠0 := by intro ha; simp [ha,hc] at hdet
    have hd : (s 1 1:ℝ)≠0 := by intro hd; simp [hd,hc] at hdet
    simp only [hc,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at hdet ⊢
    apply Prod.ext <;> dsimp [affineChart]
    all_goals field_simp
    · linear_combination ((s 0 0:ℝ)*x+s 0 1)*(s 1 1:ℝ)*hdet
    · linear_combination y*((s 0 0:ℝ)*(s 1 1:ℝ))*hdet
  · have hden : (s 1 0:ℝ)*y ≠ 0 := mul_ne_zero hc hy.ne'
    have hp : ((s 1 0:ℝ)*x+s 1 1)^2+((s 1 0:ℝ)*y)^2 ≠ 0 := by
      positivity
    have hr : (x+(s 1 1:ℝ)/s 1 0)^2+y^2 ≠ 0 := (radius_pos hy).ne'
    apply Prod.ext <;> dsimp [Function.comp_def,affineChart,F]
    all_goals field_simp
    · linear_combination ((s 1 0:ℝ)*x+s 1 1)*hdet
    · nlinarith [hdet]

#print axioms integralCuspChart_action
#print axioms hyperbolic_integralCuspChart

end QuantitativeMaass
