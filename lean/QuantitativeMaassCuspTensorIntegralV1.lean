module

public import QuantitativeMaassCuspPeriodicIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Vertical factors preserve the actual horizontal cusp periodicity. -/
theorem vertical_pair_periodic (w : ℝ) (g : ℝ → ℂ) (F : ℍ → ℂ)
    (hp : ∀ y, 0<y → Function.Periodic (fun x => F (cartesianLift (x,y))) w)
    (y : ℝ) (hy : 0<y) :
    Function.Periodic (fun x => star (g (cartesianLift (x,y)).im)*F (cartesianLift (x,y))) w := by
  have him (x : ℝ) : (cartesianLift (x,y)).im=y := by
    rw [cartesianLift_positive _ hy]
    rfl
  intro x
  change star (g (cartesianLift (x+w,y)).im)*F (cartesianLift (x+w,y))=
    star (g (cartesianLift (x,y)).im)*F (cartesianLift (x,y))
  rw [him,him]
  exact congrArg (fun z : ℂ => star (g y)*z) (hp y hy x)

/-- Compact tensor tests extract the exact unnormalized period integral. -/
theorem cuspTensor_periodic_integral (w a b : ℝ) (hw : 0<w) (ha : 0<a)
    (g : ℝ → ℂ) (hg : Continuous g) (F : ℍ → ℂ) (hF : Continuous F)
    (hp : ∀ y, 0<y → Function.Periodic (fun x => F (cartesianLift (x,y))) w) :
    (∫ Z in upperRectangle 0 (2*w) a b,
      star (upperFunction (cuspTensor (cuspHorizontal w) g) Z)*F Z)=
      ∫ Z in upperRectangle 0 w a b, star (g Z.im)*F Z := by
  have h := rectangle_periodCutoff_integral w a b hw ha
    (fun Z => star (g Z.im)*F Z) (((hg.comp continuous_im).star).mul hF)
    (vertical_pair_periodic w g F hp)
  rw [← h]
  apply integral_congr_ae
  filter_upwards with Z
  simp only [upperFunction,cuspTensor,cuspHorizontal,star_mul,Complex.star_def,Complex.conj_ofReal]
  ring

/-- Averaging the actual compact test Laplacian removes the horizontal
second derivative and retains precisely -y² g'' in the vertical test. -/
theorem cuspTensor_laplacian_periodic_integral (w a b : ℝ) (hw : 0<w) (ha : 0<a)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (F : ℍ → ℂ) (hF : Continuous F)
    (hp : ∀ y, 0<y → Function.Periodic (fun x => F (cartesianLift (x,y))) w) :
    (∫ Z in upperRectangle 0 (2*w) a b,
      star (upperLaplacian (cuspTensor (cuspHorizontal w) g) Z)*F Z)=
      ∫ Z in upperRectangle 0 w a b, star (-(Z.im:ℂ)^2*deriv (deriv g) Z.im)*F Z := by
  let q : ℝ → ℂ := fun y => -(y:ℂ)^2/(w:ℂ)^2*g y
  let v : ℝ → ℂ := fun y => -(y:ℂ)^2*deriv (deriv g) y
  have hg' : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hq : Continuous q := (((Complex.continuous_ofReal.pow 2).neg.div_const _).mul hg.continuous)
  have hv : Continuous v := ((Complex.continuous_ofReal.pow 2).neg).mul
    (hg'.continuous_deriv (by simp))
  have hx := rectangle_periodCutoff_second_integral w a b hw ha
    (fun Z => star (q Z.im)*F Z) (((hq.comp continuous_im).star).mul hF)
    (vertical_pair_periodic w q F hp)
  have hy := rectangle_periodCutoff_integral w a b hw ha
    (fun Z => star (v Z.im)*F Z) (((hv.comp continuous_im).star).mul hF)
    (vertical_pair_periodic w v F hp)
  have he : (fun Z : ℍ => star (upperLaplacian (cuspTensor (cuspHorizontal w) g) Z)*F Z)=
      fun Z => (((deriv (deriv periodCutoff) (Z.re/w):ℝ):ℂ)*(star (q Z.im)*F Z))+
        (periodCutoff (Z.re/w):ℂ)*(star (v Z.im)*F Z) := by
    funext Z
    rw [upperLaplacian,cuspTensor_laplacian,cuspHorizontal_second]
    simp only [cuspHorizontal,q,v,Complex.star_def,map_mul,map_add,map_neg,map_pow,
      map_div₀,Complex.conj_ofReal]
    ring
  have hd : ContDiff ℝ ∞ (deriv periodCutoff) := (contDiff_infty_iff_deriv.mp periodCutoff_smooth).2
  have hcx : Continuous (fun Z : ℍ => ((deriv (deriv periodCutoff) (Z.re/w):ℝ):ℂ)*
      (star (q Z.im)*F Z)) := (Complex.continuous_ofReal.comp
        ((hd.continuous_deriv (by simp)).comp (continuous_re.div_const w))).mul
          (((hq.comp continuous_im).star).mul hF)
  have hcy : Continuous (fun Z : ℍ => (periodCutoff (Z.re/w):ℂ)*(star (v Z.im)*F Z)) :=
    (Complex.continuous_ofReal.comp (periodCutoff_smooth.continuous.comp (continuous_re.div_const w))).mul
      (((hv.comp continuous_im).star).mul hF)
  rw [he,integral_add
    (hcx.continuousOn.integrableOn_compact (upperRectangle_compact 0 (2*w) a b ha))
    (hcy.continuousOn.integrableOn_compact (upperRectangle_compact 0 (2*w) a b ha)),hx,zero_add,hy]

#print axioms cuspTensor_periodic_integral
#print axioms cuspTensor_laplacian_periodic_integral

end QuantitativeMaass
