module

public import QuantitativeMaassGreenIntervalV1

set_option autoImplicit false
set_option maxHeartbeats 200000
@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Lebesgue measure on a finite period/height rectangle. The hyperbolic
measure is represented below by its explicit density y⁻². -/
def cylinderRectangle (w a b : ℝ) : Measure Point :=
  (volume.restrict (Ioc 0 w)).prod (volume.restrict (Ioc a b))

theorem continuous_cylinderRectangle_integrable (w a b : ℝ) {F : Point → ℂ}
    (hF : ContinuousOn F (Icc 0 w ×ˢ Icc a b)) :
    Integrable F (cylinderRectangle w a b) := by
  unfold cylinderRectangle
  rw [Measure.prod_restrict]
  exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- Exact Green identity in a genuine cusp cylinder. Periodicity cancels
horizontal boundary terms; the test function vanishes at both height
boundaries. Derivatives, integrability and Fubini are proved from smoothness. -/
theorem green_cylinder (w a b : ℝ) (hw : 0<w) (ha : 0<a) (hab : a≤b)
    {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hpu : ∀ y, 0<y → Function.Periodic (fun x => u (x,y)) w)
    (hpv : ∀ y, 0<y → Function.Periodic (fun x => v (x,y)) w)
    (hua : ∀ x, u (x,a)=0) (hub : ∀ x, u (x,b)=0) :
    (∫ Z, star (u Z)*hyperbolic v Z/(Z.2:ℂ)^2 ∂cylinderRectangle w a b)=
      ∫ Z, star (X u Z)*X v Z+star (Y u Z)*Y v Z ∂cylinderRectangle w a b := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have huX := dir_contDiffOn hu hs e₁
  have huY := dir_contDiffOn hu hs e₂
  have hvX := dir_contDiffOn hv hs e₁
  have hvY := dir_contDiffOn hv hs e₂
  have hvXX := dir_contDiffOn hvX hs e₁
  have hvYY := dir_contDiffOn hvY hs e₂
  have hc (F : Point → ℂ) (hF : ContDiffOn ℝ ∞ F {Z | 0<Z.2}) :
      ContinuousOn F (Icc 0 w ×ˢ Icc a b) :=
    hF.continuousOn.mono (fun _ hZ => lt_of_lt_of_le ha hZ.2.1)
  have hFX : Integrable (fun Z => star (u Z)*(-X (X v) Z)) (cylinderRectangle w a b) :=
    continuous_cylinderRectangle_integrable w a b
    ((hc u hu).star.mul (hc _ hvXX).neg)
  have hFY : Integrable (fun Z => star (u Z)*(-Y (Y v) Z)) (cylinderRectangle w a b) :=
    continuous_cylinderRectangle_integrable w a b
    ((hc u hu).star.mul (hc _ hvYY).neg)
  have hEX : Integrable (fun Z => star (X u Z)*X v Z) (cylinderRectangle w a b) :=
    continuous_cylinderRectangle_integrable w a b
    ((hc _ huX).star.mul (hc _ hvX))
  have hEY : Integrable (fun Z => star (Y u Z)*Y v Z) (cylinderRectangle w a b) :=
    continuous_cylinderRectangle_integrable w a b
    ((hc _ huY).star.mul (hc _ hvY))
  have hhor (y : ℝ) (hy : 0<y) :
      (∫ x in 0..w, star (u (x,y))*(-X (X v) (x,y)))=
        ∫ x in 0..w, star (X u (x,y))*X v (x,y) := by
    have hcont (F : Point → ℂ) (hF : ContDiffOn ℝ ∞ F {Z | 0<Z.2}) :
        Continuous (fun x => F (x,y)) := hF.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => hy)
    have hh := green_interval (fun x => u (x,y)) (fun x => X u (x,y))
      (fun x => X v (x,y)) (fun x => X (X v) (x,y)) 0 w
      (fun x _ => horizontal_hasDerivAt hu hs (x := x) hy)
      (fun x _ => horizontal_hasDerivAt hvX hs (x := x) hy)
      (hcont _ huX).continuousOn (hcont _ hvXX).continuousOn
    have hpX : Function.Periodic (fun x => X v (x,y)) w := by
      have he : (fun x => X v (x,y))=deriv (fun x => v (x,y)) :=
        funext fun x => X_eq_deriv hv hs hy
      rw [he]
      exact periodic_deriv _ _ (hpv y hy)
    have hu0 := hpu y hy 0
    have hv0 := hpX 0
    simp only [zero_add] at hu0 hv0
    simpa only [hu0,hv0,sub_self,sub_zero] using hh
  have hvert (x : ℝ) :
      (∫ y in a..b, star (u (x,y))*(-Y (Y v) (x,y)))=
        ∫ y in a..b, star (Y u (x,y))*Y v (x,y) := by
    have hpos (y : ℝ) (hy : y∈uIcc a b) : 0<y :=
      lt_of_lt_of_le ha ((uIcc_of_le hab ▸ hy).1)
    have hcont (F : Point → ℂ) (hF : ContDiffOn ℝ ∞ F {Z | 0<Z.2}) :
        ContinuousOn (fun y => F (x,y)) (uIcc a b) :=
      hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun y hy => hpos y hy)
    have hh := green_interval (fun y => u (x,y)) (fun y => Y u (x,y))
      (fun y => Y v (x,y)) (fun y => Y (Y v) (x,y)) a b
      (fun y hy => smooth_vertical_hasDerivAt hu x y (hpos y hy))
      (fun y hy => smooth_vertical_hasDerivAt hvY x y (hpos y hy))
      (hcont _ huY) (hcont _ hvYY)
    simpa only [hua,hub,star_zero,zero_mul,sub_self,sub_zero] using hh
  have hxi : (∫ Z, star (u Z)*(-X (X v) Z) ∂cylinderRectangle w a b)=
      ∫ Z, star (X u Z)*X v Z ∂cylinderRectangle w a b := by
    unfold cylinderRectangle at hFX hEX ⊢
    rw [integral_prod_symm _ hFX,integral_prod_symm _ hEX]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    simpa only [intervalIntegral.integral_of_le hw.le] using hhor y (lt_trans ha hy.1)
  have hyi : (∫ Z, star (u Z)*(-Y (Y v) Z) ∂cylinderRectangle w a b)=
      ∫ Z, star (Y u Z)*Y v Z ∂cylinderRectangle w a b := by
    unfold cylinderRectangle at hFY hEY ⊢
    rw [integral_prod _ hFY,integral_prod _ hEY]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simpa only [intervalIntegral.integral_of_le hab] using hvert x
  have hae : ∀ᵐ Z ∂cylinderRectangle w a b, 0<Z.2 := by
    unfold cylinderRectangle
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with Z hZ
    exact lt_trans ha hZ.2.1
  calc
    _ = ∫ Z, star (u Z)*(-X (X v) Z)+star (u Z)*(-Y (Y v) Z)
        ∂cylinderRectangle w a b := by
      apply integral_congr_ae
      filter_upwards [hae] with Z hZ
      rw [XX_eq_deriv hv hs hZ,YY_eq_deriv hv hs hZ]
      unfold hyperbolic euclidean
      simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_pow]
      have hzC : (Z.2:ℂ)≠0 := by exact_mod_cast hZ.ne'
      field_simp
      ring
    _ = _ := by rw [integral_add hFX hFY,hxi,hyi,integral_add hEX hEY]

#print axioms green_cylinder

end QuantitativeMaass
