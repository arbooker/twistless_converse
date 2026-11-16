module

public import QuantitativeMaassGreenIntervalV1

set_option autoImplicit false
set_option maxHeartbeats 200000
@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Lebesgue measure on a finite Cartesian rectangle. -/
def greenRectangle (l r a b : ℝ) : Measure Point :=
  (volume.restrict (Ioc l r)).prod (volume.restrict (Ioc a b))

theorem continuous_greenRectangle_integrable (l r a b : ℝ) {F : Point → ℂ}
    (hF : ContinuousOn F (Icc l r ×ˢ Icc a b)) :
    Integrable F (greenRectangle l r a b) := by
  unfold greenRectangle
  rw [Measure.prod_restrict]
  exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- Exact Green identity with vanishing boundary products on all four sides.
Neither function needs to be periodic or compactly supported. All
derivatives, integrability and Fubini are proved from smoothness. -/
theorem green_rectangle_boundary (l r a b : ℝ) (hlr : l≤r) (ha : 0<a) (hab : a≤b)
    {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hul : ∀ y, star (u (l,y))*X v (l,y)=0)
    (hur : ∀ y, star (u (r,y))*X v (r,y)=0)
    (hua : ∀ x, star (u (x,a))*Y v (x,a)=0)
    (hub : ∀ x, star (u (x,b))*Y v (x,b)=0) :
    (∫ Z, star (u Z)*hyperbolic v Z/(Z.2:ℂ)^2 ∂greenRectangle l r a b)=
      ∫ Z, star (X u Z)*X v Z+star (Y u Z)*Y v Z ∂greenRectangle l r a b := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have huX := dir_contDiffOn hu hs e₁
  have huY := dir_contDiffOn hu hs e₂
  have hvX := dir_contDiffOn hv hs e₁
  have hvY := dir_contDiffOn hv hs e₂
  have hvXX := dir_contDiffOn hvX hs e₁
  have hvYY := dir_contDiffOn hvY hs e₂
  have hc (F : Point → ℂ) (hF : ContDiffOn ℝ ∞ F {Z | 0<Z.2}) :
      ContinuousOn F (Icc l r ×ˢ Icc a b) :=
    hF.continuousOn.mono (fun _ hZ => lt_of_lt_of_le ha hZ.2.1)
  have hFX : Integrable (fun Z => star (u Z)*(-X (X v) Z)) (greenRectangle l r a b) :=
    continuous_greenRectangle_integrable l r a b
    ((hc u hu).star.mul (hc _ hvXX).neg)
  have hFY : Integrable (fun Z => star (u Z)*(-Y (Y v) Z)) (greenRectangle l r a b) :=
    continuous_greenRectangle_integrable l r a b
    ((hc u hu).star.mul (hc _ hvYY).neg)
  have hEX : Integrable (fun Z => star (X u Z)*X v Z) (greenRectangle l r a b) :=
    continuous_greenRectangle_integrable l r a b
    ((hc _ huX).star.mul (hc _ hvX))
  have hEY : Integrable (fun Z => star (Y u Z)*Y v Z) (greenRectangle l r a b) :=
    continuous_greenRectangle_integrable l r a b
    ((hc _ huY).star.mul (hc _ hvY))
  have hhor (y : ℝ) (hy : 0<y) :
      (∫ x in l..r, star (u (x,y))*(-X (X v) (x,y)))=
        ∫ x in l..r, star (X u (x,y))*X v (x,y) := by
    have hcont (F : Point → ℂ) (hF : ContDiffOn ℝ ∞ F {Z | 0<Z.2}) :
        Continuous (fun x => F (x,y)) := hF.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => hy)
    have hh := green_interval (fun x => u (x,y)) (fun x => X u (x,y))
      (fun x => X v (x,y)) (fun x => X (X v) (x,y)) l r
      (fun x _ => horizontal_hasDerivAt hu hs (x := x) hy)
      (fun x _ => horizontal_hasDerivAt hvX hs (x := x) hy)
      (hcont _ huX).continuousOn (hcont _ hvXX).continuousOn
    simpa only [hul,hur,sub_self,sub_zero] using hh
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
    simpa only [hua,hub,sub_self,sub_zero] using hh
  have hxi : (∫ Z, star (u Z)*(-X (X v) Z) ∂greenRectangle l r a b)=
      ∫ Z, star (X u Z)*X v Z ∂greenRectangle l r a b := by
    unfold greenRectangle at hFX hEX ⊢
    rw [integral_prod_symm _ hFX,integral_prod_symm _ hEX]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    simpa only [intervalIntegral.integral_of_le hlr] using hhor y (lt_trans ha hy.1)
  have hyi : (∫ Z, star (u Z)*(-Y (Y v) Z) ∂greenRectangle l r a b)=
      ∫ Z, star (Y u Z)*Y v Z ∂greenRectangle l r a b := by
    unfold greenRectangle at hFY hEY ⊢
    rw [integral_prod _ hFY,integral_prod _ hEY]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simpa only [intervalIntegral.integral_of_le hab] using hvert x
  have hae : ∀ᵐ Z ∂greenRectangle l r a b, 0<Z.2 := by
    unfold greenRectangle
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with Z hZ
    exact lt_trans ha hZ.2.1
  calc
    _ = ∫ Z, star (u Z)*(-X (X v) Z)+star (u Z)*(-Y (Y v) Z)
        ∂greenRectangle l r a b := by
      apply integral_congr_ae
      filter_upwards [hae] with Z hZ
      rw [XX_eq_deriv hv hs hZ,YY_eq_deriv hv hs hZ]
      unfold hyperbolic euclidean
      simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_pow]
      have hzC : (Z.2:ℂ)≠0 := by exact_mod_cast hZ.ne'
      field_simp
      ring
    _ = _ := by rw [integral_add hFX hFY,hxi,hyi,integral_add hEX hEY]

/-- Vanishing of the first test at all sides is one sufficient boundary
condition for the exact rectangle identity. -/
theorem green_rectangle (l r a b : ℝ) (hlr : l≤r) (ha : 0<a) (hab : a≤b)
    {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hul : ∀ y, u (l,y)=0) (hur : ∀ y, u (r,y)=0)
    (hua : ∀ x, u (x,a)=0) (hub : ∀ x, u (x,b)=0) :
    (∫ Z, star (u Z)*hyperbolic v Z/(Z.2:ℂ)^2 ∂greenRectangle l r a b)=
      ∫ Z, star (X u Z)*X v Z+star (Y u Z)*Y v Z ∂greenRectangle l r a b := by
  apply green_rectangle_boundary l r a b hlr ha hab hu hv
  · intro y; simp [hul]
  · intro y; simp [hur]
  · intro x; simp [hua]
  · intro x; simp [hub]

#print axioms green_rectangle

end QuantitativeMaass
