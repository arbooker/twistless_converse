module

public import QuantitativeNinaMaassFourierTestsV1
public import QuantitativeNinaMaassWeakRegularityV1
public import QuantitativeNinaMaassPhysicalCoefficientsV1
public import QuantitativeMaassCuspRectangleIntegralV1
public import QuantitativeMaassCuspPeriodicIntegralV1
public import QuantitativeMaassClassicalGraphV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane QuantitativeMaass
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology ContDiff InnerProductSpace

/-!
The Fourier-mode weak differential equation is obtained from genuine
compact tests in the actual Friedrichs graph. Its profile is a literal
horocycle integral of an actual continuous automorphic representative.
-/

namespace QuantitativeNinaMaass

def cartesianFourier (F : ℍ → ℂ) (n : ℤ) (y : ℝ) : ℂ :=
  unitLineFourierCoeff (fun x => F (cartesianLift (x, y))) n

theorem cartesianFourier_continuousOn (F : ℍ → ℂ) (hF : Continuous F) (n : ℤ) :
    ContinuousOn (cartesianFourier F n) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (fun W : (Ioi (0 : ℝ)) × ℝ => cartesianLift (W.2, W.1.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro W
    have hp : Continuous (fun V : (Ioi (0 : ℝ)) × ℝ => (V.2, V.1.val)) :=
      continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
    exact ContinuousAt.comp' (f := fun V : (Ioi (0 : ℝ)) × ℝ => (V.2, V.1.val)) (x := W)
      (cartesianLift_continuousAt (W.2, W.1.val) W.1.property) hp.continuousAt
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (((lineCharacter_smooth (-n)).continuous.comp continuous_snd).mul (hF.comp hc)) 0 1

theorem cartesianFourier_horocycle (F : ℍ → ℂ) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    cartesianFourier F n y = unitLineFourierCoeff (fun x => F (horocyclePoint x y hy)) n := by
  unfold cartesianFourier
  congr 1
  funext x
  rw [cartesianLift_positive _ hy]

theorem compactFourierTest_setIntegral (n : ℤ) (F : ℝ → ℂ)
    (hF : Continuous F) (hp : Function.Periodic F 1) :
    (∫ x in Icc (0 : ℝ) 2, star (compactFourierTest n x) * F x) = unitLineFourierCoeff F n := by
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
    integral_Icc_eq_integral_Ioc] using compactFourierTest_integral n F hF hp

theorem compactFourierTest_second_setIntegral (n : ℤ) (F : ℝ → ℂ)
    (hF : Continuous F) (hp : Function.Periodic F 1) :
    (∫ x in Icc (0 : ℝ) 2, star (deriv (deriv (compactFourierTest n)) x) * F x) =
      ((-((2 * Real.pi * (n : ℝ)) ^ 2) : ℝ) : ℂ) * unitLineFourierCoeff F n := by
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
    integral_Icc_eq_integral_Ioc] using compactFourierTest_second_integral n F hF hp

theorem fourierTensor_rectangle_integral (n : ℤ) (a b : ℝ) (ha : 0 < a)
    (g : ℝ → ℂ) (hg : Continuous g) (F : ℍ → ℂ) (hF : Continuous F)
    (hp : ∀ y, 0 < y → Function.Periodic (fun x => F (cartesianLift (x, y))) 1) :
    (∫ Z in upperRectangle 0 2 a b,
      star (upperFunction (cuspTensor (compactFourierTest n) g) Z) * F Z) =
      ∫ y in Icc a b, star (g y) * cartesianFourier F n y / (y : ℂ) ^ 2 := by
  have hc : Continuous (fun Z : ℍ =>
      star (upperFunction (cuspTensor (compactFourierTest n) g) Z) * F Z) :=
    ((((compactFourierTest_smooth n).continuous.comp continuous_re).mul
      (hg.comp continuous_im)).star).mul hF
  rw [integral_upperRectangle_iterated 0 2 a b ha _ hc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have hpos := ha.trans_le hy.1
  have he : (fun x : ℝ =>
      star (upperFunction (cuspTensor (compactFourierTest n) g) (cartesianLift (x, y))) *
        F (cartesianLift (x, y)) / (y : ℂ) ^ 2) =
      fun x => (star (g y) / (y : ℂ) ^ 2) *
        (star (compactFourierTest n x) * F (cartesianLift (x, y))) := by
    funext x
    rw [cartesianLift_positive _ hpos]
    change star (compactFourierTest n x * g y) * F (horocyclePoint x y hpos) / (y : ℂ) ^ 2 =
      (star (g y) / (y : ℂ) ^ 2) * (star (compactFourierTest n x) * F (horocyclePoint x y hpos))
    rw [star_mul]
    ring
  rw [he, integral_const_mul, compactFourierTest_setIntegral n (fun x => F (cartesianLift (x, y)))
    (hF.comp (cartesianLift_horizontal_continuous y hpos)) (hp y hpos)]
  change (star (g y) / (y : ℂ) ^ 2) * cartesianFourier F n y = _
  ring

theorem fourierTensor_laplacian_rectangle_integral (n : ℤ) (a b : ℝ) (ha : 0 < a)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (F : ℍ → ℂ) (hF : Continuous F)
    (hp : ∀ y, 0 < y → Function.Periodic (fun x => F (cartesianLift (x, y))) 1) :
    (∫ Z in upperRectangle 0 2 a b,
      star (upperLaplacian (cuspTensor (compactFourierTest n) g) Z) * F Z) =
      ∫ y in Icc a b,
        (((2 * Real.pi * (n : ℝ)) ^ 2 : ℝ) * star (g y) - star (deriv (deriv g) y)) *
          cartesianFourier F n y := by
  have hh := compactFourierTest_smooth n
  have hdd := (contDiff_infty_iff_deriv.mp hh).2
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have hLc : Continuous (upperLaplacian (cuspTensor (compactFourierTest n) g)) := by
    have he : upperLaplacian (cuspTensor (compactFourierTest n) g) =
        fun Z : ℍ => -(Z.im : ℂ) ^ 2 *
          (deriv (deriv (compactFourierTest n)) Z.re * g Z.im +
            compactFourierTest n Z.re * deriv (deriv g) Z.im) := by
      funext Z
      exact cuspTensor_laplacian _ _ _
    rw [he]
    exact ((Complex.continuous_ofReal.comp continuous_im).pow 2).neg.mul
      ((((hdd.continuous_deriv (by simp)).comp continuous_re).mul (hg.continuous.comp continuous_im)).add
        ((hh.continuous.comp continuous_re).mul ((hg'.continuous_deriv (by simp)).comp continuous_im)))
  rw [integral_upperRectangle_iterated 0 2 a b ha
    (fun Z => star (upperLaplacian (cuspTensor (compactFourierTest n) g) Z) * F Z) (hLc.star.mul hF)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have hpos := ha.trans_le hy.1
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  let f : ℝ → ℂ := fun x => F (cartesianLift (x, y))
  have hf : Continuous f := hF.comp (cartesianLift_horizontal_continuous y hpos)
  have he : (fun x : ℝ =>
      star (upperLaplacian (cuspTensor (compactFourierTest n) g) (cartesianLift (x, y))) *
        F (cartesianLift (x, y)) / (y : ℂ) ^ 2) =
      fun x => (-star (g y)) * (star (deriv (deriv (compactFourierTest n)) x) * f x) +
        (-star (deriv (deriv g) y)) * (star (compactFourierTest n x) * f x) := by
    funext x
    dsimp only [f]
    rw [cartesianLift_positive _ hpos]
    rw [upperLaplacian, cuspTensor_laplacian]
    change star (-(y : ℂ) ^ 2 * (deriv (deriv (compactFourierTest n)) x * g y +
      compactFourierTest n x * deriv (deriv g) y)) * F (horocyclePoint x y hpos) / (y : ℂ) ^ 2 =
      (-star (g y)) * (star (deriv (deriv (compactFourierTest n)) x) * F (horocyclePoint x y hpos)) +
        (-star (deriv (deriv g) y)) * (star (compactFourierTest n x) * F (horocyclePoint x y hpos))
    simp only [star_mul, star_neg, star_pow, star_add, Complex.star_def, Complex.conj_ofReal]
    field_simp [hy0]
    ring
  have hi₁ : IntegrableOn (fun x => star (deriv (deriv (compactFourierTest n)) x) * f x)
      (Icc (0 : ℝ) 2) :=
    ((hdd.continuous_deriv (by simp)).star.mul hf).continuousOn.integrableOn_compact isCompact_Icc
  have hi₂ : IntegrableOn (fun x => star (compactFourierTest n x) * f x) (Icc (0 : ℝ) 2) :=
    (hh.continuous.star.mul hf).continuousOn.integrableOn_compact isCompact_Icc
  rw [he, integral_add (hi₁.const_mul _) (hi₂.const_mul _), integral_const_mul, integral_const_mul,
    compactFourierTest_second_setIntegral n f hf (hp y hpos),
    compactFourierTest_setIntegral n f hf (hp y hpos)]
  change _ = _ * unitLineFourierCoeff f n
  push_cast
  ring

/-- Every actual continuous Friedrichs eigenvector satisfies the compact
Fourier-mode equation. Horizontal periodicity follows from automorphy. -/
theorem fourierTensor_eigen_equation (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (ell : ℂ)
    (heigen : FriedrichsGraph N (AutomorphicL2.denseEmbedding _ _ f)
      (ell • AutomorphicL2.denseEmbedding _ _ f))
    (n : ℤ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support g ⊆ Icc a b) :
    (∫ y in Icc a b,
      (((2 * Real.pi * (n : ℝ)) ^ 2 : ℝ) * star (g y) - star (deriv (deriv g) y)) *
        cartesianFourier f.val n y) =
      ell * ∫ y in Icc a b, star (g y) * cartesianFourier f.val n y / (y : ℂ) ^ 2 := by
  let u := fourierTensorSeed n g hg a b ha hs
  have hp (y : ℝ) (hy : 0 < y) :
      Function.Periodic (fun x => f.val (cartesianLift (x, y))) 1 := by
    have he (x : ℝ) : cartesianLift (x, y) = horocyclePoint x y hy := by
      rw [cartesianLift_positive _ hy]
    simp_rw [he]
    exact representative_unit_periodic N f y hy
  have hu : tsupport (upperFunction u.toFun) ⊆ upperRectangle 0 2 a b :=
    cuspTensor_support _ _ _ _ _ _ ha (compactFourierTest_support n) hs
  have hbase : (∫ Z : ℍ, star (upperFunction u.toFun Z) * f.val Z) =
      ∫ y in Icc a b, star (g y) * cartesianFourier f.val n y / (y : ℂ) ^ 2 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := upperRectangle 0 2 a b) (fun Z hZ => by
        have hz : upperFunction u.toFun Z = 0 := by
          by_contra hn
          exact hZ (hu (subset_tsupport _ hn))
        rw [hz, star_zero, zero_mul])]
    exact fourierTensor_rectangle_integral n a b ha g hg.continuous f.val hf hp
  have hlap : (∫ Z : ℍ, star (upperFunction u.laplacian.toFun Z) * f.val Z) =
      ∫ y in Icc a b,
        (((2 * Real.pi * (n : ℝ)) ^ 2 : ℝ) * star (g y) - star (deriv (deriv g) y)) *
          cartesianFourier f.val n y := by
    change (∫ Z : ℍ, star (upperLaplacian u.toFun Z) * f.val Z) = _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := upperRectangle 0 2 a b) (fun Z hZ => by
        have hz : upperLaplacian u.toFun Z = 0 := by
          by_contra hn
          exact hZ (hu (upperLaplacian_support _ hn))
        rw [hz, star_zero, zero_mul])]
    exact fourierTensor_laplacian_rectangle_integral n a b ha g hg f.val hf hp
  have hh := friedrichsGraph_symmetric N (friedrichsGraph_poincareSeed N u) heigen
  rw [inner_smul_right (𝕜 := ℂ) (poincareSeedVector N u)
    (AutomorphicL2.denseEmbedding _ _ f), poincareSeed_pairing_representative,
    poincareSeed_pairing_representative, hlap, hbase] at hh
  exact hh

def fourierHeightPotential (n : ℤ) (ell : ℂ) (y : ℝ) : ℂ :=
  (((2 * Real.pi * (n : ℝ)) ^ 2 : ℝ) : ℂ) - ell / (y : ℂ) ^ 2

theorem fourierHeightPotential_continuousOn (n : ℤ) (ell : ℂ) :
    ContinuousOn (fourierHeightPotential n ell) (Ioi 0) :=
  continuous_const.continuousOn.sub (continuous_const.continuousOn.div
    (Complex.continuous_ofReal.pow 2).continuousOn
    (fun _ hy => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hy))))

/-- The tested equation for each literal height profile, on the full
positive test space. The coefficients and the hyperbolic y^-2 term come
from the actual compact Friedrichs pairings above. -/
theorem friedrichs_fourier_weak_equation (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (ell : ℂ)
    (heigen : FriedrichsGraph N (AutomorphicL2.denseEmbedding _ _ f)
      (ell • AutomorphicL2.denseEmbedding _ _ f)) (n : ℤ) (φ : PositiveSmoothTest) :
    (∫ y, positiveSmoothTestDeriv (positiveSmoothTestDeriv φ) y • cartesianFourier f.val n y) =
      ∫ y, φ y • (fourierHeightPotential n ell y * cartesianFourier f.val n y) := by
  let I := positiveSmoothTestInterval φ
  let D := positiveSmoothTestDeriv (positiveSmoothTestDeriv φ)
  let F := cartesianFourier f.val n
  let g : ℝ → ℂ := fun y => (φ y : ℂ)
  let k : ℂ := (((2 * Real.pi * (n : ℝ)) ^ 2 : ℝ) : ℂ)
  have hF : ContinuousOn F (Ioi 0) := cartesianFourier_continuousOn f.val hf n
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hs : Function.support g ⊆ Icc I.left I.right := by
    intro y hy
    apply I.subset
    apply subset_tsupport
    intro hz
    exact hy (by simp only [g, hz, Complex.ofReal_zero])
  have hDsup : tsupport D ⊆ tsupport φ :=
    (positiveSmoothTestDeriv_tsupport_subset (positiveSmoothTestDeriv φ)).trans
      (positiveSmoothTestDeriv_tsupport_subset φ)
  have hgdd : deriv (deriv g) = fun y => (D y : ℂ) :=
    (positiveSmoothTestToAbel_second φ).symm
  have h := fourierTensor_eigen_equation N f hf ell heigen n g hg I.left I.right I.left_pos hs
  rw [hgdd] at h
  simp only [g, Complex.star_def, Complex.conj_ofReal] at h
  change (∫ y in Icc I.left I.right, (k * (φ y : ℂ) - (D y : ℂ)) * F y) =
    ell * ∫ y in Icc I.left I.right, (φ y : ℂ) * F y / (y : ℂ) ^ 2 at h
  have hz (y : ℝ) (hy : y ∉ Icc I.left I.right) : φ y = 0 ∧ D y = 0 := by
    constructor
    · by_contra hn
      exact hy (I.subset (subset_tsupport _ hn))
    · by_contra hn
      exact hy (I.subset (hDsup (subset_tsupport _ hn)))
  have hl : (∫ y in Icc I.left I.right, (k * (φ y : ℂ) - (D y : ℂ)) * F y) =
      ∫ y, (k * (φ y : ℂ) - (D y : ℂ)) * F y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [(hz y hy).1, (hz y hy).2, Complex.ofReal_zero, mul_zero, sub_self, zero_mul])
  have hr : (∫ y in Icc I.left I.right, (φ y : ℂ) * F y / (y : ℂ) ^ 2) =
      ∫ y, (φ y : ℂ) * F y / (y : ℂ) ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [(hz y hy).1, Complex.ofReal_zero, zero_mul, zero_div])
  rw [hl, hr] at h
  have hi : Integrable (fun y => (φ y : ℂ) * F y) := by
    simpa only [Complex.real_smul] using positiveTest_smul_integrable F hF φ
  have hiD : Integrable (fun y => (D y : ℂ) * F y) := by
    simpa only [Complex.real_smul] using positiveTest_smul_integrable F hF D
  have hdiv : ContinuousOn (fun y => F y / (y : ℂ) ^ 2) (Ioi 0) :=
    hF.div (Complex.continuous_ofReal.pow 2).continuousOn
      (fun y hy => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hy)))
  have hiQ : Integrable (fun y => (φ y : ℂ) * (F y / (y : ℂ) ^ 2)) := by
    simpa only [Complex.real_smul] using positiveTest_smul_integrable _ hdiv φ
  have hsplit : (fun y => (k * (φ y : ℂ) - (D y : ℂ)) * F y) =
      fun y => k * ((φ y : ℂ) * F y) - (D y : ℂ) * F y := by
    funext y
    ring
  rw [hsplit, integral_sub (hi.const_mul k) hiD, integral_const_mul] at h
  simp_rw [mul_div_assoc] at h
  have hforce : (fun y => φ y • (fourierHeightPotential n ell y * F y)) =
      fun y => k * ((φ y : ℂ) * F y) - ell * ((φ y : ℂ) * (F y / (y : ℂ) ^ 2)) := by
    funext y
    simp only [Complex.real_smul, fourierHeightPotential, k]
    ring
  change (∫ y, (D y : ℂ) * F y) = ∫ y, φ y • (fourierHeightPotential n ell y * F y)
  rw [hforce, integral_sub (hi.const_mul k) (hiQ.const_mul ell), integral_const_mul, integral_const_mul]
  linear_combination -h

/-- Classical height derivatives of every actual continuous Friedrichs
eigenvector. This is derived from the weak equation, without assuming
spatial smoothness or a Fourier--Bessel expansion of the vector. -/
theorem friedrichs_fourier_classical (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (ell : ℂ)
    (heigen : FriedrichsGraph N (AutomorphicL2.denseEmbedding _ _ f)
      (ell • AutomorphicL2.denseEmbedding _ _ f)) (n : ℤ) :
    ∃ F' : ℝ → ℂ, ContinuousOn F' (Ioi 0) ∧ ∀ y, 0 < y →
      HasDerivAt (cartesianFourier f.val n) (F' y) y ∧
        HasDerivAt F' (fourierHeightPotential n ell y * cartesianFourier f.val n y) y := by
  have hF := cartesianFourier_continuousOn f.val hf n
  exact positive_weak_second_regular _ _ hF
    ((fourierHeightPotential_continuousOn n ell).mul hF)
    (friedrichs_fourier_weak_equation N f hf ell heigen n)

#print axioms cartesianFourier_continuousOn
#print axioms cartesianFourier_horocycle
#print axioms fourierTensor_rectangle_integral
#print axioms fourierTensor_laplacian_rectangle_integral
#print axioms fourierTensor_eigen_equation
#print axioms fourierHeightPotential_continuousOn
#print axioms friedrichs_fourier_weak_equation
#print axioms friedrichs_fourier_classical

end QuantitativeNinaMaass
