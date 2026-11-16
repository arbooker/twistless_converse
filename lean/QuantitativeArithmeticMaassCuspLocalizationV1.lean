module
public import AsymptoticOrbitDensityCoverV1
public import MaassDirectionalV1
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import QuantitativeArithmeticMaassCuspMassIdentitiesV1
public import QuantitativeArithmeticMaassHighCuspEnergyTheoryV4
public import QuantitativeMaassCoshLocalizedEnergyV1
public import QuantitativeMaassCuspPoincareV1
public import QuantitativeMaassFriedrichsCoreV1
public import QuantitativeMaassLVCuspHeightV1
public import QuantitativeMaassLocalRestrictionCoherenceV1
public import QuantitativeSpectralObservabilityFundamentalV1

/-! Cusp localization on the completed automorphic Hilbert space.

The proof retains the horizontal mean through form-core approximation,
constructs the actual infinite-tail operators, covers the quotient by a
compact core and finitely many tails, and proves the matching raw-area
Bessel estimate. No discrete spectral decomposition is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace QuantitativeArithmeticMaassCuspMeanDefect

/-- Poincare with the horizontal mean retained. This estimate applies before
passing to the closed cuspidal space: the approximating smooth functions
need not themselves have zero mean. -/
theorem horizontal_energy_with_mean (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (w : ℝ) (hw : 0 < w) (c : ℂ)
    (hc : (∫ x in (0:ℝ)..w, f x) = w • c) :
    (∫ x in (0:ℝ)..w, ‖f x‖^2) ≤
      2*w^2*(∫ x in (0:ℝ)..w, ‖deriv f x‖^2) + 2*w*‖c‖^2 := by
  let g : ℝ → ℂ := fun x => f x-c
  have hg : ContDiff ℝ ∞ g := hf.sub contDiff_const
  have hmean : (∫ x in (0:ℝ)..w, g x) = 0 := by
    dsimp [g]
    rw [intervalIntegral.integral_sub (hf.continuous.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), hc]
    simp only [intervalIntegral.integral_const, sub_zero, sub_self]
  have hd : deriv g = deriv f := deriv_sub_const_fun c
  have hp := QuantitativeMaass.zero_mean_horizontal_energy g hg w hw hmean
  rw [hd] at hp
  have hpoint (x : ℝ) : ‖f x‖^2 ≤ 2*‖g x‖^2 + 2*‖c‖^2 := by
    have he : f x = g x+c := by dsimp [g]; abel
    have ht : ‖f x‖ ≤ ‖g x‖+‖c‖ := by rw [he]; exact norm_add_le _ _
    have hs := pow_le_pow_left₀ (norm_nonneg (f x)) ht 2
    nlinarith [sq_nonneg (‖g x‖-‖c‖)]
  have hi := intervalIntegral.integral_mono_on (μ := volume) hw.le
    ((hf.continuous.norm.pow 2).intervalIntegrable (0:ℝ) w)
    (((continuous_const.mul (hg.continuous.norm.pow 2)).add
      continuous_const).intervalIntegrable (0:ℝ) w)
    (fun x (_ : x ∈ Icc 0 w) => hpoint x)
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply] at hi
  have hgi : IntervalIntegrable (fun x : ℝ => 2*‖g x‖^2) volume 0 w :=
    (continuous_const.mul (hg.continuous.norm.pow 2)).intervalIntegrable _ _
  have hci : IntervalIntegrable (fun _x : ℝ => 2*‖c‖^2) volume 0 w :=
    continuous_const.intervalIntegrable _ _
  have he : (∫ x in (0:ℝ)..w, 2*‖g x‖^2 + 2*‖c‖^2) =
      2*(∫ x in (0:ℝ)..w, ‖g x‖^2)+2*w*‖c‖^2 := by
    rw [intervalIntegral.integral_add hgi hci, intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [he] at hi
  linarith

#print axioms horizontal_energy_with_mean
end QuantitativeArithmeticMaassCuspMeanDefect
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace QuantitativeArithmeticMaassCuspBand
open MaassDifferential QuantitativeArithmeticMaassCuspMeanDefect

/-- Smoothness in a horizontal slice follows from smoothness on the upper
half-plane, without an extension across its boundary. -/
theorem horizontal_slice_smooth (u : Point → ℂ)
    (hu : ContDiffOn ℝ ∞ u {Z | 0 < Z.2}) (y : ℝ) (hy : 0 < y) :
    ContDiff ℝ ∞ (fun x : ℝ => u (x,y)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hopen : IsOpen {Z : Point | 0 < Z.2} :=
    isOpen_lt continuous_const continuous_snd
  exact (hu.contDiffAt (hopen.mem_nhds hy)).comp x
    (contDiff_id.prodMk contDiff_const).contDiffAt

/-- The horizontal mean-defect inequality with the actual hyperbolic weight.
Its derivative coefficient is uniform for every height y at least Y. -/
theorem weighted_horizontal_mass_le (u : Point → ℂ)
    (hu : ContDiffOn ℝ ∞ u {Z | 0 < Z.2})
    (w Y y : ℝ) (hw : 0 < w) (hY : 0 < Y) (hy : Y ≤ y) (c : ℂ)
    (hc : (∫ x in (0:ℝ)..w, u (x,y)) = w • c) :
    (∫ x in (0:ℝ)..w, ‖u (x,y)‖^2)/y^2 ≤
      (2*w^2/Y^2)*(∫ x in (0:ℝ)..w, ‖X u (x,y)‖^2) + 2*w*‖c‖^2/y^2 := by
  have hypos : 0 < y := hY.trans_le hy
  have hopen : IsOpen {Z : Point | 0 < Z.2} :=
    isOpen_lt continuous_const continuous_snd
  have hderiv : deriv (fun x : ℝ => u (x,y)) = fun x => X u (x,y) := by
    funext x
    exact (X_eq_deriv hu hopen (x := x) (y := y) hypos).symm
  have hp := horizontal_energy_with_mean (fun x => u (x,y))
    (horizontal_slice_smooth u hu y hypos) w hw c hc
  rw [hderiv] at hp
  let D := ∫ x in (0:ℝ)..w, ‖X u (x,y)‖^2
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg_of_forall
    (μ := volume) hw.le (fun x => sq_nonneg ‖X u (x,y)‖)
  have hnum : 0 ≤ 2*w^2*D := by positivity
  have hsq : Y^2 ≤ y^2 := pow_le_pow_left₀ hY.le hy 2
  calc
    _ ≤ (2*w^2*D + 2*w*‖c‖^2)/y^2 :=
      div_le_div_of_nonneg_right hp (sq_nonneg y)
    _ = (2*w^2*D)/y^2 + 2*w*‖c‖^2/y^2 := add_div _ _ _
    _ ≤ (2*w^2*D)/Y^2 + 2*w*‖c‖^2/y^2 :=
      add_le_add (div_le_div_of_nonneg_left hnum (sq_pos_of_pos hY) hsq) le_rfl
    _ = _ := by dsimp [D]; ring

#print axioms horizontal_slice_smooth
#print axioms weighted_horizontal_mass_le
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped Topology ContDiff
namespace QuantitativeArithmeticMaassCuspBand
open MaassDifferential QuantitativeMaass QuantitativeArithmeticMaassCuspMass

/-- Integrability needed for Fubini and order comparison on a finite band. -/
theorem rectangle_iterated_integrable (l r Y H : ℝ) (hY : 0 < Y)
    (F : ℍ → ℝ) (hF : Continuous F) :
    IntegrableOn (fun y => ∫ x in Icc l r, F (cartesianLift (x,y))/y^2) (Icc Y H) := by
  have hc : ContinuousOn cartesianLift (Icc l r ×ˢ Icc Y H) := by
    intro Z hZ
    exact (cartesianLift_continuousAt Z (hY.trans_le hZ.2.1)).continuousWithinAt
  have ht : ContinuousOn (fun Z : ℝ × ℝ => F (cartesianLift Z)/Z.2^2)
      (Icc l r ×ˢ Icc Y H) :=
    (hF.comp_continuousOn hc).div ((continuous_snd.pow 2).continuousOn)
      (fun Z hZ => pow_ne_zero 2 (ne_of_gt (hY.trans_le hZ.2.1)))
  have hi : IntegrableOn (fun Z : ℝ × ℝ => F (cartesianLift Z)/Z.2^2)
      (Icc l r ×ˢ Icc Y H) volume :=
    ht.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  change Integrable _ (((volume : Measure ℝ).prod volume).restrict (Icc l r ×ˢ Icc Y H)) at hi
  rw [← Measure.prod_restrict] at hi
  exact hi.integral_prod_right

/-- Actual finite-band mass estimate. The mean is retained as the genuine
height-marginal integral, allowing later passage through the full form core. -/
theorem smooth_band_mass_le (u : Point → ℂ)
    (hu : ContDiffOn ℝ ∞ u {Z | 0 < Z.2})
    (w Y H : ℝ) (hw : 0 < w) (hY : 0 < Y) :
    (∫ z in upperRectangle 0 w Y H, ‖upperFunction u z‖^2) ≤
      (2*w^2/Y^2)*(∫ z in upperRectangle 0 w Y H,
        z.im^2*‖upperFunction (X u) z‖^2) +
      2*(∫ y, ‖horocycleAverageExtension 0 w Y (upperFunction u) y‖^2
        ∂heightMeasure (upperRectangle 0 w Y H)) := by
  let m := horocycleAverageExtension 0 w Y (upperFunction u)
  let A : ℍ → ℝ := fun z => ‖upperFunction u z‖^2
  let B : ℍ → ℝ := fun z => z.im^2*‖upperFunction (X u) z‖^2
  let C : ℍ → ℝ := fun z => ‖m z.im‖^2
  let J : (ℍ → ℝ) → ℝ → ℝ := fun F y =>
    ∫ x in Icc (0:ℝ) w, F (cartesianLift (x,y))/y^2
  have hU := upperFunction_continuous hu
  have hopen : IsOpen {Z : Point | 0 < Z.2} :=
    isOpen_lt continuous_const continuous_snd
  have hX : Continuous (upperFunction (X u)) :=
    upperFunction_continuous (dir_contDiffOn hu hopen e₁)
  have hm : Continuous m := horocycleAverageExtension_continuous 0 w Y hY _ hU
  have hA : Continuous A := hU.norm.pow 2
  have hB : Continuous B := (continuous_im.pow 2).mul (hX.norm.pow 2)
  have hC : Continuous C := (hm.comp continuous_im).norm.pow 2
  have hiA : IntegrableOn (J A) (Icc Y H) := rectangle_iterated_integrable 0 w Y H hY A hA
  have hiB : IntegrableOn (J B) (Icc Y H) := rectangle_iterated_integrable 0 w Y H hY B hB
  have hiC : IntegrableOn (J C) (Icc Y H) := rectangle_iterated_integrable 0 w Y H hY C hC
  have hpoint : ∀ᵐ y ∂volume.restrict (Icc Y H),
      J A y ≤ (2*w^2/Y^2)*J B y + 2*J C y := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hypos : 0 < y := hY.trans_le hy.1
    have hmval : m y = (w:ℂ)⁻¹*(∫ x in Icc (0:ℝ) w, u (x,y)) := by
      dsimp only [m, horocycleAverageExtension]
      simp only [sub_zero, max_eq_right hy.1]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => upperFunction_cartesianLift hypos)
    have hmean : (∫ x in (0:ℝ)..w, u (x,y)) = w • m y := by
      rw [intervalIntegral.integral_of_le hw.le, ← integral_Icc_eq_integral_Ioc,
        hmval, Complex.real_smul]
      simp only [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hw.ne'), one_mul]
    have hp := weighted_horizontal_mass_le u hu w Y y hw hY hy.1 (m y) hmean
    have hJa : J A y = (∫ x in (0:ℝ)..w, ‖u (x,y)‖^2)/y^2 := by
      dsimp only [J, A]
      have he (x : ℝ) : upperFunction u (cartesianLift (x,y)) = u (x,y) :=
        upperFunction_cartesianLift hypos
      simp_rw [he]
      rw [integral_div, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hw.le]
    have hJb : J B y = ∫ x in (0:ℝ)..w, ‖X u (x,y)‖^2 := by
      dsimp only [J, B]
      have he (x : ℝ) : (cartesianLift (x,y)).im^2*
          ‖upperFunction (X u) (cartesianLift (x,y))‖^2/y^2 = ‖X u (x,y)‖^2 := by
        rw [upperFunction_cartesianLift hypos, cartesianLift_positive _ hypos]
        change y^2*‖X u (x,y)‖^2/y^2 = ‖X u (x,y)‖^2
        exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hypos.ne')
      simp_rw [he]
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hw.le]
    have hJc : J C y = w*‖m y‖^2/y^2 := by
      dsimp only [J, C]
      have he (x : ℝ) : ‖m (cartesianLift (x,y)).im‖^2/y^2 = ‖m y‖^2/y^2 := by
        rw [cartesianLift_positive _ hypos]
        rfl
      simp_rw [he]
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
        sub_zero, ENNReal.toReal_ofReal hw.le, smul_eq_mul]
      ring
    rw [hJa,hJb,hJc]
    have he : 2*w*‖m y‖^2/y^2 = 2*(w*‖m y‖^2/y^2) := by ring
    simpa only [he] using hp
  have hbound := integral_mono_ae hiA ((hiB.const_mul (2*w^2/Y^2)).add (hiC.const_mul 2)) hpoint
  dsimp only [Pi.add_apply, Pi.mul_apply] at hbound
  rw [integral_add (hiB.const_mul (2*w^2/Y^2)) (hiC.const_mul 2),
    integral_const_mul, integral_const_mul] at hbound
  have hAe := rectangle_real_integral 0 w Y H hY A hA
  have hBe := rectangle_real_integral 0 w Y H hY B hB
  have hCe := rectangle_real_integral 0 w Y H hY C hC
  change (∫ z in upperRectangle 0 w Y H, A z) = ∫ y in Icc Y H, J A y at hAe
  change (∫ z in upperRectangle 0 w Y H, B z) = ∫ y in Icc Y H, J B y at hBe
  change (∫ z in upperRectangle 0 w Y H, C z) = ∫ y in Icc Y H, J C y at hCe
  rw [← hAe, ← hBe, ← hCe] at hbound
  have hmarg : (∫ y, ‖m y‖^2 ∂heightMeasure (upperRectangle 0 w Y H)) =
      ∫ z in upperRectangle 0 w Y H, C z := by
    have hmnorm : AEStronglyMeasurable (fun y : ℝ => ‖m y‖^2)
        (heightMeasure (upperRectangle 0 w Y H)) := (hm.norm.pow 2).aestronglyMeasurable
    exact integral_map continuous_im.measurable.aemeasurable hmnorm
  rw [hmarg]
  exact hbound

#print axioms rectangle_iterated_integrable
#print axioms smooth_band_mass_le
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open scoped Topology ContDiff MatrixGroups ENNReal
namespace QuantitativeArithmeticMaassCuspBand
open MaassDifferential QuantitativeMaass QuantitativeArithmeticMaassHighCuspEnergy

/-- The horizontal energy in any high finite band is controlled by the
actual quotient closed form, uniformly in the upper height. -/
theorem seed_horizontal_integral_le (N W : ℕ) (s : SL(2,ℤ))
    (Y H : ℝ) (hY : 2 ≤ Y) (u : SmoothUpperSeed) :
    (∫ z in upperRectangle 0 W Y H,
      z.im^2 * ‖upperFunction (X (congruencePoincareCartesian N u.toFun ∘
        integralCuspChart s)) z‖^2) ≤
      (W+1:ℝ) * (quotientClosedEnergy N (poincareEnergySeed N u)
        (poincareEnergySeed N u)).re := by
  let P := congruencePoincareCartesian N u.toFun ∘ integralCuspChart s
  have hP : ContDiffOn ℝ ∞ P {Z | 0 < Z.2} :=
    integralCuspChart_pullback_smooth s
      (congruencePoincareCartesian_smooth N u.smooth u.compact)
  have hX : Continuous (upperFunction (X P)) := upperFunction_continuous
    (dir_contDiffOn hP (isOpen_lt continuous_const continuous_snd) e₁)
  have hcont : Continuous (fun z : ℍ => z.im^2 * ‖upperFunction (X P) z‖^2) :=
    (continuous_im.pow 2).mul (hX.norm.pow 2)
  have hi : IntegrableOn (fun z : ℍ => z.im^2 * ‖upperFunction (X P) z‖^2)
      (upperRectangle 0 W Y H) volume := hcont.continuousOn.integrableOn_compact
    (upperRectangle_compact 0 W Y H (by linarith))
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun z : ℍ =>
      mul_nonneg (sq_nonneg z.im) (sq_nonneg ‖upperFunction (X P) z‖)))
  have hb := poincare_cusp_horizontal_lintegral_le N W s 0 Y H hY u
  simp only [zero_add] at hb
  change (∫⁻ z in upperRectangle 0 W Y H,
    ENNReal.ofReal (z.im^2 * ‖upperFunction (X P) z‖^2)) ≤ _ at hb
  rw [← he] at hb
  have hq := quotientClosedEnergy_nonnegative N (poincareEnergySeed N u)
  have hr : ENNReal.ofReal ((W+1:ℝ) * (quotientClosedEnergy N
      (poincareEnergySeed N u) (poincareEnergySeed N u)).re) =
      (W+1:ℕ) * ENNReal.ofReal (quotientClosedEnergy N
        (poincareEnergySeed N u) (poincareEnergySeed N u)).re := by
    rw [ENNReal.ofReal_mul (by positivity)]
    rw [show (W+1:ℝ) = ((W+1:ℕ):ℝ) by norm_num, ENNReal.ofReal_natCast]
  rw [← hr] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hq)).mp hb

/-- Smooth Poincare vectors satisfy the cusp mass estimate with their genuine
closed energy and horizontal mean. The constant is independent of H. -/
theorem seed_band_mass_le (N W : ℕ) (hW : 0 < W) (s : SL(2,ℤ))
    (Y H : ℝ) (hY : 2 ≤ Y) (u : SmoothUpperSeed) :
    (∫ z in upperRectangle 0 W Y H,
      ‖upperFunction (congruencePoincareCartesian N u.toFun ∘ integralCuspChart s) z‖^2) ≤
      (2*(W:ℝ)^2/Y^2)*(W+1) *
        (quotientClosedEnergy N (poincareEnergySeed N u) (poincareEnergySeed N u)).re +
      2*(∫ y, ‖horocycleAverageExtension 0 W Y
        (upperFunction (congruencePoincareCartesian N u.toFun ∘ integralCuspChart s)) y‖^2
        ∂heightMeasure (upperRectangle 0 W Y H)) := by
  have hP := integralCuspChart_pullback_smooth s
    (congruencePoincareCartesian_smooth N u.smooth u.compact)
  have hb := smooth_band_mass_le _ hP W Y H (by exact_mod_cast hW) (by linarith)
  have he := seed_horizontal_integral_le N W s Y H hY u
  have hc : 0 ≤ 2*(W:ℝ)^2/Y^2 := by positivity
  apply hb.trans
  simpa only [mul_assoc] using (add_le_add (mul_le_mul_of_nonneg_left he hc) le_rfl)

#print axioms seed_horizontal_integral_le
#print axioms seed_band_mass_le
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology ContDiff MatrixGroups
namespace QuantitativeArithmeticMaassCuspBand
open MaassDifferential QuantitativeMaass QuantitativeArithmeticMaassCuspMass

/-- The smooth estimate is expressed using the existing bounded restriction
and constant-term operators, so both sides extend to the form completion. -/
theorem seed_band_norm_le (N : ℕ) (hN : 0 < N) (s : SL(2,ℤ))
    (Y H : ℝ) (hY : 2 ≤ Y) (u : SmoothUpperSeed) :
    ‖cuspRestriction N s (upperRectangle 0 N Y H)
      (upperRectangle_compact 0 N Y H (by linarith)) (poincareSeedVector N u)‖^2 ≤
      (2*(N:ℝ)^2/Y^2)*(N+1) *
        (quotientClosedEnergy N (poincareEnergySeed N u) (poincareEnergySeed N u)).re +
      2*‖cuspConstantLocal N s Y H (by linarith) (poincareSeedVector N u)‖^2 := by
  let P := congruencePoincareCartesian N u.toFun ∘ integralCuspChart s
  let f : AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
    ⟨_,poincareSeed_representative N u⟩
  have hP := integralCuspChart_pullback_smooth s
    (congruencePoincareCartesian_smooth N u.smooth u.compact)
  have hrep (z : ℍ) : f.val (cuspAction s z) = upperFunction P z := by
    have hp := upperFunction_integral_action (congruencePoincareCartesian N u.toFun)
      s (z.re,z.im) z.im_pos
    have hz : cartesianLift (z.re,z.im) = z := by
      rw [cartesianLift_positive _ z.im_pos]
      ext; rfl
    rw [hz] at hp
    change poincareSum (G := gamma N) (upperFunction u.toFun) (s • z) =
      congruencePoincareCartesian N u.toFun (integralCuspChart s (z.re,z.im))
    simpa only [congruencePoincareCartesian_represents] using hp
  have hnorm := restriction_norm_sq N s (upperRectangle 0 N Y H)
    (upperRectangle_compact 0 N Y H (by linarith)) f
  change ‖cuspRestriction N s _ _ (poincareSeedVector N u)‖^2 = _ at hnorm
  simp_rw [hrep] at hnorm
  have hlocal := localHeightAverage_horocycle_ae 0 (N:ℝ) Y H
    (Nat.cast_pos.mpr hN) (by linarith) (upperFunction P) (upperFunction_continuous hP)
    (cuspRestriction N s _ (upperRectangle_compact 0 N Y H (by linarith))
      (poincareSeedVector N u)) (by
        have h := cuspRestriction_representative_ae N s (upperRectangle 0 N Y H)
          (upperRectangle_compact 0 N Y H (by linarith)) f
        simp_rw [hrep] at h
        simpa only [f,poincareSeedVector] using h)
  have hmean : ‖cuspConstantLocal N s Y H (by linarith) (poincareSeedVector N u)‖^2 =
      ∫ y, ‖horocycleAverageExtension 0 N Y (upperFunction P) y‖^2
        ∂heightMeasure (upperRectangle 0 N Y H) := by
    rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [hlocal] with y hy
    exact congrArg (fun z : ℂ => ‖z‖^2) hy
  rw [hnorm,hmean]
  exact seed_band_mass_le N N hN s Y H hY u

/-- Uniform finite-band mass bound on the full closed energy domain.
The full smooth core is used, and the mean is retained during passage to the
limit; no density assertion about smooth cusp forms is needed. -/
theorem form_band_norm_le (N : ℕ) (hN : 0 < N) (s : SL(2,ℤ))
    (Y H : ℝ) (hY : 2 ≤ Y) (u : QuotientEnergySpace N) :
    ‖cuspRestriction N s (upperRectangle 0 N Y H)
      (upperRectangle_compact 0 N Y H (by linarith)) (energyInclusion N u)‖^2 ≤
      (2*(N:ℝ)^2/Y^2)*(N+1) * (quotientClosedEnergy N u u).re +
      2*‖cuspConstantLocal N s Y H (by linarith) (energyInclusion N u)‖^2 := by
  let A := cuspRestriction N s (upperRectangle 0 N Y H)
    (upperRectangle_compact 0 N Y H (by linarith))
  let B := cuspConstantLocal N s Y H (by linarith)
  let C : ℝ := (2*(N:ℝ)^2/Y^2)*(N+1)
  have he (v : QuotientEnergySpace N) : (quotientClosedEnergy N v v).re =
      ‖v‖^2 - ‖energyInclusion N v‖^2 := by
    linarith [quotientClosedEnergy_norm N v]
  have hclosed : IsClosed {v : QuotientEnergySpace N |
      ‖A (energyInclusion N v)‖^2 ≤ C * (‖v‖^2 - ‖energyInclusion N v‖^2) +
        2*‖B (energyInclusion N v)‖^2} := by
    apply isClosed_le <;> fun_prop
  have hsub : Set.range (fun v : SmoothUpperSeed =>
      (poincareEnergySeed N v : QuotientEnergySpace N)) ⊆
      {v : QuotientEnergySpace N |
        ‖A (energyInclusion N v)‖^2 ≤ C * (‖v‖^2 - ‖energyInclusion N v‖^2) +
          2*‖B (energyInclusion N v)‖^2} := by
    rintro _ ⟨v,rfl⟩
    have hb := seed_band_norm_le N hN s Y H hY v
    simpa only [Set.mem_ofPred_eq,A,B,C,← he,energyInclusion_coe,poincareEnergySeed_value] using hb
  have hall := closure_minimal hsub hclosed (poincareEnergySeed_completion_dense N u)
  simpa only [Set.mem_ofPred_eq,A,B,C,← he] using hall

/-- Geometric cuspidality kills the actual bounded height average, before
any logarithmic change of coordinates, on every positive finite band. -/
theorem cuspidal_constantLocal_zero (N : ℕ) (hN : 0 < N) (s : SL(2,ℤ))
    (Y H : ℝ) (hY : 0 < Y) (hH : 0 < H) (f : AutomorphicSpace N)
    (hf : f ∈ localCuspidalSpace N hN) : cuspConstantLocal N s Y H hY f = 0 := by
  have hz := (mem_localCuspidalSpace N hN f).mp hf s (Real.log Y) (Real.log H)
  have h := (localHalfDensity_eq_zero_iff N (Real.log Y) (Real.log H)
    (Nat.cast_pos.mpr hN) (cuspConstantLocal N s (Real.exp (Real.log Y))
      (Real.exp (Real.log H)) (Real.exp_pos _) f)).mp hz
  have transfer : ∀ (a b : ℝ) (ha : 0 < a), a = Y → b = H →
      cuspConstantLocal N s a b ha f = 0 → cuspConstantLocal N s Y H hY f = 0 := by
    intro a b ha haY hbH hzero
    subst a
    subst b
    exact hzero
  exact transfer _ _ _ (Real.exp_log hY) (Real.exp_log hH) h

/-- Uniform cusp mass bound for every cuspidal vector in the closed energy
form domain. Its Y⁻² decay is independent of the upper height H. -/
theorem cuspidal_form_band_norm_le (N : ℕ) (hN : 0 < N) (s : SL(2,ℤ))
    (Y H : ℝ) (hY : 2 ≤ Y) (hH : 0 < H) (u : QuotientEnergySpace N)
    (hu : energyInclusion N u ∈ localCuspidalSpace N hN) :
    ‖cuspRestriction N s (upperRectangle 0 N Y H)
      (upperRectangle_compact 0 N Y H (by linarith)) (energyInclusion N u)‖^2 ≤
      (2*(N:ℝ)^2/Y^2)*(N+1) * (quotientClosedEnergy N u u).re := by
  have hb := form_band_norm_le N hN s Y H hY u
  rw [cuspidal_constantLocal_zero N hN s Y H (by linarith) hH _ hu,
    norm_zero,zero_pow (by decide),mul_zero,add_zero] at hb
  exact hb

#print axioms cuspidal_constantLocal_zero
#print axioms cuspidal_form_band_norm_le
#print axioms seed_band_norm_le
#print axioms form_band_norm_le
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups ENNReal Pointwise
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass

/-- The norm of the actual local restriction as a nonnegative integral. -/
theorem restriction_norm_lintegral (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ)
    (hK : IsCompact K)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    ENNReal.ofReal (‖cuspRestriction N s K hK
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)‖^2) =
      ∫⁻ z in K, ENNReal.ofReal (‖f.val (cuspAction s z)‖^2) := by
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral,
    ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp _).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  apply lintegral_congr_ae
  filter_upwards [cuspRestriction_representative_ae N s K hK f] with z hz
  rw [hz]

/-- Actual infinite cusp tail estimate for any invariant representative of a
cuspidal vector in the closed form domain. No smoothness is assumed. -/
theorem cuspidal_representative_tail_le (N : ℕ) (hN : 0 < N) (s : SL(2,ℤ))
    (Y : ℝ) (hY : 2 ≤ Y) (u : QuotientEnergySpace N)
    (hu : energyInclusion N u ∈ localCuspidalSpace N hN)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : energyInclusion N u =
      AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) :
    (∫⁻ z in {z : ℍ | z.re ∈ Icc 0 (N:ℝ) ∧ Y ≤ z.im},
      ENNReal.ofReal (‖f.val (cuspAction s z)‖^2)) ≤
      ENNReal.ofReal ((2*(N:ℝ)^2/Y^2)*(N+1)*(quotientClosedEnergy N u u).re) := by
  let K : ℕ → Set ℍ := fun n => upperRectangle 0 N Y (n+1)
  have hm : Monotone K := by
    intro i j hij z hz
    exact ⟨hz.1,hz.2.1,hz.2.2.trans (by exact_mod_cast Nat.add_le_add_right hij 1)⟩
  have hcover : (⋃ n, K n) = {z : ℍ | z.re ∈ Icc 0 (N:ℝ) ∧ Y ≤ z.im} := by
    ext z
    constructor
    · intro hz
      obtain ⟨n,hn⟩ := mem_iUnion.mp hz
      exact ⟨hn.1,hn.2.1⟩
    · intro hz
      obtain ⟨n,hn⟩ := exists_nat_ge z.im
      exact mem_iUnion.mpr ⟨n,hz.1,hz.2,by dsimp only [K]; linarith⟩
  rw [← hcover,setLIntegral_iUnion_of_directed _ hm.directed_le]
  apply iSup_le
  intro n
  have hb := cuspidal_form_band_norm_le N hN s Y (n+1) hY (by positivity) u hu
  rw [hf] at hb
  rw [← restriction_norm_lintegral N s (K n)
    (upperRectangle_compact 0 N Y (n+1) (by linarith)) f]
  exact ENNReal.ofReal_le_ofReal hb

/-- The normalized orbit density converts any orbit-covering set into an
upper bound for genuine quotient mass. This needs no disjointness assertion. -/
theorem quotient_lintegral_le_cover (N : ℕ) (F : ℍ → ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, F (g.val • z) = F z)
    (S : Set ℍ) (hSm : MeasurableSet S)
    (hS : ∀ z : ℍ, ∃ g : gamma N, g.val • z ∈ S) :
    (∫⁻ z, F z ∂quotientMeasure N) ≤ ∫⁻ z in S, F z := by
  have hun := lintegral_poincare_unfold volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (S.indicator F) (hF.indicator hSm)
  rw [← lintegral_indicator hSm F, ← hun]
  apply lintegral_mono
  intro z
  obtain ⟨g,hg⟩ := hS z
  calc
    F z = S.indicator F (g.val • z) := by rw [Set.indicator_of_mem hg,hinv]
    _ ≤ ∑' a : gamma N, S.indicator F (a.val • z) :=
      ENNReal.le_tsum (f := fun a : gamma N => S.indicator F (a.val • z)) g

#print axioms restriction_norm_lintegral
#print axioms cuspidal_representative_tail_le
#print axioms quotient_lintegral_le_cover
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups ENNReal
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass QuantitativeArithmeticMaassHighCuspEnergy

def cuspTailSet (W : ℕ) (Y : ℝ) : Set ℍ :=
  {z | z.re ∈ Icc 0 (W:ℝ) ∧ Y ≤ z.im}

/-- Exhaustion of the infinite cusp strip preserves a uniform finite-band
bound, with no measurability hypothesis on the nonnegative integrand. -/
theorem tail_lintegral_le_of_bands (W : ℕ) (Y : ℝ) (F : ℍ → ℝ≥0∞)
    (C : ℝ≥0∞)
    (h : ∀ H : ℝ, 0 < H → (∫⁻ z in upperRectangle 0 W Y H, F z) ≤ C) :
    (∫⁻ z in cuspTailSet W Y, F z) ≤ C := by
  let K : ℕ → Set ℍ := fun n => upperRectangle 0 W Y (n+1)
  have hm : Monotone K := by
    intro i j hij z hz
    exact ⟨hz.1,hz.2.1,hz.2.2.trans (by exact_mod_cast Nat.add_le_add_right hij 1)⟩
  have he : (⋃ n, K n) = cuspTailSet W Y := by
    ext z
    constructor
    · intro hz
      obtain ⟨n,hn⟩ := mem_iUnion.mp hz
      exact ⟨hn.1,hn.2.1⟩
    · intro hz
      obtain ⟨n,hn⟩ := exists_nat_ge z.im
      exact mem_iUnion.mpr ⟨n,hz.1,hz.2,by dsimp only [K]; linarith⟩
  rw [← he,setLIntegral_iUnion_of_directed _ hm.directed_le]
  exact iSup_le (fun n => h (n+1) (by positivity))

/-- Arbitrary invariant quotient L2 mass has bounded restriction to the
whole high cusp strip. This is independent of cuspidality and energy. -/
theorem representative_tail_mass_le (N W : ℕ) (s : SL(2,ℤ))
    (Y : ℝ) (hY : 2 ≤ Y)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    (∫⁻ z in cuspTailSet W Y, ENNReal.ofReal (‖f.val (cuspAction s z)‖^2)) ≤
      (W+1:ℕ) * ∫⁻ z, ENNReal.ofReal (‖f.val z‖^2) ∂quotientMeasure N := by
  apply tail_lintegral_le_of_bands
  intro H _
  have hb := cusp_rectangle_lintegral_le N W s 0 Y H hY
    (fun z => ENNReal.ofReal (‖f.val z‖^2))
    ((f.property.1.norm.pow_const 2).ennreal_ofReal)
    (fun g z => congrArg (fun v : ℂ => ENNReal.ofReal (‖v‖^2)) (f.property.2.1 g z))
  simpa only [zero_add] using hb

theorem representative_tail_memLp (N W : ℕ) (s : SL(2,ℤ))
    (Y : ℝ) (hY : 2 ≤ Y)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    MemLp (fun z => f.val (cuspAction s z)) 2 (volume.restrict (cuspTailSet W Y)) := by
  have hm := f.property.1.comp (cuspAction_continuous s).measurable
  have hi := (memLp_two_iff_integrable_sq_norm f.property.2.2.aestronglyMeasurable).mp
    f.property.2.2
  have hfin : (∫⁻ z, ENNReal.ofReal (‖f.val z‖^2) ∂quotientMeasure N) < ∞ :=
    (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  refine ⟨(hm.norm.pow_const 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mpr
  exact (representative_tail_mass_le N W s Y hY f).trans_lt
    (ENNReal.mul_lt_top (by simp) hfin)

/-- Literal restriction on the dense representative domain. -/
def representativeTailRestriction (N W : ℕ) (s : SL(2,ℤ)) (Y : ℝ) (hY : 2 ≤ Y) :
    AutomorphicL2.representatives (gamma N) (quotientMeasure N) →ₗ[ℂ]
      Lp ℂ 2 (volume.restrict (cuspTailSet W Y)) where
  toFun f := (representative_tail_memLp N W s Y hY f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun _ => rfl)

theorem representativeTailRestriction_bound (N W : ℕ) (s : SL(2,ℤ))
    (Y : ℝ) (hY : 2 ≤ Y)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    ‖representativeTailRestriction N W s Y hY f‖ ≤
      (W+2:ℝ) * ‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f‖ := by
  have hi := (memLp_two_iff_integrable_sq_norm f.property.2.2.aestronglyMeasurable).mp
    f.property.2.2
  have hfin : (∫⁻ z, ENNReal.ofReal (‖f.val z‖^2) ∂quotientMeasure N) ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2).ne
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin)
    (representative_tail_mass_le N W s Y hY f)
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,
    square_energy_toReal _ (representative_tail_memLp N W s Y hY f),
    square_energy_toReal _ f.property.2.2] at hb
  change ‖representativeTailRestriction N W s Y hY f‖^2 ≤
    ((W+1:ℕ):ℝ) * ‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f‖^2 at hb
  have hmul := mul_le_mul_of_nonneg_right
    (show ((W+1:ℕ):ℝ) ≤ (W+2:ℝ)^2 by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) W])
    (sq_nonneg ‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f‖)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  exact hb.trans hmul

/-- Bounded restriction to the infinite cusp strip on the full quotient
Hilbert space, obtained from actual invariant representatives by density. -/
def cuspTailRestriction (N W : ℕ) (s : SL(2,ℤ)) (Y : ℝ) (hY : 2 ≤ Y) :
    AutomorphicSpace N →L[ℂ] Lp ℂ 2 (volume.restrict (cuspTailSet W Y)) :=
  (representativeTailRestriction N W s Y hY).extendOfNorm
    (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))

theorem cuspTailRestriction_representative (N W : ℕ) (s : SL(2,ℤ))
    (Y : ℝ) (hY : 2 ≤ Y)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    cuspTailRestriction N W s Y hY
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) =
      (representative_tail_memLp N W s Y hY f).toLp _ := by
  apply LinearMap.extendOfNorm_eq
    (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N))
  exact ⟨W+2,representativeTailRestriction_bound N W s Y hY⟩

#print axioms tail_lintegral_le_of_bands
#print axioms representative_tail_mass_le
#print axioms representative_tail_memLp
#print axioms representativeTailRestriction_bound
#print axioms cuspTailRestriction_representative
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups ENNReal
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass

theorem cuspTailRestriction_representative_ae (N W : ℕ) (s : SL(2,ℤ))
    (Y : ℝ) (hY : 2 ≤ Y)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    (cuspTailRestriction N W s Y hY
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) : ℍ → ℂ)
      =ᵐ[volume.restrict (cuspTailSet W Y)] fun z => f.val (cuspAction s z) := by
  rw [cuspTailRestriction_representative]
  exact MemLp.coeFn_toLp _

/-- Restriction to a finite sub-band agrees with the previously constructed
compact restriction on the entire quotient Hilbert space. -/
theorem cuspTailRestriction_coherence (N W : ℕ) (s : SL(2,ℤ))
    (Y H : ℝ) (hY : 2 ≤ Y) (f : AutomorphicSpace N) :
    localRestrictionMap (upperRectangle 0 W Y H) (cuspTailSet W Y)
      (fun _ hz => ⟨hz.1,hz.2.1⟩) (cuspTailRestriction N W s Y hY f) =
      cuspRestriction N s (upperRectangle 0 W Y H)
        (upperRectangle_compact 0 W Y H (by linarith)) f := by
  have he : (fun f : AutomorphicSpace N =>
      localRestrictionMap (upperRectangle 0 W Y H) (cuspTailSet W Y)
        (fun _ hz => ⟨hz.1,hz.2.1⟩) (cuspTailRestriction N W s Y hY f)) =
      fun f => cuspRestriction N s (upperRectangle 0 W Y H)
        (upperRectangle_compact 0 W Y H (by linarith)) f := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (by fun_prop) (by fun_prop)
    funext g
    dsimp only [Function.comp_apply]
    apply Lp.ext
    have hac : volume.restrict (upperRectangle 0 W Y H) ≪
        volume.restrict (cuspTailSet W Y) :=
      (Measure.restrict_mono_set volume
        (show upperRectangle 0 W Y H ⊆ cuspTailSet W Y from
          fun _ hz => ⟨hz.1,hz.2.1⟩)).absolutelyContinuous
    have ht := hac.ae_eq (cuspTailRestriction_representative_ae N W s Y hY g)
    filter_upwards [localRestrictionMap_ae (upperRectangle 0 W Y H) (cuspTailSet W Y)
      (fun _ hz => ⟨hz.1,hz.2.1⟩) (cuspTailRestriction N W s Y hY
        (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) g)),ht,
      cuspRestriction_representative_ae N s (upperRectangle 0 W Y H)
        (upperRectangle_compact 0 W Y H (by linarith)) g] with z hr ht' hc
    exact (hr.trans ht').trans hc.symm
  exact congrFun he f

theorem cuspTailRestriction_coherence_ae (N W : ℕ) (s : SL(2,ℤ))
    (Y H : ℝ) (hY : 2 ≤ Y) (f : AutomorphicSpace N) :
    (cuspRestriction N s (upperRectangle 0 W Y H)
      (upperRectangle_compact 0 W Y H (by linarith)) f : ℍ → ℂ)
      =ᵐ[volume.restrict (upperRectangle 0 W Y H)] cuspTailRestriction N W s Y hY f := by
  rw [← cuspTailRestriction_coherence N W s Y H hY f]
  exact localRestrictionMap_ae _ _ _ _

theorem lp_norm_square_lintegral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (f : Lp ℂ 2 μ) : ENNReal.ofReal (‖f‖^2) = ∫⁻ z, ENNReal.ofReal (‖f z‖^2) ∂μ := by
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  exact ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))

/-- Uniform infinite-tail estimate on the full cuspidal energy-form domain.
No pointwise representative or smooth cuspidal approximation is assumed. -/
theorem cuspidal_form_tail_norm_le (N : ℕ) (hN : 0 < N) (s : SL(2,ℤ))
    (Y : ℝ) (hY : 2 ≤ Y) (u : QuotientEnergySpace N)
    (hu : energyInclusion N u ∈ localCuspidalSpace N hN) :
    ‖cuspTailRestriction N N s Y hY (energyInclusion N u)‖^2 ≤
      (2*(N:ℝ)^2/Y^2)*(N+1)*(quotientClosedEnergy N u u).re := by
  have hq := quotientClosedEnergy_nonnegative N u
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hq)).mp
  rw [lp_norm_square_lintegral]
  apply tail_lintegral_le_of_bands
  intro H hH
  have hc := cuspTailRestriction_coherence_ae N N s Y H hY (energyInclusion N u)
  have he : (∫⁻ z in upperRectangle 0 N Y H,
      ENNReal.ofReal (‖cuspTailRestriction N N s Y hY (energyInclusion N u) z‖^2)) =
      ENNReal.ofReal (‖cuspRestriction N s (upperRectangle 0 N Y H)
        (upperRectangle_compact 0 N Y H (by linarith)) (energyInclusion N u)‖^2) := by
    rw [lp_norm_square_lintegral]
    apply lintegral_congr_ae
    filter_upwards [hc] with z hz
    rw [hz]
  rw [he]
  exact ENNReal.ofReal_le_ofReal (cuspidal_form_band_norm_le N hN s Y H hY hH u hu)

#print axioms cuspTailRestriction_coherence
#print axioms cuspTailRestriction_coherence_ae
#print axioms lp_norm_square_lintegral
#print axioms cuspidal_form_tail_norm_le
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped Topology MatrixGroups ENNReal Pointwise Modular
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass QuantitativeSpectralObservability

/-- Two integral charts per congruence coset cover the two halves of the
standard modular cusp; no classification of cusp widths is needed. -/
def globalCuspChart (N : ℕ) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    (b : Bool) : SL(2,ℤ) :=
  if b then q.out⁻¹ * (upperSL (N:ℤ))⁻¹ else q.out⁻¹

def globalCuspTail (N : ℕ) (Y : ℝ) : Set ℍ :=
  ⋃ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ⋃ b : Bool,
    cuspAction (globalCuspChart N q b) '' cuspTailSet N Y

theorem cuspTailSet_measurable (W : ℕ) (Y : ℝ) : MeasurableSet (cuspTailSet W Y) := by
  exact ((measurableSet_Icc.preimage continuous_re.measurable).inter
    (measurableSet_Ici.preimage continuous_im.measurable))

theorem globalCuspTail_measurable (N : ℕ) (hN : 0 < N) (Y : ℝ) : MeasurableSet (globalCuspTail N Y) := by
  let : NeZero N := ⟨hN.ne'⟩
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro b
  change MeasurableSet ((SpecialLinearGroup.mapGL ℝ (globalCuspChart N q b)) • cuspTailSet N Y)
  rw [← preimage_smul_inv]
  exact (cuspTailSet_measurable N Y).preimage (continuous_const_smul _).measurable

/-- The actual fundamental set is covered by a compact core and finitely
many of the infinite cusp strips on which the form estimate is proved. -/
theorem fundamentalSet_subset_core_cusps (N : ℕ) (hN : 0 < N) (Y : ℝ) :
    fundamentalSet N ⊆ wideCompactCover N Y ∪ globalCuspTail N Y := by
  intro z hz
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  by_cases hy : w.im ≤ Y
  · left
    apply fundamentalCompact_subset_wide
    exact mem_iUnion.mpr ⟨q,w,⟨hw,hy⟩,rfl⟩
  · right
    have hYw : Y ≤ w.im := (lt_of_not_ge hy).le
    have hNreal : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hr := abs_le.mp hw.2
    apply mem_iUnion.mpr
    refine ⟨q,?_⟩
    by_cases hx : 0 ≤ w.re
    · apply mem_iUnion.mpr
      refine ⟨false,w,⟨⟨hx,by linarith⟩,hYw⟩,?_⟩
      change q.out⁻¹ • w = (integralLabel q.out)⁻¹ • w
      rw [← integralLabel_action,map_inv]
    · let v := integralLabel (upperSL (N:ℤ)) • w
      have hvre : v.re = w.re + N := by
        dsimp only [v]
        rw [upper_label,translation_re,Int.cast_natCast]
      have hvim : v.im = w.im := by
        dsimp only [v]
        rw [upper_label]
        exact AsymptoticCompactTranslation.label_im (N:ℚ) w
      apply mem_iUnion.mpr
      refine ⟨true,v,⟨⟨?_,?_⟩,?_⟩,?_⟩
      · rw [hvre]; linarith
      · rw [hvre]; linarith
      · rw [hvim]; exact hYw
      · change (q.out⁻¹ * (upperSL (N:ℤ))⁻¹) • v = (integralLabel q.out)⁻¹ • w
        rw [← integralLabel_action,map_mul,map_inv,map_inv,mul_smul]
        exact congrArg ((integralLabel q.out)⁻¹ • ·) (inv_smul_smul _ w)

theorem core_cusps_orbit_cover (N : ℕ) (hN : 0 < N) (Y : ℝ) (z : ℍ) :
    ∃ g : gamma N, g.val • z ∈ wideCompactCover N Y ∪ globalCuspTail N Y := by
  obtain ⟨g,hg⟩ := fundamentalSet_orbit_meets N z
  exact ⟨g,fundamentalSet_subset_core_cusps N hN Y hg⟩

/-- Genuine quotient mass is bounded by compact hyperbolic mass plus the
finite family of cusp-tail masses. No identification of measures is made. -/
theorem quotient_mass_le_core_cusps (N : ℕ) (hN : 0 < N) (Y : ℝ)
    (F : ℍ → ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, F (g.val • z) = F z) :
    (∫⁻ z, F z ∂quotientMeasure N) ≤ (∫⁻ z in wideCompactCover N Y, F z) +
      ∑' q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ∑' b : Bool,
        ∫⁻ z in cuspTailSet N Y, F (cuspAction (globalCuspChart N q b) z) := by
  let : NeZero N := ⟨hN.ne'⟩
  have hc := quotient_lintegral_le_cover N F hF hinv
    (wideCompactCover N Y ∪ globalCuspTail N Y)
    ((wideCompactCover_compact N hN Y).measurableSet.union (globalCuspTail_measurable N hN Y))
    (core_cusps_orbit_cover N hN Y)
  apply hc.trans
  apply (lintegral_union_le _ _ _).trans
  apply add_le_add le_rfl
  apply (lintegral_iUnion_le _ F).trans
  apply ENNReal.tsum_le_tsum
  intro q
  apply (lintegral_iUnion_le _ F).trans
  apply ENNReal.tsum_le_tsum
  intro b
  have hp : MeasurePreserving (cuspAction (globalCuspChart N q b)) volume volume :=
    measurePreserving_smul (SpecialLinearGroup.mapGL ℝ (globalCuspChart N q b)) (volume : Measure ℍ)
  exact le_of_eq (hp.setLIntegral_comp_emb
    (measurableEmbedding_const_smul (SpecialLinearGroup.mapGL ℝ (globalCuspChart N q b)))
    F (cuspTailSet N Y)).symm

#print axioms fundamentalSet_subset_core_cusps
#print axioms core_cusps_orbit_cover
#print axioms quotient_mass_le_core_cusps
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups ENNReal
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass QuantitativeSpectralObservability

/-- The geometric cover controls the norm on the full Hilbert completion.
All restriction operators use raw hyperbolic measure, not quotient measure. -/
theorem quotient_norm_le_core_cusps (N : ℕ) (hN : 0 < N) (Y : ℝ) (hY : 2 ≤ Y)
    (f : AutomorphicSpace N) :
    ‖f‖^2 ≤ ‖quotientRestriction N (wideCompactCover N Y)
      (wideCompactCover_compact N hN Y) (wideCompactCover_compact N hN Y).measurableSet f‖^2 +
      ∑' q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ∑' b : Bool,
        ‖cuspTailRestriction N N (globalCuspChart N q b) Y hY f‖^2 := by
  let : NeZero N := ⟨hN.ne'⟩
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Fintype.ofFinite _
  let A := quotientRestriction N (wideCompactCover N Y)
    (wideCompactCover_compact N hN Y) (wideCompactCover_compact N hN Y).measurableSet
  let B := fun q b => cuspTailRestriction N N (globalCuspChart N q b) Y hY
  have hclosed : IsClosed {v : AutomorphicSpace N |
      ‖v‖^2 ≤ ‖A v‖^2 + ∑ q, ∑ b : Bool, ‖B q b v‖^2} := by
    apply isClosed_le <;> fun_prop
  have hsub : Set.range (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N)) ⊆
      {v : AutomorphicSpace N | ‖v‖^2 ≤ ‖A v‖^2 + ∑ q, ∑ b : Bool, ‖B q b v‖^2} := by
    rintro _ ⟨g,rfl⟩
    let v := AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) g
    have hv : ENNReal.ofReal (‖v‖^2) = ∫⁻ z, ENNReal.ofReal (‖g.val z‖^2) ∂quotientMeasure N := by
      change ENNReal.ofReal (‖v.val‖^2) = _
      rw [lp_norm_square_lintegral]
      apply lintegral_congr_ae
      filter_upwards [g.property.2.2.coeFn_toLp] with z hz
      exact congrArg (fun t : ℂ => ENNReal.ofReal (‖t‖^2)) hz
    have ha : ENNReal.ofReal (‖A v‖^2) =
        ∫⁻ z in wideCompactCover N Y, ENNReal.ofReal (‖g.val z‖^2) := by
      rw [lp_norm_square_lintegral]
      apply lintegral_congr_ae
      filter_upwards [quotientRestriction_representative_ae N (wideCompactCover N Y)
        (wideCompactCover_compact N hN Y) (wideCompactCover_compact N hN Y).measurableSet g] with z hz
      exact congrArg (fun t : ℂ => ENNReal.ofReal (‖t‖^2)) hz
    have hb (q) (b) : ENNReal.ofReal (‖B q b v‖^2) =
        ∫⁻ z in cuspTailSet N Y, ENNReal.ofReal (‖g.val (cuspAction (globalCuspChart N q b) z)‖^2) := by
      rw [lp_norm_square_lintegral]
      apply lintegral_congr_ae
      filter_upwards [cuspTailRestriction_representative_ae N N (globalCuspChart N q b) Y hY g] with z hz
      exact congrArg (fun t : ℂ => ENNReal.ofReal (‖t‖^2)) hz
    have hc := quotient_mass_le_core_cusps N hN Y (fun z => ENNReal.ofReal (‖g.val z‖^2))
      (g.property.1.norm.pow_const 2).ennreal_ofReal
      (fun a z => by rw [g.property.2.1 a z])
    change ‖v‖^2 ≤ ‖A v‖^2 + ∑ q, ∑ b : Bool, ‖B q b v‖^2
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [ENNReal.ofReal_add (sq_nonneg _) (by positivity)]
    rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))]
    simp only [ENNReal.ofReal_sum_of_nonneg (fun b _ => sq_nonneg _)]
    simpa only [tsum_fintype, ← hv, ← ha, ← hb] using hc
  have hall := closure_minimal hsub hclosed
    (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N) f)
  simpa only [Set.mem_ofPred_eq,tsum_fintype,A,B] using hall

#print axioms quotient_norm_le_core_cusps
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups ENNReal
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass QuantitativeSpectralObservability

/-- Compact mass plus an explicit O_N(Y⁻²) energy tail controls the entire
cuspidal vector. The estimate holds on the full closed form domain. -/
theorem cuspidal_norm_le_core_energy (N : ℕ) (hN : 0 < N) (Y : ℝ) (hY : 2 ≤ Y)
    (u : QuotientEnergySpace N) (hu : energyInclusion N u ∈ localCuspidalSpace N hN) :
    ‖energyInclusion N u‖^2 ≤ ‖quotientRestriction N (wideCompactCover N Y)
      (wideCompactCover_compact N hN Y) (wideCompactCover_compact N hN Y).measurableSet
      (energyInclusion N u)‖^2 +
      (4 * (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : ℝ) * N^2 * (N+1) / Y^2) *
        (quotientClosedEnergy N u u).re := by
  let : NeZero N := ⟨hN.ne'⟩
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Fintype.ofFinite _
  apply (quotient_norm_le_core_cusps N hN Y hY (energyInclusion N u)).trans
  apply add_le_add le_rfl
  simp only [tsum_fintype]
  calc
    _ ≤ ∑ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ∑ b : Bool,
        (2*(N:ℝ)^2/Y^2)*(N+1)*(quotientClosedEnergy N u u).re := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      intro b _
      exact cuspidal_form_tail_norm_le N hN (globalCuspChart N q b) Y hY u hu
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul,
        Nat.card_eq_fintype_card]
      ring

/-- A compact core sees at least half the norm of every cuspidal vector
whose form energy is bounded by E times its norm squared. -/
theorem cuspidal_bounded_energy_core (N : ℕ) (hN : 0 < N)
    (E Y : ℝ) (hY : 2 ≤ Y)
    (hsize : 8 * (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : ℝ) * N^2 * (N+1) * E ≤ Y^2)
    (u : QuotientEnergySpace N) (hu : energyInclusion N u ∈ localCuspidalSpace N hN)
    (henergy : (quotientClosedEnergy N u u).re ≤ E*‖energyInclusion N u‖^2) :
    ‖energyInclusion N u‖^2 ≤ 2*‖quotientRestriction N (wideCompactCover N Y)
      (wideCompactCover_compact N hN Y) (wideCompactCover_compact N hN Y).measurableSet
      (energyInclusion N u)‖^2 := by
  have h := cuspidal_norm_le_core_energy N hN Y hY u hu
  let C : ℝ := 4 * (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : ℝ) * N^2 * (N+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hYsq : 0 < Y^2 := by positivity
  have hc : C/Y^2*E ≤ 1/2 := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hYsq]
    dsimp [C]
    nlinarith [hsize]
  have hb := mul_le_mul_of_nonneg_left henergy (div_nonneg hC hYsq.le)
  have hd := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖energyInclusion N u‖)
  change ‖energyInclusion N u‖^2 ≤ _ + C/Y^2*(quotientClosedEnergy N u u).re at h
  nlinarith

#print axioms cuspidal_norm_le_core_energy
#print axioms cuspidal_bounded_energy_core
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups ENNReal ContDiff
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass

/-- Compact restriction of a radial output is its literal integral output
in raw hyperbolic measure. Quotient almost-everywhere equality alone would
not justify this assertion. -/
theorem radialKernel_compact_restriction_ae (N : ℕ) [NeZero N]
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support g ⊆ Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (f : AutomorphicSpace N) :
    (quotientRestriction N K hK hK.measurableSet (radialKernelOperator N g hg R hR hs f) : ℍ → ℂ)
      =ᵐ[volume.restrict K] (radialKernelData N g hg R hR hs).output f.val := by
  let D := radialKernelData N g hg R hR hs
  have hm : D.output f.val ∈ AutomorphicL2.representatives (gamma N) (quotientMeasure N) := by
    refine ⟨D.output_measurable f.val (Lp.stronglyMeasurable f.val).measurable,?_,
      D.output_memLp f.val (Lp.stronglyMeasurable f.val).measurable (Lp.memLp f.val)⟩
    intro a z
    exact radialKernel_output_invariant N g hg R hR hs f.val a z
  let v : AutomorphicL2.representatives (gamma N) (quotientMeasure N) := ⟨D.output f.val,hm⟩
  have he : AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) v =
      radialKernelOperator N g hg R hR hs f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hm.2.2.coeFn_toLp,D.operator_coeFn f.val] with z hz hz'
    exact hz.trans hz'.symm
  rw [← he]
  exact quotientRestriction_representative_ae N K hK hK.measurableSet v

/-- Bessel's inequality for the RAW compact restriction operator. It holds
for arbitrary orthonormal families without assuming spectral discreteness. -/
theorem radialKernel_raw_compact_bessel {ι : Type*} (N : ℕ) [NeZero N]
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hr : ∀ q, star (g q) = g q)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support g ⊆ Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) :
    (∑' i, ENNReal.ofReal (‖quotientRestriction N K hK hK.measurableSet
      (radialKernelOperator N g hg R hR hs (v i))‖^2)) ≤
      ∫⁻ x in K, ∫⁻ y, ENNReal.ofReal (‖radialPoincareKernel N g x y‖^2) ∂quotientMeasure N := by
  classical
  let D := radialKernelData N g hg R hR hs
  have he (i : ι) : ENNReal.ofReal (‖quotientRestriction N K hK hK.measurableSet
      (radialKernelOperator N g hg R hR hs (v i))‖^2) =
      ∫⁻ x in K, ENNReal.ofReal (‖D.output (v i).val x‖^2) := by
    rw [lp_norm_square_lintegral]
    apply lintegral_congr_ae
    filter_upwards [radialKernel_compact_restriction_ae N g hg R hR hs K hK (v i)] with x hx
    exact congrArg (fun t : ℂ => ENNReal.ofReal (‖t‖^2)) hx
  simp_rw [he]
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  have hm (i : ι) : Measurable (fun x => ENNReal.ofReal (‖D.output (v i).val x‖^2)) :=
    ((D.output_measurable (v i).val (Lp.stronglyMeasurable (v i).val).measurable).norm.pow_const 2).ennreal_ofReal
  rw [← lintegral_finsetSum (μ := volume.restrict K) s (fun i _ => hm i)]
  apply lintegral_mono
  intro x
  change (∑ i ∈ s, ENNReal.ofReal (‖D.output (v i).val x‖^2)) ≤
    ∫⁻ y, ENNReal.ofReal (‖radialPoincareKernel N g x y‖^2) ∂quotientMeasure N
  rw [← radialKernel_row_lintegral N g hg R hR hs x]
  calc
    _ = ENNReal.ofReal (∑ i ∈ s, ‖D.output (v i).val x‖^2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (radialKernel_output_bessel N v hv s g hg hr R hR hs x)


/-- The raw compact squared-kernel energy is finite; this is distinct from
integrating the same kernel against the quotient measure in both variables. -/
theorem radialKernel_raw_compact_energy_finite (N : ℕ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support g ⊆ Iic (Real.cosh R)) (K : Set ℍ) (hK : IsCompact K) :
    (∫⁻ x in K, ∫⁻ y, ENNReal.ofReal (‖radialPoincareKernel N g x y‖^2) ∂quotientMeasure N) < (∞ : ℝ≥0∞) := by
  obtain ⟨L,hL⟩ := hK.isBounded.subset_closedBall (default : ℍ)
  obtain ⟨M,hM⟩ := radialKernel_compact_energy_bound N (default : ℍ) L R hR
  have hb : (∫⁻ x in K, ∫⁻ y, ENNReal.ofReal (‖radialPoincareKernel N g x y‖^2) ∂quotientMeasure N) ≤
      ((M:ℝ≥0∞)*ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2))*volume K := by
    calc
      _ ≤ ∫⁻ _x in K, (M:ℝ≥0∞)*ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2) := by
        apply setLIntegral_mono' hK.measurableSet
        intro x hx
        rw [← radialKernel_row_lintegral N g hg R hR hs x,← radialKernel_row_energy N g hg R hR hs x]
        exact hM g hg hs x (hL hx)
      _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]
  exact hb.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top) hK.measure_lt_top)

#print axioms radialKernel_compact_restriction_ae
#print axioms radialKernel_raw_compact_bessel
#print axioms radialKernel_raw_compact_energy_finite
end QuantitativeArithmeticMaassCuspBand
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups ENNReal ContDiff
namespace QuantitativeArithmeticMaassCuspBand
open QuantitativeMaass QuantitativeSpectralObservability

/-- Only finitely many orthonormal vectors have a fixed positive amount
of radial-packet mass on a raw compact set. -/
theorem radialKernel_finite_raw_threshold {ι : Type*} (N : ℕ) [NeZero N]
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hr : ∀ q, star (g q) = g q)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support g ⊆ Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    {i | ε ≤ ENNReal.ofReal (‖quotientRestriction N K hK hK.measurableSet
      (radialKernelOperator N g hg R hR hs (v i))‖^2)}.Finite := by
  apply ENNReal.finite_const_le_of_tsum_ne_top _ hε
  exact ((radialKernel_raw_compact_bessel N v hv g hg hr R hR hs K hK).trans_lt
    (radialKernel_raw_compact_energy_finite N g hg R hR hs K hK)).ne

/-- Bounded-energy cuspidal packet eigenvectors form a finite orthonormal
family whenever their packet eigenvalues are uniformly separated from zero.
The compact mass hypothesis is derived, not assumed. A spectral-window
application must still choose a test with the stated scalar lower bound. -/
theorem cuspidal_packet_family_finite {ι : Type*} (N : ℕ) (hN : 0 < N)
    (u : ι → QuotientEnergySpace N)
    (hv : Orthonormal ℂ (fun i => energyInclusion N (u i)))
    (hu : ∀ i, energyInclusion N (u i) ∈ localCuspidalSpace N hN)
    (E Y : ℝ) (hY : 2 ≤ Y)
    (hsize : 8 * (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : ℝ) * N^2 * (N+1) * E ≤ Y^2)
    (henergy : ∀ i, (quotientClosedEnergy N (u i) (u i)).re ≤ E*‖energyInclusion N (u i)‖^2)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hr : ∀ q, star (g q) = g q)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support g ⊆ Iic (Real.cosh R))
    (eigenvalue : ι → ℂ) (b : ℝ) (hb : 0 < b)
    (heigenvalue : ∀ i, b ≤ ‖eigenvalue i‖)
    (hpacket : letI : NeZero N := ⟨hN.ne'⟩; ∀ i,
      radialKernelOperator N g hg R hR hs (energyInclusion N (u i)) =
        eigenvalue i • energyInclusion N (u i)) : (Set.univ : Set ι).Finite := by
  let : NeZero N := ⟨hN.ne'⟩
  let K := wideCompactCover N Y
  have hK := wideCompactCover_compact N hN Y
  let A := quotientRestriction N K hK hK.measurableSet
  have hf := radialKernel_finite_raw_threshold N (fun i => energyInclusion N (u i)) hv
    g hg hr R hR hs K hK (ENNReal.ofReal (b^2/2)) (by positivity)
  apply hf.subset
  intro i _
  change ENNReal.ofReal (b^2/2) ≤ ENNReal.ofReal (‖A (radialKernelOperator N g hg R hR hs
    (energyInclusion N (u i)))‖^2)
  apply ENNReal.ofReal_le_ofReal
  rw [hpacket i,map_smul,norm_smul,mul_pow]
  have hc := cuspidal_bounded_energy_core N hN E Y hY hsize (u i) (hu i) (henergy i)
  have hn : ‖energyInclusion N (u i)‖ = 1 := hv.norm_eq_one i
  rw [hn,one_pow] at hc
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg ‖eigenvalue i‖)
  have hl : b^2 ≤ ‖eigenvalue i‖^2 := by nlinarith [heigenvalue i,norm_nonneg (eigenvalue i)]
  change 1 ≤ 2*‖A (energyInclusion N (u i))‖^2 at hc
  change ‖eigenvalue i‖^2*1 ≤ ‖eigenvalue i‖^2*(2*‖A (energyInclusion N (u i))‖^2) at hm
  nlinarith

#print axioms radialKernel_finite_raw_threshold
#print axioms cuspidal_packet_family_finite
end QuantitativeArithmeticMaassCuspBand
end
