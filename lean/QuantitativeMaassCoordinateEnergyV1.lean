module

public import QuantitativeMaassEnergyLocalizationV1
public import QuantitativeMaassHyperbolicIntegralV1
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane Filter
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- The real-valued form of the actual hyperbolic coordinate integration rule. -/
theorem integral_upper_cartesian_real (F : Point → ℝ) :
    (∫ z : ℍ,F (z.re,z.im))=∫ Z in {Z : Point | 0<Z.2},F Z/Z.2^2 := by
  have h := integral_upper_cartesian (fun Z => (F Z:ℂ))
  simp only [upperFunction,←Complex.ofReal_pow,←Complex.ofReal_div,integral_complex_ofReal] at h
  exact_mod_cast h

/-- The height factor in gradient energy cancels the hyperbolic volume density. -/
theorem upperEnergy_integral_coordinates (u : Point → ℂ)
    (hp : tsupport u⊆{Z : Point | 0<Z.2}) :
    (∫ z : ℍ,(upperEnergy u u z).re)=∫ Z,‖X u Z‖^2+‖Y u Z‖^2 := by
  have hz (Z : Point) (hZ : ¬0<Z.2) : X u Z=0 ∧ Y u Z=0 := by
    have hd := fderiv_of_notMem_tsupport ℝ (show Z∉tsupport u from fun h => hZ (hp h))
    simp only [X,Y,dir,D,hd,zero_apply,and_self]
  have he : (fun z : ℍ => (upperEnergy u u z).re)=
      (fun z : ℍ => z.im^2*(‖X u (z.re,z.im)‖^2+‖Y u (z.re,z.im)‖^2)) :=
    funext (fun z => hyperbolicEnergy_self_eq u (z.re,z.im))
  rw [he,integral_upper_cartesian_real (fun Z : Point => Z.2^2*(‖X u Z‖^2+‖Y u Z‖^2))]
  calc
    _ = ∫ Z in {Z : Point | 0<Z.2},‖X u Z‖^2+‖Y u Z‖^2 := by
      apply setIntegral_congr_fun (isOpen_lt continuous_const continuous_snd).measurableSet
      intro Z hZ
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 (ne_of_gt hZ))
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro Z hZ
      simp only [(hz Z hZ).1,(hz Z hZ).2,norm_zero,zero_pow (by decide : 2≠0),add_zero]

/-- The two coordinate columns are bounded by twice the squared operator norm. -/
theorem coordinate_gradient_square_le (u : Point → ℂ) (Z : Point) :
    ‖X u Z‖^2+‖Y u Z‖^2≤2*‖fderiv ℝ u Z‖^2 := by
  have hx : ‖X u Z‖≤‖fderiv ℝ u Z‖ := by
    simpa [X,dir,D,e₁,Prod.norm_def] using (fderiv ℝ u Z).le_opNorm e₁
  have hy : ‖Y u Z‖≤‖fderiv ℝ u Z‖ := by
    simpa [Y,dir,D,e₂,Prod.norm_def] using (fderiv ℝ u Z).le_opNorm e₂
  have hx2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hy2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  linarith

/-- Euclidean derivative energy controls the actual hyperbolic seed energy. -/
theorem upperEnergy_integral_le_fderiv (u : Point → ℂ)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hp : tsupport u⊆{Z : Point | 0<Z.2}) :
    (∫ z : ℍ,(upperEnergy u u z).re)≤2*∫ Z,‖fderiv ℝ u Z‖^2 := by
  rw [upperEnergy_integral_coordinates u hp,←integral_const_mul]
  have hd : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hi : Integrable (fun Z => ‖fderiv ℝ u Z‖^2) := by
    apply (hd.norm.pow 2).integrable_of_hasCompactSupport
    apply (hc.fderiv ℝ).mono
    intro Z hZ hz
    apply hZ
    simp [hz]
  exact integral_mono_of_nonneg (Eventually.of_forall (fun Z => add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (hi.const_mul 2) (Eventually.of_forall (coordinate_gradient_square_le u))

#print axioms integral_upper_cartesian_real
#print axioms upperEnergy_integral_coordinates
#print axioms coordinate_gradient_square_le
#print axioms upperEnergy_integral_le_fderiv

/-- Above a fixed positive support height, Euclidean mass controls hyperbolic mass. -/
theorem upper_mass_integral_le_cartesian (u : Point → ℂ)
    (hu : Continuous u) (hc : HasCompactSupport u) {r : ℝ} (hr : 0<r)
    (hs : ∀ Z∈Function.support u,r≤Z.2) :
    (∫ z : ℍ,‖u (z.re,z.im)‖^2)≤(r^2)⁻¹*∫ Z,‖u Z‖^2 := by
  rw [integral_upper_cartesian_real (fun Z : Point => ‖u Z‖^2),←integral_const_mul]
  have hi : Integrable (fun Z => ‖u Z‖^2) := by
    apply (hu.norm.pow 2).integrable_of_hasCompactSupport
    apply hc.mono
    intro Z hZ hz
    apply hZ
    simp [hz]
  have hbound (Z : Point) : ‖u Z‖^2/Z.2^2≤(r^2)⁻¹*‖u Z‖^2 := by
    by_cases hz : u Z=0
    · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),zero_div,mul_zero,le_refl]
    · have hrZ := hs Z hz
      have hrZ2 : r^2≤Z.2^2 := pow_le_pow_left₀ hr.le hrZ 2
      have hh := div_le_div_of_nonneg_left (sq_nonneg ‖u Z‖) (sq_pos_of_pos hr) hrZ2
      simpa only [div_eq_mul_inv,mul_comm] using hh
  calc
    _ ≤ ∫ Z in {Z : Point | 0<Z.2},(r^2)⁻¹*‖u Z‖^2 :=
      integral_mono_of_nonneg
        (Eventually.of_forall (fun Z => div_nonneg (sq_nonneg _) (sq_nonneg _)))
        (hi.const_mul _).integrableOn (Eventually.of_forall hbound)
    _ ≤ _ := setIntegral_le_integral (hi.const_mul _)
      (Eventually.of_forall (fun Z => mul_nonneg (inv_nonneg.mpr (sq_nonneg r)) (sq_nonneg _)))

#print axioms upper_mass_integral_le_cartesian

end QuantitativeMaass
