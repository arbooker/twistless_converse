module

public import QuantitativeMaassPoincareGradientIntegralV1
public import QuantitativeMaassCoordinateEnergyV1
public import QuantitativeMaassLocalizationIntegralV1
public import QuantitativeMaassPoincareNormBoundV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem poincareEnergySeed_mass_gradient (N : ℕ) (u : SmoothUpperSeed) :
    ‖poincareEnergySeed N u‖^2=‖poincareSeedVector N u‖^2+
      ∫ z,(upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N u.toFun) z).re ∂quotientMeasure N := by
  rw [poincareEnergySeed_norm_sq_integral,poincareSeedVector_norm_sq_integral]
  exact integral_add
    ((poincareSeed_representative N u).2.2.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    (poincare_green_energy N u.smooth u.smooth u.compact u.compact).1.re

/-- Fixed-support periodization is bounded from the actual coordinate Sobolev
norm to the actual quotient form-core norm. -/
theorem compact_poincare_coordinate_energy_bound (N : ℕ) (K : Set ℍ) (hK : IsCompact K) :
    ∃ C : ℝ,0<C ∧ ∀ (u : SmoothUpperSeed),ContDiff ℝ ∞ u.toFun →
      HasCompactSupport u.toFun → tsupport u.toFun⊆{Z : Point | 0<Z.2} →
      tsupport (upperFunction u.toFun)⊆K →
      ‖poincareEnergySeed N u‖^2≤C*((∫ Z,‖u.toFun Z‖^2)+(∫ Z,‖fderiv ℝ u.toFun Z‖^2)) := by
  obtain ⟨r,hr,hrK⟩ := hK.exists_forall_le' continuous_im.continuousOn (fun z _ => z.im_pos)
  obtain ⟨A,hA,hAM⟩ := compact_poincare_uniform_norm_bound volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N) K hK
  obtain ⟨M,hMG⟩ := compact_poincare_gradient_integral_bound N K hK
  let C := A^2*(r^2)⁻¹+2*(M:ℝ)+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro u hu hc hp hs
  have hf := upperFunction_continuous u.smooth
  have hL : MemLp (upperFunction u.toFun) 2 volume := hf.memLp_of_hasCompactSupport u.compact
  have hb := hAM (upperFunction u.toFun) hf.measurable
    ((subset_tsupport _).trans hs) hL
  change ‖poincareSeedVector N u‖≤A*‖hL.toLp (upperFunction u.toFun)‖ at hb
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow,complex_toLp_norm_sq] at hb2
  have hmass := upper_mass_integral_le_cartesian u.toFun hu.continuous hc hr
    (fun Z hZ => by
      have hz := hp (subset_tsupport _ hZ)
      let z : ℍ := ⟨⟨Z.1,Z.2⟩,hz⟩
      exact hrK z (hs (subset_tsupport _ hZ)))
  have hg := (hMG u hs).trans (mul_le_mul_of_nonneg_left
    (upperEnergy_integral_le_fderiv u.toFun hu hc hp) (Nat.cast_nonneg M))
  have hm := hb2.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg A))
  rw [poincareEnergySeed_mass_gradient]
  apply (add_le_add hm hg).trans
  have hi1 : 0≤∫ Z,‖u.toFun Z‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hi2 : 0≤∫ Z,‖fderiv ℝ u.toFun Z‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have ha0 : 0≤A^2*(r^2)⁻¹ := mul_nonneg (sq_nonneg A) (inv_nonneg.mpr (sq_nonneg r))
  have hm0 : 0≤(M:ℝ) := Nat.cast_nonneg M
  dsimp [C]
  nlinarith [mul_nonneg ha0 hi2,mul_nonneg hm0 hi1]

#print axioms poincareEnergySeed_mass_gradient
#print axioms compact_poincare_coordinate_energy_bound

end QuantitativeMaass
