module

public import AsymptoticCongruenceCovolumeV1
public import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalPetersson

open UpperHalfPlane MeasureTheory AsymptoticCongruenceWeight
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticRegularTrace
open AsymptoticCompactBranch AsymptoticMassTransport
open scoped ENNReal

/-- A fixed orbit density with total mass one on each congruence orbit. -/
def density (N : ℕ) (z : ℍ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖amplitude N 1 1 z‖ ^ 2)

def quotientMeasure (N : ℕ) : Measure ℍ := volume.withDensity (density N)

theorem density_measurable (N : ℕ) : Measurable (density N) :=
  ((amplitude_measurable N 1 1).norm.pow_const 2).ennreal_ofReal

theorem density_orbit_sum (N : ℕ) (z : ℍ) :
    ∑' g : gamma N, density N (g.val • z) = 1 :=
  amplitude_ofReal_tsum N (by norm_num) (by norm_num) z

theorem density_integral (N : ℕ) (hN : 0 < N) :
    (∫⁻ z : ℍ, density N z) =
      ((gamma N).relIndex (gamma 1) : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 3) := by
  have he : trace volume (projection N (by norm_num : (0 : ℝ) < 1) (by norm_num : 1 ≤ (1 : ℕ))) =
      ∫⁻ z : ℍ, density N z := by
    apply lintegral_congr
    intro z
    rw [projection_diagonal, one_smul]
    congr 1
    simpa only [OneMemClass.coe_one, one_smul] using
      (amplitude_norm_sq N (by norm_num : (0 : ℝ) < 1) (by norm_num : 1 ≤ (1 : ℕ)) 1 z).symm
  exact he.symm.trans (projection_trace_covolume N hN (by norm_num) (by norm_num))

theorem quotientMeasure_univ (N : ℕ) (hN : 0 < N) :
    quotientMeasure N Set.univ =
      ((gamma N).relIndex (gamma 1) : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 3) := by
  rw [quotientMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, density_integral N hN]

instance quotientMeasure_finite (N : ℕ) [NeZero N] : IsFiniteMeasure (quotientMeasure N) := by
  apply isFiniteMeasure_withDensity
  rw [density_integral N (Nat.pos_of_ne_zero (NeZero.ne N))]
  exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top

theorem density_pos (N : ℕ) {z : ℍ} (hz : z ∈ strip) : 0 < density N z := by
  unfold density amplitude
  rw [Set.indicator_of_mem hz]
  apply ENNReal.ofReal_pos.mpr
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact sq_pos_of_pos (div_pos (cap_pos (by norm_num) 1 z)
    (Real.sqrt_pos.mpr (weight_pos N (by norm_num) (by norm_num) z)))

/-- The quotient density is positive throughout the unit strip. -/
theorem ae_strip_of_ae (N : ℕ) {P : ℍ → Prop}
    (h : ∀ᵐ z ∂quotientMeasure N, P z) :
    ∀ᵐ z : ℍ ∂volume, z ∈ strip → P z := by
  have hh := (ae_withDensity_iff (density_measurable N)).mp h
  filter_upwards [hh] with z hz hs
  exact hz (density_pos N hs).ne'

#print axioms ae_strip_of_ae

#print axioms density_orbit_sum
#print axioms density_integral
#print axioms quotientMeasure_univ
#print axioms quotientMeasure_finite
#print axioms density_pos

end AsymptoticClassicalPetersson
