module

public import QuantitativeEulerOldProjectionRepeatedV1
public import QuantitativeMaassCosetTraceNormV1
public import QuantitativeMaassTraceAdjointV1
public import AsymptoticClassicalPeterssonMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionPhysical

open MeasureTheory
open scoped ENNReal

section General
variable {G α : Type*} [Group G] [MulAction G α]
    (H : Subgroup G) [H.FiniteIndex] (σ : α → ℝ≥0∞)

/-- A normalized density on a finite-index subgroup, divided by the
literal index, is a normalized density on the larger group. -/
def extensionDensity (x : α) : ℝ≥0∞ := (H.index : ℝ≥0∞)⁻¹ * σ x

theorem extensionDensity_normalized (hσ : ∀ x, ∑' h : H, σ (h.val • x) = 1) (x : α) :
    ∑' g : G, extensionDensity H σ (g • x) = 1 := by
  simp only [extensionDensity]
  rw [ENNReal.tsum_mul_left,
    AsymptoticOrbitDensity.subgroup_mass_eq_index H σ hσ]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast H.index_ne_zero_of_finite) (by simp)

variable [MeasurableSpace α]

omit [MulAction G α] [H.FiniteIndex] in
theorem extensionDensity_measurable (hσ : Measurable σ) : Measurable (extensionDensity H σ) :=
  measurable_const.mul hσ
end General

open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeNewGap

variable (L : ℕ) (hL : 0 < L)

/-- A concrete quotient density for the actual repeated join; no
fundamental-domain existence or normalization hypothesis is assumed. -/
def repeatedJoinDensity (z : UpperHalfPlane) : ℝ≥0∞ :=
  ((if 2 ∣ L then 4 else 6 : ℕ) : ℝ≥0∞)⁻¹ * density (2*(2*L)) z

theorem repeatedJoinDensity_measurable : Measurable (repeatedJoinDensity L) :=
  measurable_const.mul (density_measurable _)

include hL in
theorem repeatedJoinDensity_normalized (z : UpperHalfPlane) :
    ∑' g : repeatedJoin L, repeatedJoinDensity L (g.val • z) = 1 := by
  let : (repeatedBase L).FiniteIndex := repeatedBaseFiniteIndex L hL
  have hn : ∀ x, ∑' h : repeatedBase L, density (2*(2*L)) (h.val.val • x) = 1 := by
    intro x
    exact QuantitativeMaass.AutomorphicL2.subgroupDensityNormalized
      (gamma (2*(2*L))) (repeatedJoin L)
      ((QuantitativeEulerOldProjectionBlock.repeatedAmbient_le_old₀ L).trans
        (QuantitativeEulerOldProjectionBlock.repeatedOld_le_join₀ L))
      (density (2*(2*L))) (density_orbit_sum _) x
  have he := extensionDensity_normalized (repeatedBase L) (density (2*(2*L))) hn z
  change (∑' g : repeatedJoin L, ((repeatedBase L).index : ℝ≥0∞)⁻¹ *
    density (2*(2*L)) (g.val • z)) = 1 at he
  simpa only [repeatedJoinDensity, repeatedBase_index L hL] using he

#print axioms extensionDensity_normalized
#print axioms repeatedJoinDensity_normalized
end QuantitativeEulerOldProjectionPhysical
