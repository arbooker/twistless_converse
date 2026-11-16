module

public import QuantitativeMaassPoincareGradientOverlapV1
public import QuantitativeMaassPoincareCoordinateBoundV1
public import QuantitativeArithmeticMaassOverlapTheoryV4

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassOverlap
open scoped ENNReal

namespace QuantitativeMaass
open MaassDifferential

/-- The L2 norm of a compact Poincare seed retains the prescribed
multiplicity, with no existential compact-dependent replacement. -/
theorem poincareSeedVector_norm_sq_le_of_overlap (N : ℕ)
    (K : Set ℍ) (hK : IsCompact K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m)
    (u : SmoothUpperSeed) (hu : tsupport (upperFunction u.toFun) ⊆ K) :
    ‖poincareSeedVector N u‖^2 ≤
      (m : ℝ) * ∫ z : ℍ, ‖upperFunction u.toFun z‖^2 := by
  have hL : MemLp (upperFunction u.toFun) 2 volume :=
    (upperFunction_continuous u.smooth).memLp_of_hasCompactSupport u.compact
  have hb := compact_poincare_energy_bound_of_overlap volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N) K hK m hm
    (upperFunction u.toFun) (upperFunction_continuous u.smooth).measurable
    ((subset_tsupport _).trans hu)
  change (∫⁻ z, ENNReal.ofReal (‖poincareSum (G := gamma N) (upperFunction u.toFun) z‖^2)
    ∂quotientMeasure N) ≤ (m : ℝ≥0∞) * ∫⁻ z : ℍ, ENNReal.ofReal (‖upperFunction u.toFun z‖^2) at hb
  have hf : (∫⁻ z : ℍ, ENNReal.ofReal (‖upperFunction u.toFun z‖^2)) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hL.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
      (Filter.Eventually.of_forall (fun z => sq_nonneg ‖upperFunction u.toFun z‖))]
    exact ENNReal.ofReal_ne_top
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hf) hb
  rw [square_energy_toReal _ (poincareSeed_representative N u).2.2,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, square_energy_toReal _ hL,
    complex_toLp_norm_sq (upperFunction u.toFun) hL] at ht
  exact ht

/-- Full form-core energy of periodization is bounded by the same
explicit overlap constant times the ambient mass plus gradient energy. -/
theorem poincareEnergySeed_norm_sq_le_of_overlap (N : ℕ)
    (K : Set ℍ) (hK : IsCompact K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m)
    (u : SmoothUpperSeed) (hu : tsupport (upperFunction u.toFun) ⊆ K) :
    ‖poincareEnergySeed N u‖^2 ≤ (m : ℝ) *
      ((∫ z : ℍ, ‖upperFunction u.toFun z‖^2) +
       ∫ z : ℍ, (upperEnergy u.toFun u.toFun z).re) := by
  rw [poincareEnergySeed_mass_gradient, mul_add]
  exact add_le_add (poincareSeedVector_norm_sq_le_of_overlap N K hK m hm u hu)
    (compact_poincare_gradient_integral_bound_of_overlap N K hK m hm u hu)

#print axioms poincareSeedVector_norm_sq_le_of_overlap
#print axioms poincareEnergySeed_norm_sq_le_of_overlap

end QuantitativeMaass
