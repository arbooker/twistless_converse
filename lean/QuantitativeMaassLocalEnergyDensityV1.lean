module

public import QuantitativeMaassLocalGradientRestrictionV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal

namespace QuantitativeMaass

/-- Continuity is used only for the compact local integral; invariance
of the full density was proved separately. -/
theorem poincareEnergyDensity_continuous (N : ℕ) (u : SmoothUpperSeed) :
    Continuous (poincareEnergyDensity N u) := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun g => AsymptoticRationalBranches.action_continuous g.val⟩
  exact ((poincareSum_continuous (G := gamma N) _ u.compact
      (upperFunction_continuous u.smooth)).norm.pow 2).add
    (Complex.continuous_re.comp (upperEnergy_continuous
      (congruencePoincareCartesian_smooth N u.smooth u.compact)
      (congruencePoincareCartesian_smooth N u.smooth u.compact)))

/-- Full local mass and gradient energy are bounded by the original
quotient energy norm, with the supplied geometric multiplicity. -/
theorem poincareEnergyDensity_local_integral_le (N : ℕ) (u : SmoothUpperSeed)
    (K : Set ℍ) (hK : IsCompact K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m) :
    (∫ z in K, poincareEnergyDensity N u z) ≤ (m : ℝ) * ‖poincareEnergySeed N u‖^2 := by
  have hc := poincareEnergyDensity_continuous N u
  have hi : IntegrableOn (poincareEnergyDensity N u) K volume :=
    hc.continuousOn.integrableOn_compact hK
  have hb := invariant_lintegral_restrict_le volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N) K hK.measurableSet
    (m : ℝ≥0∞) (orbit_indicator_tsum_le_of_overlap K m hm)
    (fun z => ENNReal.ofReal (poincareEnergyDensity N u z)) hc.measurable.ennreal_ofReal
    (fun g z => congrArg ENNReal.ofReal (poincareEnergyDensity_invariant N u g z))
  change (∫⁻ z, ENNReal.ofReal (poincareEnergyDensity N u z) ∂volume.restrict K) ≤
    (m : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal (poincareEnergyDensity N u z) ∂quotientMeasure N at hb
  rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (poincareEnergyDensity_nonnegative N u)),
    ← ofReal_integral_eq_lintegral_ofReal (poincareEnergyDensity_integrable N u)
      (Filter.Eventually.of_forall (poincareEnergyDensity_nonnegative N u)),
    ← poincareEnergySeed_norm_sq_integral, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg m)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

#print axioms poincareEnergyDensity_continuous
#print axioms poincareEnergyDensity_local_integral_le

end QuantitativeMaass
