module

public import QuantitativeMaassLocalRestrictionV1
public import QuantitativeMaassInvariantLocalIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal

namespace QuantitativeMaass

/-- The original local restriction has the square-root overlap bound
already on invariant representatives. -/
theorem representativeRestriction_bound_of_overlap (N : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    ‖representativeRestriction N K hK hK.measurableSet f‖ ≤
      Real.sqrt (m : ℝ) * ‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f‖ := by
  have hb := invariant_lintegral_restrict_le volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N) K hK.measurableSet
    (m : ℝ≥0∞) (orbit_indicator_tsum_le_of_overlap K m hm)
    (fun z => ENNReal.ofReal (‖f.val z‖^2)) (f.property.1.norm.pow_const 2).ennreal_ofReal
    (fun g z => congrArg (fun w : ℂ => ENNReal.ofReal (‖w‖^2)) (f.property.2.1 g z))
  have hf : (∫⁻ z, ENNReal.ofReal (‖f.val z‖^2) ∂quotientMeasure N) ≠ ∞ := by
    exact ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z => sq_nonneg ‖f.val z‖))).mp
      (f.property.2.2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).2).ne
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hf) hb
  rw [square_energy_toReal _ (representativeLocalMemLp N K hK hK.measurableSet f),
    ENNReal.toReal_mul, ENNReal.toReal_natCast, square_energy_toReal _ f.property.2.2] at ht
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  exact ht

/-- Explicit quantitative norm bound for the existing quotient
restriction on its whole completed Hilbert space. -/
theorem quotientRestriction_norm_le_of_overlap (N : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m) :
    ‖quotientRestriction N K hK hK.measurableSet‖ ≤ Real.sqrt (m : ℝ) :=
  LinearMap.opNorm_extendOfNorm_le
    (f := representativeRestriction N K hK hK.measurableSet)
    (e := AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))
    (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N))
    (Real.sqrt_nonneg _) (representativeRestriction_bound_of_overlap N K hK m hm)

#print axioms representativeRestriction_bound_of_overlap
#print axioms quotientRestriction_norm_le_of_overlap

end QuantitativeMaass
