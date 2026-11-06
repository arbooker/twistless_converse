module

public import QuantitativeMaassTraceAdjointV1
public import AsymptoticClassicalCosetBridgeV1
public import QuantitativeEulerModularProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerOldEmbedding

open MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeMaass QuantitativeMaass.AutomorphicL2
open scoped ENNReal InnerProductSpace

variable (N M : ℕ) [NeZero N] (hMN : M ∣ N)

/-- The literal index of the lower-level congruence cover. -/
def coverIndex : ℕ := ((gamma N).subgroupOf (gamma M)).index

theorem coverIndex_pos : 0 < coverIndex N M :=
  Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

/-- The actual identity of functions pulled from level M to level N. -/
def inclusion : AutomorphicSpace M →L[ℂ] AutomorphicSpace N :=
  coverOperator volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (gamma M) (gamma_le_of_dvd hMN)
    (density M) (density N) (density_measurable M) (density_measurable N)
    (density_orbit_sum M) (density_orbit_sum N)

theorem inclusion_norm (f : AutomorphicSpace M) :
    ‖inclusion N M hMN f‖ = Real.sqrt (coverIndex N M : ℝ) * ‖f‖ := by
  refine (denseEmbedding_dense (gamma M) (quotientMeasure M)).induction_on f ?_ ?_
  · exact isClosed_eq (inclusion N M hMN).continuous.norm
      (continuous_const.mul continuous_norm)
  · intro F
    exact (congrArg norm (coverOperator_apply volume
      AsymptoticRationalGroup.measurePreserving (gamma N) (gamma M)
      (gamma_le_of_dvd hMN) (density M) (density N)
      (density_measurable M) (density_measurable N)
      (density_orbit_sum M) (density_orbit_sum N) F)).trans
      (coverRepresentative_norm volume AsymptoticRationalGroup.measurePreserving
        (gamma N) (gamma M) (gamma_le_of_dvd hMN) (density M) (density N)
        (density_measurable M) (density_measurable N)
        (density_orbit_sum M) (density_orbit_sum N) F)

/-- Normalizing by the square root of the index is an actual isometric
embedding of the complete lower-level quotient space. -/
def normalizedInclusion : AutomorphicSpace M →ₗᵢ[ℂ] AutomorphicSpace N where
  toLinearMap := ((Real.sqrt (coverIndex N M : ℝ))⁻¹ : ℂ) •
    (inclusion N M hMN).toLinearMap
  norm_map' f := by
    change ‖((Real.sqrt (coverIndex N M : ℝ))⁻¹ : ℂ) • inclusion N M hMN f‖ = ‖f‖
    rw [norm_smul, inclusion_norm]
    have hp : 0 < Real.sqrt (coverIndex N M : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast coverIndex_pos N M)
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
      ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

/-- The actual unnormalized lower-level trace, defined by Hilbert adjunction. -/
def trace : AutomorphicSpace N →L[ℂ] AutomorphicSpace M :=
  (inclusion N M hMN).adjoint

local instance : Fintype (gamma M ⧸ (gamma N).subgroupOf (gamma M)) := Fintype.ofFinite _

/-- On measurable automorphic representatives the adjoint is the literal
finite coset sum; no spectral or smoothness assumptions occur. -/
theorem trace_apply (f : representatives (gamma N) (quotientMeasure N)) :
    trace N M hMN (denseEmbedding (gamma N) (quotientMeasure N) f) =
      denseEmbedding (gamma M) (quotientMeasure M)
        (traceRepresentative volume AsymptoticRationalGroup.measurePreserving
          (gamma N) (gamma M) (gamma_le_of_dvd hMN)
          (density M) (density N) (density_measurable M) (density_measurable N)
          (density_orbit_sum M) (density_orbit_sum N) f) :=
  coverOperator_adjoint_apply _ _ _ _ _ _ _ _ _ _ _ f

theorem trace_kernel : (trace N M hMN).ker = (inclusion N M hMN).rangeᗮ :=
  (inclusion N M hMN).orthogonal_range.symm

/-- The actual orthogonal projection onto normalized lower-level data. -/
def oldProjection : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  QuantitativeEulerModularProjection.rangeProjection (normalizedInclusion N M hMN)

theorem oldProjection_star : IsStarProjection (oldProjection N M hMN) :=
  QuantitativeEulerModularProjection.rangeProjection_star _

theorem oldProjection_fixes (f : AutomorphicSpace M) :
    oldProjection N M hMN (normalizedInclusion N M hMN f) =
      normalizedInclusion N M hMN f :=
  QuantitativeEulerModularProjection.rangeProjection_fixes _ f

theorem normalizedInclusion_range :
    (normalizedInclusion N M hMN).toContinuousLinearMap.range =
      (inclusion N M hMN).range := by
  have hp : 0 < Real.sqrt (coverIndex N M : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast coverIndex_pos N M)
  have hc : (Real.sqrt (coverIndex N M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  ext y
  constructor
  · rintro ⟨f,rfl⟩
    refine ⟨((Real.sqrt (coverIndex N M : ℝ))⁻¹ : ℂ) • f, ?_⟩
    exact (inclusion N M hMN).map_smul _ f
  · rintro ⟨f,rfl⟩
    refine ⟨(Real.sqrt (coverIndex N M : ℝ) : ℂ) • f, ?_⟩
    change ((Real.sqrt (coverIndex N M : ℝ))⁻¹ : ℂ) •
      inclusion N M hMN ((Real.sqrt (coverIndex N M : ℝ) : ℂ) • f) = _
    rw [map_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rfl

theorem oldProjection_range :
    (oldProjection N M hMN).range = (inclusion N M hMN).range := by
  rw [oldProjection, QuantitativeEulerModularProjection.rangeProjection_range,
    normalizedInclusion_range]

/-- Pullback followed by the literal trace counts each covering sheet once. -/
theorem trace_inclusion (f : AutomorphicSpace M) :
    trace N M hMN (inclusion N M hMN f) = (coverIndex N M : ℂ) • f := by
  refine (denseEmbedding_dense (gamma M) (quotientMeasure M)).induction_on f ?_ ?_
  · exact isClosed_eq ((trace N M hMN).continuous.comp (inclusion N M hMN).continuous)
      (continuous_const_smul _)
  · intro F
    let F' := coverRepresentative volume AsymptoticRationalGroup.measurePreserving
      (gamma N) (gamma M) (gamma_le_of_dvd hMN)
      (density M) (density N) (density_measurable M) (density_measurable N)
      (density_orbit_sum M) (density_orbit_sum N) F
    have he : inclusion N M hMN (denseEmbedding (gamma M) (quotientMeasure M) F) =
        denseEmbedding (gamma N) (quotientMeasure N) F' :=
      coverOperator_apply _ _ _ _ _ _ _ _ _ _ _ F
    rw [he, trace_apply]
    have hr : traceRepresentative volume AsymptoticRationalGroup.measurePreserving
        (gamma N) (gamma M) (gamma_le_of_dvd hMN)
        (density M) (density N) (density_measurable M) (density_measurable N)
        (density_orbit_sum M) (density_orbit_sum N) F' = (coverIndex N M : ℂ) • F := by
      apply Subtype.ext
      funext z
      rw [traceRepresentative_apply]
      change (∑ q : gamma M ⧸ (gamma N).subgroupOf (gamma M),
        F.val (q.out.val⁻¹ • z)) = (coverIndex N M : ℂ) * F.val z
      have hi (q : gamma M ⧸ (gamma N).subgroupOf (gamma M)) :
          F.val (q.out.val⁻¹ • z) = F.val z := F.property.2.1 q.out⁻¹ z
      simp only [hi, Finset.sum_const, Finset.card_univ]
      simp [coverIndex, Subgroup.index, Nat.card_eq_fintype_card, nsmul_eq_mul]
    rw [hr, map_smul]

#print axioms inclusion_norm
#print axioms normalizedInclusion
#print axioms trace_apply
#print axioms trace_kernel
#print axioms oldProjection_star
#print axioms oldProjection_range
#print axioms trace_inclusion
end QuantitativeEulerOldEmbedding
