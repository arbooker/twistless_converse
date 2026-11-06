module

public import QuantitativeEulerModularEmbeddingV1
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerModularProjection

open ContinuousLinearMap

section General
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def rangeProjection (U : H →ₗᵢ[ℂ] K) : K →L[ℂ] K :=
  U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint

theorem rangeProjection_fixes (U : H →ₗᵢ[ℂ] K) (x : H) : rangeProjection U (U x) = U x := by
  have he := congrArg (fun T : H →L[ℂ] H => T x) U.adjoint_comp_self
  change U.toContinuousLinearMap.adjoint (U x)=x at he
  change U (U.toContinuousLinearMap.adjoint (U x))=U x
  rw [he]

theorem rangeProjection_star (U : H →ₗᵢ[ℂ] K) : IsStarProjection (rangeProjection U) := by
  constructor
  · ext x
    change rangeProjection U (rangeProjection U x)=rangeProjection U x
    exact rangeProjection_fixes U (U.toContinuousLinearMap.adjoint x)
  · change (rangeProjection U).adjoint = rangeProjection U
    simp only [rangeProjection,adjoint_comp,adjoint_adjoint]

theorem rangeProjection_range (U : H →ₗᵢ[ℂ] K) :
    (rangeProjection U).range=U.toContinuousLinearMap.range := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨U.toContinuousLinearMap.adjoint y,rfl⟩
  · rintro ⟨y,rfl⟩
    exact ⟨U y,rangeProjection_fixes U y⟩

theorem rangeProjection_norm_le (U : H →ₗᵢ[ℂ] K) : ‖rangeProjection U‖ ≤ 1 := by
  have hU : ‖U.toContinuousLinearMap‖ ≤ 1 := by
    apply U.toContinuousLinearMap.opNorm_le_bound zero_le_one
    intro x
    simp
  calc
    _ ≤ ‖U.toContinuousLinearMap‖ * ‖U.toContinuousLinearMap.adjoint‖ := opNorm_comp_le _ _
    _ ≤ 1*1 := mul_le_mul hU (by simpa using hU) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end General

open MeasureTheory UpperHalfPlane QuantitativeMaass.AutomorphicL2
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip

variable (N : ℕ) {ε : ℝ} (hε : 0 < ε) {t : ℕ} (ht : 1 ≤ t)

/-- Actual orthogonal projection onto the normalized full-modular range.
This is not the weighted new/sign projection, which needs a compressed
metric inverse on the corresponding quotient subspace. -/
def projection : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space :=
  rangeProjection (QuantitativeEulerModularEmbedding.isometry N hε ht)

theorem projection_isStarProjection : IsStarProjection (projection N hε ht) :=
  rangeProjection_star _

theorem projection_norm_le : ‖projection N hε ht‖ ≤ 1 := rangeProjection_norm_le _

theorem projection_range :
    (projection N hε ht).range =
      (QuantitativeEulerModularEmbedding.isometry N hε ht).toContinuousLinearMap.range :=
  rangeProjection_range _

theorem projection_fixes (F : space (gamma N) (quotientMeasure N)) :
    projection N hε ht (QuantitativeEulerModularEmbedding.isometry N hε ht F) =
      QuantitativeEulerModularEmbedding.isometry N hε ht F := rangeProjection_fixes _ F

#print axioms projection_isStarProjection
#print axioms projection_range
#print axioms projection_fixes

end QuantitativeEulerModularProjection
