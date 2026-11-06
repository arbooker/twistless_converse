module

public import QuantitativeSpectralCutRowV1
public import AsymptoticCornerKernelV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralCornerCutRow

open ContinuousLinearMap InnerProductSpace QuantitativeSpectralCutRow
open scoped InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Submodule ℂ H) [CompleteSpace U] (B : H →L[ℂ] H) (c : ℝ)

/-- The high cut uses the residual restricted to the current surviving corner. -/
def restricted : H →L[ℂ] H := B * U.starProjection

def removedSpace : Submodule ℂ H :=
  QuantitativeSpectralCut.highAt (star (restricted U B) * restricted U B) (c^2)

instance removedSpace_complete : CompleteSpace (removedSpace U B c) :=
  QuantitativeSpectralCut.highAt_complete _ _

def nextSpace : Submodule ℂ H :=
  AsymptoticCornerKernel.remaining U (removed (restricted U B) c)

instance nextSpace_complete : CompleteSpace (nextSpace U B c) :=
  AsymptoticCornerKernel.remaining_complete _ _

theorem removedSpace_le : removedSpace U B c ≤ U := by
  apply QuantitativeSpectralCut.highAt_le_corner _
    (IsSelfAdjoint.star_mul_self (restricted U B)) U (sq_nonneg c)
  change (star (restricted U B) * (B * U.starProjection)) * U.starProjection = _
  rw [mul_assoc, mul_assoc, Submodule.isIdempotentElem_starProjection U |>.eq]
  rfl

theorem nextSpace_le : nextSpace U B c ≤ U := inf_le_left

/-- An exact projection subtraction, valid also for infinite-dimensional
closed subspaces and nonclosed residual range. -/
theorem nextSpace_projection : (nextSpace U B c).starProjection =
    U.starProjection - removed (restricted U B) c := by
  have hh : (removed (restricted U B) c).comp U.starProjection =
      removed (restricted U B) c :=
    Submodule.starProjection_comp_starProjection_of_le (removedSpace_le U B c)
  have he := AsymptoticCornerKernel.remaining_projection U (removed (restricted U B) c) hh
  simpa only [nextSpace, removed, Submodule.ker_starProjection, Submodule.orthogonal_orthogonal] using he

theorem nextSpace_low : nextSpace U B c ≤
    QuantitativeSpectralCut.lowAt (star (restricted U B) * restricted U B) (c^2) := by
  intro v hv
  have hh : removed (restricted U B) c v = 0 := hv.2
  have hm := (QuantitativeSpectralCut.highAt
    (star (restricted U B) * restricted U B) (c^2)).starProjection_apply_eq_zero_iff.mp hh
  simpa only [QuantitativeSpectralCut.highAt, QuantitativeSpectralCut.high,
    QuantitativeSpectralCut.lowAt, Submodule.orthogonal_orthogonal] using hm

/-- The inverse is formed using the restricted residual, while the row acts
on the original residual. This distinction retains its off-diagonal blocks. -/
def row : H →L[ℂ] H := cutNormalizer (restricted U B) c * B

theorem row_diagonal (hc : 0 < c) :
    row U B c * removed (restricted U B) c = c • removed (restricted U B) c := by
  have hp : U.starProjection * removed (restricted U B) c =
      removed (restricted U B) c := by
    apply ContinuousLinearMap.ext
    intro x
    exact U.starProjection_eq_self_iff.mpr
      (removedSpace_le U B c ((removedSpace U B c).starProjection_apply_mem x))
  have he := cutNormalizer_diagonal (restricted U B) hc
  change cutNormalizer (restricted U B) c * (B * U.starProjection) * removed (restricted U B) c = _ at he
  rw [mul_assoc, mul_assoc, hp, ← mul_assoc] at he
  exact he

theorem row_retained : row U B c * (nextSpace U B c).starProjection = 0 := by
  have hp : U.starProjection * (nextSpace U B c).starProjection =
      (nextSpace U B c).starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    exact U.starProjection_eq_self_iff.mpr
      (nextSpace_le U B c ((nextSpace U B c).starProjection_apply_mem x))
  have hl : retained (restricted U B) c * (nextSpace U B c).starProjection =
      (nextSpace U B c).starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    exact Submodule.starProjection_eq_self_iff.mpr
      (nextSpace_low U B c ((nextSpace U B c).starProjection_apply_mem x))
  calc
    row U B c * (nextSpace U B c).starProjection =
        (cutNormalizer (restricted U B) c * restricted U B * retained (restricted U B) c) *
          (nextSpace U B c).starProjection := by
      change cutNormalizer (restricted U B) c * B * (nextSpace U B c).starProjection =
        (cutNormalizer (restricted U B) c * (B * U.starProjection) * retained (restricted U B) c) *
          (nextSpace U B c).starProjection
      simp only [mul_assoc, hl, hp]
    _ = 0 := by rw [cutNormalizer_retained, zero_mul]

theorem row_left_supported (hc : 0 < c) :
    removed (restricted U B) c * row U B c = row U B c := by
  have hh := QuantitativeSpectralNormalizedRow.normalizer_left_supported
    (removed (restricted U B) c) (restricted U B)
    (removed_projection (restricted U B) c) c hc (removed_coercive (restricted U B) c)
  change removed (restricted U B) c * (cutNormalizer (restricted U B) c * B) = _
  rw [← mul_assoc]
  exact congrArg (fun W => W * B) hh

/-- Exact solutions in the current corner survive the cut. -/
theorem kernel_survives {v : H} (hv : v ∈ U) (hB : B v = 0) : v ∈ nextSpace U B c := by
  refine ⟨hv, ?_⟩
  have hp : U.starProjection v = v := U.starProjection_eq_self_iff.mpr hv
  have ht : restricted U B v = 0 := by change B (U.starProjection v) = 0; rw [hp, hB]
  have hl := QuantitativeSpectralCut.kernel_mem_lowAt (star (restricted U B) * restricted U B)
    (IsSelfAdjoint.star_mul_self (restricted U B)) (sq_nonneg c)
    (v := v) (by change (restricted U B).adjoint (restricted U B v) = 0; rw [ht, map_zero])
  change removed (restricted U B) c v = 0
  apply (QuantitativeSpectralCut.highAt
    (star (restricted U B) * restricted U B) (c^2)).starProjection_apply_eq_zero_iff.mpr
  simpa only [QuantitativeSpectralCut.highAt, QuantitativeSpectralCut.high,
    QuantitativeSpectralCut.lowAt, Submodule.orthogonal_orthogonal] using hl

theorem row_gram_le (hc : 0 < c) : star (row U B c) * row U B c ≤ star B * B :=
  QuantitativeSpectralTriangularAssembly.contraction_gram _ _
    (cutNormalizer_contracts (restricted U B) hc)

#print axioms removedSpace_le
#print axioms nextSpace_projection
#print axioms row_diagonal
#print axioms row_retained
#print axioms row_left_supported
#print axioms kernel_survives
#print axioms row_gram_le

end QuantitativeSpectralCornerCutRow
