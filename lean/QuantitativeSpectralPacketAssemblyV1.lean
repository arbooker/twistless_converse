module

public import QuantitativeSpectralDeflationChainV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralPacketAssembly

open QuantitativeSpectralDeflationChain QuantitativeSpectralCornerCutRow
open QuantitativeSpectralTriangularAssembly

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance closedSubmodule_complete (U : ClosedSubmodule ℂ H) :
    CompleteSpace U.toSubmodule := U.isClosed.completeSpace_coe

variable (U : ClosedSubmodule ℂ H) (B : ℕ → H →L[ℂ] H) (c : ℝ)

theorem removed_isStarProjection (i : ℕ) : IsStarProjection (removedProjection U B c i) :=
  QuantitativeSpectralCutRow.removed_projection _ _

theorem removed_right_supported (i : ℕ) :
    removedProjection U B c i * projection U B c i = removedProjection U B c i :=
  Submodule.starProjection_comp_starProjection_of_le (removedSpace_le _ _ _)

theorem removed_next (i : ℕ) :
    removedProjection U B c i * projection U B c (i+1) = 0 := by
  rw [projection_sub_removed, mul_sub, removed_right_supported,
    (removed_isStarProjection U B c i).isIdempotentElem.eq, sub_self]

theorem removed_later (i j : ℕ) (hij : i < j) :
    removedProjection U B c i * projection U B c j = 0 := by
  have hle := chain_antitone U B c (Nat.succ_le_of_lt hij)
  have hp : projection U B c (i+1) * projection U B c j = projection U B c j := by
    apply ContinuousLinearMap.ext
    intro x
    exact (chain U B c (i+1)).toSubmodule.starProjection_eq_self_iff.mpr
      (hle ((chain U B c j).toSubmodule.starProjection_apply_mem x))
  calc
    removedProjection U B c i * projection U B c j =
        removedProjection U B c i * (projection U B c (i+1) * projection U B c j) := by rw [hp]
    _ = 0 := by rw [← mul_assoc, removed_next, zero_mul]

theorem removed_mul_of_lt (i j : ℕ) (hij : i < j) :
    removedProjection U B c i * removedProjection U B c j = 0 := by
  rw [removed_eq_sub U B c j, mul_sub, removed_later U B c i j hij,
    removed_later U B c i (j+1) (lt_trans hij (Nat.lt_succ_self j)), sub_self]

theorem removed_orthogonal (i j : ℕ) (hij : i ≠ j) :
    removedProjection U B c i * removedProjection U B c j = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact removed_mul_of_lt U B c i j h
  · have hh := congrArg star (removed_mul_of_lt U B c j i h)
    simpa only [star_mul, (removed_isStarProjection U B c i).isSelfAdjoint.star_eq,
      (removed_isStarProjection U B c j).isSelfAdjoint.star_eq, star_zero] using hh

/-- Gram domination for the sum of the actual recursively normalized rows.
There is no factor equal to the number of primes: all cross terms vanish. -/
theorem assembled_gram_le {c : ℝ} (hc : 0 < c) (n : ℕ) :
    star (∑ i : Fin n, packetRow U B c i) * (∑ i : Fin n, packetRow U B c i) ≤
      ∑ i : Fin n, star (B i) * B i := by
  apply row_sum_gram_le (fun i : Fin n => removedProjection U B c i)
    (fun i j hij => removed_orthogonal U B c i j (fun he => hij (Fin.ext he)))
    (fun i : Fin n => packetRow U B c i)
    (fun i => packetRow_left_supported U B hc i)
    (fun i => (removed_isStarProjection U B c i).isSelfAdjoint)
  exact fun i => packetRow_gram_le U B hc i

/-- The full finite partition comprises the removed cuts and the final
retained projection, in chronological order. -/
def blocks (n : ℕ) : Fin (n+1) → H →L[ℂ] H :=
  Fin.lastCases (projection U B c n) (fun i : Fin n => removedProjection U B c i)

theorem sum_blocks (n : ℕ) : ∑ i, blocks U B c n i = projection U B c 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [blocks, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [Fin.sum_univ_eq_sum_range, sum_removed]
  abel

#print axioms removed_orthogonal
#print axioms assembled_gram_le
#print axioms sum_blocks

end QuantitativeSpectralPacketAssembly
