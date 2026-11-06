module

public import QuantitativeSpectralPacketAssemblyV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralPacketSupport

open QuantitativeSpectralDeflationChain QuantitativeSpectralCornerCutRow
open QuantitativeSpectralCutRow QuantitativeSpectralPacketAssembly

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance closedSubmodule_complete (U : ClosedSubmodule ℂ H) :
    CompleteSpace U.toSubmodule := U.isClosed.completeSpace_coe
variable (U : ClosedSubmodule ℂ H) (B : ℕ → H →L[ℂ] H) (c : ℝ)

theorem projection_left_initial (n : ℕ) :
    projection U B c 0 * projection U B c n = projection U B c n := by
  apply ContinuousLinearMap.ext
  intro x
  exact U.toSubmodule.starProjection_eq_self_iff.mpr
    (chain_antitone U B c (Nat.zero_le n) ((chain U B c n).toSubmodule.starProjection_apply_mem x))

theorem projection_right_initial (n : ℕ) :
    projection U B c n * projection U B c 0 = projection U B c n :=
  Submodule.starProjection_comp_starProjection_of_le (chain_antitone U B c (Nat.zero_le n))

theorem removed_left_initial (n : ℕ) :
    projection U B c 0 * removedProjection U B c n = removedProjection U B c n := by
  rw [removed_eq_sub, mul_sub, projection_left_initial, projection_left_initial]

theorem removed_right_initial (n : ℕ) :
    removedProjection U B c n * projection U B c 0 = removedProjection U B c n := by
  rw [removed_eq_sub, sub_mul, projection_right_initial, projection_right_initial]

theorem row_left_initial (hc : 0 < c) (n : ℕ) :
    projection U B c 0 * packetRow U B c n = packetRow U B c n := by
  calc
    projection U B c 0 * packetRow U B c n =
        projection U B c 0 * (removedProjection U B c n * packetRow U B c n) := by
      rw [packetRow_left_supported U B hc n]
    _ = packetRow U B c n := by
      rw [← mul_assoc, removed_left_initial, packetRow_left_supported U B hc n]

/-- The only source assumption is the original residual's terminal support;
the recursive row then belongs to the same two-sided terminal corner. -/
theorem row_right_initial (n : ℕ) (hB : B n * projection U B c 0 = B n) :
    packetRow U B c n * projection U B c 0 = packetRow U B c n := by
  change (cutNormalizer (restricted (chain U B c n).toSubmodule (B n)) c * B n) *
    projection U B c 0 = _
  rw [mul_assoc, hB]
  rfl

#print axioms projection_left_initial
#print axioms projection_right_initial
#print axioms removed_left_initial
#print axioms removed_right_initial
#print axioms row_left_initial
#print axioms row_right_initial

end QuantitativeSpectralPacketSupport
