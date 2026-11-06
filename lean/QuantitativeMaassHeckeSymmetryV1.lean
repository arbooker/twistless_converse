module

public import QuantitativeMaassHeckeL2V1
public import QuantitativeMaassNormalizerSymmetryV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticClassicalCusp

namespace QuantitativeMaass.HeckeL2

variable (N p : ℕ) [Fact p.Prime] (hN : 0 < N) (hpN : ¬ p ∣ N)
    (A B : ℤ) (hAB : (p : ℤ)*A + (N : ℤ)*B = 1)

theorem normalizer_selfAdjoint :
    IsSelfAdjoint (normalizer N p hN A B hAB).toContinuousLinearMap := by
  apply AutomorphicL2.normalizerIsometry_selfAdjoint
  rw [heckeNormalizerLabel_eq N p (hp p) A B hAB hN]
  simpa only [mul_inv_rev] using (gamma (p*N)).inv_mem
    (AsymptoticAtkinLehner.localAtkin_square_mem N p hN (hp p) A B hAB)

/-- The bounded prime correspondence is self-adjoint on the genuine
level-N quotient Hilbert completion. -/
theorem operator_selfAdjoint : IsSelfAdjoint (operator N p hN hpN A B hAB) := by
  unfold operator
  apply IsSelfAdjoint.smul
  · simp [IsSelfAdjoint]
  · change ContinuousLinearMap.adjoint _ = _
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      (normalizer_selfAdjoint N p hN A B hAB).adjoint_eq,
      ContinuousLinearMap.comp_assoc]

#print axioms normalizer_selfAdjoint
#print axioms operator_selfAdjoint

end QuantitativeMaass.HeckeL2
