module

public import QuantitativeMaassShiftedWaveDomainV1
public import QuantitativeMaassHeckeSymmetryV1
public import QuantitativeMaassCuspidalizerOrderV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

open Wave

theorem heckeWaveDifference_selfAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T W : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hW : IsSelfAdjoint W) :
    IsSelfAdjoint (T - (2 : ℂ) • W) :=
  hT.sub (IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) hW)

variable (N p : ℕ) [Fact p.Prime] (hN : 0 < N) (hpN : ¬ p ∣ N)
    (A B : ℤ) (hAB : (p : ℤ)*A + (N : ℤ)*B = 1)

/-- The actual Hecke-minus-shifted-wave operator on the quotient completion. -/
def lvDifference : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  HeckeL2.operator N p hN hpN A B hAB - (2 : ℂ) • shiftedQuotientWave N (Real.log p)

/-- An explicit positive normalization. Its precise simplification is
irrelevant for the bounded polynomial, and it includes exceptional spectrum. -/
def lvBound (p : ℕ) : ℝ :=
  (p+1 : ℕ) / Real.sqrt (p : ℝ) + 2 * Real.cosh (|Real.log p|/2)

theorem lvBound_pos (p : ℕ) : 0 < lvBound p := by
  unfold lvBound
  positivity

theorem lvDifference_selfAdjoint : IsSelfAdjoint (lvDifference N p hN hpN A B hAB) := by
  unfold lvDifference
  exact heckeWaveDifference_selfAdjoint _ _
    (HeckeL2.operator_selfAdjoint N p hN hpN A B hAB)
    (shiftedQuotientWave_isSelfAdjoint N (Real.log p))

theorem lvDifference_norm_le : ‖lvDifference N p hN hpN A B hAB‖ ≤ lvBound p := by
  unfold lvDifference lvBound
  have hW : ‖(2 : ℂ) • shiftedQuotientWave N (Real.log p)‖ ≤
      2 * Real.cosh (|Real.log p|/2) := by
    calc
      _ ≤ ‖(2 : ℂ)‖ * ‖shiftedQuotientWave N (Real.log p)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ = 2 * ‖shiftedQuotientWave N (Real.log p)‖ := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (shiftedQuotientWave_norm_le N _) (by norm_num)
  exact (norm_sub_le (HeckeL2.operator N p hN hpN A B hAB)
    ((2 : ℂ) • shiftedQuotientWave N (Real.log p))).trans
      (add_le_add (HeckeL2.operator_norm_le N p hN hpN A B hAB) hW)

/-- The literal LV polynomial on the genuine quotient Hilbert space.
Its range is not yet asserted to be cuspidal: that requires the all-cusp
constant-term intertwining theorem. -/
def actualLVFilter (d : ℕ) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  lvFilter (lvDifference N p hN hpN A B hAB) ((lvBound p)^2)⁻¹ d

theorem actualLVFilter_order (d : ℕ) :
    0 ≤ actualLVFilter N p hN hpN A B hAB d ∧
    actualLVFilter N p hN hpN A B hAB d ≤ 1 ∧
    ‖actualLVFilter N p hN hpN A B hAB d‖ ≤ 1 :=
  lvFilter_normalized_order _ (lvDifference_selfAdjoint N p hN hpN A B hAB)
    _ (lvBound_pos p) (lvDifference_norm_le N p hN hpN A B hAB) d

theorem actualLVFilter_mem_range (d : ℕ) (v : AutomorphicSpace N) :
    actualLVFilter N p hN hpN A B hAB d v ∈
      LinearMap.range (lvDifference N p hN hpN A B hAB).toLinearMap :=
  lvFilter_mem_range _ _ _ _

#print axioms lvDifference_selfAdjoint
#print axioms lvDifference_norm_le
#print axioms actualLVFilter_order
#print axioms actualLVFilter_mem_range

end QuantitativeMaass
