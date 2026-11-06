module

public import QuantitativeEulerIntegerHeightV1
public import AsymptoticRationalCompactFoldV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerIntegerHeight

open QuantitativeHolomorphic UpperHalfPlane
open AsymptoticRationalBranches AsymptoticRationalFreeness

/-- The same fixed integer representative controls every compact-row fold;
the sole increase is the explicit linear translation factor. -/
theorem compactFold_integer_height (g : GL (Fin 2) ℚ)
    (hg : 0 < (realMatrix g).det.val) {M : IntegerMatrix2} {B : ℝ}
    (hM : IntegerAction (ofMatrix g hg) M) (hB : MatrixEntryBound M B) (n : ℤ) :
    ∃ Mn : IntegerMatrix2, IntegerAction (compactFold g hg n) Mn ∧
      MatrixEntryBound Mn (2*(1+|(n:ℝ)|)*B) := by
  let T : IntegerMatrix2 := !![1,-n;0,1]
  have hT : MatrixEntryBound T (1+|(n:ℝ)|) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [T, abs_nonneg]
    positivity
  refine ⟨T*M, ⟨?_, ?_⟩, matrix_entry_bound_mul (by positivity) hT hB⟩
  · rw [Matrix.det_mul]
    simpa [T, Matrix.det_fin_two] using hM.1
  · intro z
    rw [compactFold_action, AsymptoticMobiusFold.fold_action, ← ofMatrix_action g hg, hM.2]
    have hd := QuantitativeArithmetic.integer_matrix_denominator_ne_zero M hM.1 z
    norm_num [T, Matrix.mul_apply, Fin.sum_univ_two]
    apply (eq_div_iff hd).2
    rw [sub_mul, div_mul_cancel₀ _ hd]
    ring

#print axioms compactFold_integer_height
end QuantitativeEulerIntegerHeight
