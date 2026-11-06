module

public import QuantitativeHolomorphicReconstructionMatrixV1
public import QuantitativeEulerIntegerHeightV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCertificateBranches AsymptoticRegularCertificate

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Every fixed reconstruction certificate has one base matrix height.
All its integer translates have a linear, explicit height bound. -/
theorem certificate_fold_height (hN : 0<N) :
    ∃ C : ℝ, 1≤C ∧ ∀ J : ℕ, ∀ v : Index A,
      ∀ j ∈ Finset.Icc (-(J:ℤ)) J, ∃ M : IntegerMatrix2,
        IntegerAction (AsymptoticRationalBranches.fold (levelQ_pos A hN v)
          (inputShiftQ A v) (outputShiftQ A v) j) M ∧
        MatrixEntryBound M (2*(1+(J:ℝ))*C) := by
  obtain ⟨C,hC,hrep⟩ := QuantitativeEulerIntegerHeight.finite_family_height
    (fun v : Index A => AsymptoticRationalBranches.fold (levelQ_pos A hN v)
      (inputShiftQ A v) (outputShiftQ A v) 0)
  refine ⟨C,hC,?_⟩
  intro J v j hj
  obtain ⟨M,hm,hM⟩ := hrep v
  obtain ⟨L,hl,hL⟩ := QuantitativeEulerIntegerHeight.fold_integer_height
    (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v) hm hM j
  have hj' : |(j:ℝ)|≤J := by
    have hh := Finset.mem_Icc.mp hj
    apply abs_le.mpr
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2
  refine ⟨L,hl,?_⟩
  intro a b
  exact (hL a b).trans (by nlinarith [zero_le_one.trans hC])

/-- Actual reconstruction matrix complexity, with no branch-height or
geometric certificate hypotheses remaining. The single constant depends
only on the fixed level certificate, while every truncation depth and
integer cutoff is quantified explicitly. -/
theorem scaledCutCountExpression_uniform_matrix_height (hN : 0<N) :
    ∃ C : ℝ, 1≤C ∧ ∀ (P : Parameters A) (e : Sector N) (Y : ℝ) (n J : ℕ),
      ExpressionMatrixBound (scaledCutCountExpression A hN P e Y n J)
        (8*max 1 (2*(2*(2*(1+(J:ℝ))*C))^n*(2*(1+(J:ℝ))*C))) := by
  obtain ⟨C,hC,hfold⟩ := certificate_fold_height A hN
  refine ⟨C,hC,?_⟩
  intro P e Y n J
  apply scaledCutCountExpression_matrix_bound A hN P e Y n J
  · nlinarith [Nat.cast_nonneg (α:=ℝ) J]
  · exact hfold J

#print axioms certificate_fold_height
#print axioms scaledCutCountExpression_uniform_matrix_height

end QuantitativeHolomorphic
