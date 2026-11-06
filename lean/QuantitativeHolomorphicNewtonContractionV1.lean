module

public import QuantitativeHolomorphicGramV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap

variable {G H : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Newton normalization is a contraction even when the approximating
Gram has a kernel.  No inverse or lower spectral bound is required. -/
theorem polynomialNormalizedReconstruction_norm_le (V : G →L[ℂ] H)
    (hV : ‖V‖ ≤ 1) (n : ℕ) : ‖polynomialNormalizedReconstruction V n‖ ≤ 1 := by
  let A := V.adjoint.comp V
  let q := inverseSqrtPolynomial n
  let T := Polynomial.aeval A q
  have hA : IsSelfAdjoint A := (isPositive_adjoint_comp_self V).isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ A, 0 ≤ x ∧ x ≤ 1 :=
    reconstruction_gram_spectrum V (fun v => by simp) hV
  have hq : ContinuousOn q.eval (spectrum ℝ A) := q.continuous.continuousOn
  have hid : ContinuousOn (fun x : ℝ => x) (spectrum ℝ A) := continuous_id.continuousOn
  have hT : T = cfc q.eval A := (cfc_polynomial q A hA).symm
  have hTadj : T.adjoint = T := by
    rw [hT]
    exact (cfc_predicate q.eval A : IsSelfAdjoint (cfc q.eval A))
  have hprod : T * A * T = cfc (fun x : ℝ => x * q.eval x ^ 2) A := by
    have hc : T * A * T = cfc (fun x : ℝ => q.eval x * x * q.eval x) A := by
      rw [cfc_mul (fun x : ℝ => q.eval x * x) q.eval A (hq.mul hid) hq,
        cfc_mul q.eval (fun x : ℝ => x) A hq hid, cfc_id' ℝ A hA, ← hT]
    rw [hc]
    apply cfc_congr
    intro x _
    ring
  have hnorm : ‖T * A * T‖ ≤ 1 := by
    rw [hprod]
    apply norm_cfc_le zero_le_one
    intro x hx
    have hx0 := (hspec x hx).1
    have hx1 := (hspec x hx).2
    have hinv := (inverseSqrt_invariant hx0 hx1 n).2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0 (sq_nonneg _))]
    change x * inverseSqrtValue n x ^ 2 ≤ 1
    linarith
  have hg : (polynomialNormalizedReconstruction V n).adjoint.comp
      (polynomialNormalizedReconstruction V n) = T * A * T := by
    change (V.comp T).adjoint.comp (V.comp T) = T * A * T
    rw [adjoint_comp, hTadj]
    simp only [mul_def, comp_assoc, A]
  have hh := congrArg norm hg
  rw [norm_adjoint_comp_self] at hh
  have hn := norm_nonneg (polynomialNormalizedReconstruction V n)
  nlinarith

#print axioms polynomialNormalizedReconstruction_norm_le

end QuantitativeHolomorphic
