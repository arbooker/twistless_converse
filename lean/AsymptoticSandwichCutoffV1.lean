module

public import AsymptoticDiagonalSubtractionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap InnerProductSpace AsymptoticDiagonalTrace
open scoped InnerProduct

variable {G H : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem compressedSandwich_diagonal_eq (R : G →L[ℂ] H) (I : G →L[ℂ] G)
    (U : Submodule ℂ H) [CompleteSpace U] (u : U) :
    ⟪compressedSandwich R I U u,u⟫_ℂ = ⟪I (R.adjoint (u : H)),R.adjoint (u : H)⟫_ℂ := by
  have hu := U.subtypeL.adjoint_inner_left u (R (I (R.adjoint (u : H))))
  change ⟪U.subtypeL.adjoint (R (I (R.adjoint (u : H)))),u⟫_ℂ = _
  rw [hu]
  exact (R.adjoint_inner_right (I (R.adjoint (u : H))) (u : H)).symm

theorem compressedSandwich_trace_eq_sum (R : G →L[ℂ] H) (I : G →L[ℂ] G)
    (U : Submodule ℂ H) [CompleteSpace U] (b : HilbertBasis ℕ ℂ U) :
    trace b (compressedSandwich R I U) =
      ∑' n, (⟪I (R.adjoint (b n : H)),R.adjoint (b n : H)⟫_ℂ).re := by
  simp only [trace, compressedSandwich_diagonal_eq]

/-- Remove a spatial part of the range before forming the sandwich. -/
noncomputable def removePart (P : H →L[ℂ] H) (R : G →L[ℂ] H) : G →L[ℂ] H :=
  (1-P).comp R

theorem removePart_adjoint_apply (P : H →L[ℂ] H) (hP : P.adjoint = P)
    (R : G →L[ℂ] H) (x : H) :
    (removePart P R).adjoint x = R.adjoint x - R.adjoint (P x) := by
  simp only [removePart, adjoint_comp, map_sub, adjoint_one, hP, comp_apply, sub_apply]
  rfl

/-- An upper spatial cutoff can be removed using the total Gram trace
and the mass in the omitted region. No identity-block calculation or
positivity of the middle polynomial is required. -/
theorem removePart_trace_bound (P : H →L[ℂ] H) (hP : P.adjoint = P)
    (R : G →L[ℂ] H) (I : G →L[ℂ] G) (U : Submodule ℂ H) [CompleteSpace U]
    (b : HilbertBasis ℕ ℂ U)
    (hu : Summable (fun n => ‖R.adjoint (b n : H)‖^2))
    (hd : Summable (fun n => ‖R.adjoint (P (b n : H))‖^2)) {A D : ℝ}
    (hA : (∑' n, ‖R.adjoint (b n : H)‖^2) ≤ A)
    (hD : (∑' n, ‖R.adjoint (P (b n : H))‖^2) ≤ D) :
    ‖trace b (compressedSandwich R I U) - trace b (compressedSandwich (removePart P R) I U)‖ ≤
      ‖I‖ * (2*Real.sqrt A*Real.sqrt D + D) := by
  simp only [compressedSandwich_trace_eq_sum, removePart_adjoint_apply P hP]
  exact AsymptoticDiagonalComparison.trace_subtract_bound I
    (fun n => R.adjoint (b n : H)) (fun n => R.adjoint (P (b n : H))) hu hd hA hD

theorem normalize_sqrt_bound {A D k : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hk : 0 < k) :
    (2*Real.sqrt (A*k)*Real.sqrt (D*k)+D*k)/k = 2*Real.sqrt A*Real.sqrt D+D := by
  rw [Real.sqrt_mul hA, Real.sqrt_mul hD]
  have he : 2*(Real.sqrt A*Real.sqrt k)*(Real.sqrt D*Real.sqrt k)+D*k =
      (2*Real.sqrt A*Real.sqrt D+D)*k := by
    calc
      _ = 2*Real.sqrt A*Real.sqrt D*(Real.sqrt k)^2+D*k := by ring
      _ = _ := by rw [Real.sq_sqrt hk.le]; ring
  rw [he, mul_div_cancel_right₀ _ hk.ne']

theorem removePart_normalized_trace_bound (P : H →L[ℂ] H) (hP : P.adjoint = P)
    (R : G →L[ℂ] H) (I : G →L[ℂ] G) (U : Submodule ℂ H) [CompleteSpace U]
    (b : HilbertBasis ℕ ℂ U)
    (hu : Summable (fun n => ‖R.adjoint (b n : H)‖^2))
    (hd : Summable (fun n => ‖R.adjoint (P (b n : H))‖^2)) {A D k : ℝ}
    (hA0 : 0 ≤ A) (hD0 : 0 ≤ D) (hk : 0 < k)
    (hA : (∑' n, ‖R.adjoint (b n : H)‖^2) ≤ A*k)
    (hD : (∑' n, ‖R.adjoint (P (b n : H))‖^2) ≤ D*k) :
    ‖trace b (compressedSandwich R I U) - trace b (compressedSandwich (removePart P R) I U)‖/k ≤
      ‖I‖ * (2*Real.sqrt A*Real.sqrt D+D) := by
  apply (div_le_div_of_nonneg_right (removePart_trace_bound P hP R I U b hu hd hA hD) hk.le).trans_eq
  rw [mul_div_assoc, normalize_sqrt_bound hA0 hD0 hk]

#print axioms compressedSandwich_diagonal_eq
#print axioms removePart_trace_bound
#print axioms removePart_normalized_trace_bound

end AsymptoticObservation
