module

public import AsymptoticObservationKernelLimitV1
public import AsymptoticRegularObservationGramV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap

variable {G H J K : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Changing the observation target space while preserving its Gram
operator leaves the positive reconstruction operator unchanged. -/
theorem operator_eq_of_gram (R : G →L[ℂ] H) (L : H →L[ℂ] J) (M : H →L[ℂ] K)
    (hR : ∀ g,‖g‖≤‖R g‖) (h : L.adjoint.comp L=M.adjoint.comp M) :
    operator R L hR=operator R M hR := by
  have hn : normal R L=normal R M := by rw [normal_formula,normal_formula,h]
  ext1 x
  change R ((normalEquiv R L hR).symm (R.adjoint x))=
    R ((normalEquiv R M hR).symm (R.adjoint x))
  congr 1
  apply (normalEquiv R L hR).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,normalEquiv_apply,hn]
  exact ((normalEquiv R M hR).apply_symm_apply (R.adjoint x)).symm

theorem nat_scaled_gram (L : H →L[ℂ] J) (n : ℕ) :
    ((n:ℂ) • L).adjoint.comp ((n:ℂ) • L)=((n^2:ℕ):ℂ) • L.adjoint.comp L := by
  simp only [map_smulₛₗ,starRingEnd_apply,star_natCast,smul_comp,comp_smul,smul_smul,pow_two,Nat.cast_mul]

#print axioms operator_eq_of_gram
#print axioms nat_scaled_gram

end AsymptoticObservation

namespace AsymptoticObservationStack

open ContinuousLinearMap

variable {ι E J : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- Repeating every row d times multiplies the observation Gram by d.
The repeated family still consists solely of the original equations. -/
theorem repeated_stack_gram (L : ι → E →L[ℂ] J) (d : ℕ) :
    (stack (fun j : Fin d × ι => L j.2)).adjoint.comp (stack (fun j : Fin d × ι => L j.2))=
      (d:ℂ) • (stack L).adjoint.comp (stack L) := by
  rw [stack_gram,stack_gram,Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_smul_eq_nsmul]

theorem repeated_square_gram (L : ι → E →L[ℂ] J) (n : ℕ) :
    (stack (fun j : Fin ((n+1)^2) × ι => L j.2)).adjoint.comp
        (stack (fun j : Fin ((n+1)^2) × ι => L j.2))=
      (((n+1:ℕ):ℂ) • stack L).adjoint.comp (((n+1:ℕ):ℂ) • stack L) := by
  rw [repeated_stack_gram,AsymptoticObservation.nat_scaled_gram]

#print axioms repeated_stack_gram
#print axioms repeated_square_gram

end AsymptoticObservationStack
