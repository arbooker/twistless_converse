module

public import AsymptoticObservationOperatorV1
public import AsymptoticRegularInverseV1
public import AsymptoticRegularSignedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem normal_identity (L : H →L[ℂ] J) : normal (1 : H →L[ℂ] H) L=1+L.adjoint.comp L := by
  simp only [normal,one_def,adjoint_id,comp_id]

theorem normal_identity_norm (L : H →L[ℂ] J) : ‖normal (1 : H →L[ℂ] H) L‖≤1+‖L‖^2 := by
  rw [normal_identity]
  have ho : ‖(1 : H →L[ℂ] H)‖≤1 := norm_id_le
  exact (norm_add_le _ _).trans (by rw [norm_adjoint_comp_self]; nlinarith [ho])

/-- The identity-reconstruction observation inverse agrees with the
coercive Neumann inverse used for regular operator families. -/
theorem operator_identity_inverse (L : H →L[ℂ] J) (C : ℝ)
    (hC : ‖normal (1 : H →L[ℂ] H) L‖≤C) :
    operator (1 : H →L[ℂ] H) L (fun _ => le_rfl)=
      AsymptoticCoerciveNeumann.inverse C (normal (1 : H →L[ℂ] H) L) := by
  ext x
  let e := normalEquiv (1 : H →L[ℂ] H) L (fun _ => le_rfl)
  have he : operator (1 : H →L[ℂ] H) L (fun _ => le_rfl) x=e.symm x := by
    simp only [operator_apply,one_def,adjoint_id,id_apply,e]
  rw [he]
  apply e.injective
  calc
    e (e.symm x)=x := e.apply_symm_apply x
    _=e (AsymptoticCoerciveNeumann.inverse C (normal (1 : H →L[ℂ] H) L) x) :=
      (AsymptoticCoerciveNeumann.mul_apply_inverse C _ hC
        (normal_coercive (1 : H →L[ℂ] H) L (fun _ => le_rfl)) x).symm

#print axioms normal_identity
#print axioms normal_identity_norm
#print axioms operator_identity_inverse

end AsymptoticObservation

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticObservation
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Identity-reconstruction observation inverses retain measurable
matrix coefficients and covariance. -/
theorem identity_observation_regular (L : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (L x) g h)) (hc : Covariant L)
    (M : ℝ) (hM : ∀ x,‖L x‖≤M) :
    (∀ g h,Measurable (fun x => matrix (operator 1 (L x) (fun _ => le_rfl)) g h)) ∧
      Covariant (fun x => operator 1 (L x) (fun _ => le_rfl)) := by
  let B (x : α) := normal (1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (L x)
  have hb (x : α) : ‖B x‖≤1+M^2 :=
    (normal_identity_norm (L x)).trans (by nlinarith [hM x,norm_nonneg (L x)])
  have hco (x : α) := normal_coercive (1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (L x) (fun _ => le_rfl)
  have hmb : ∀ g h,Measurable (fun x => matrix (B x) g h) := by
    simp only [B,normal_identity]
    exact matrix_add_measurable _ _ (fun _ _ => measurable_const)
      (matrix_comp_measurable _ _ (matrix_adjoint_measurable L hm) hm)
  have hcb : Covariant B := by
    simp only [B,normal_identity]
    exact covariant_add _ _ covariant_one (covariant_comp _ _ (covariant_adjoint L hc) hc)
  have he (x : α) := operator_identity_inverse (L x) (1+M^2) (hb x)
  simp only [he]
  exact ⟨inverse_matrix_measurable _ B hmb hb hco,inverse_covariant _ B hcb hb hco⟩

#print axioms identity_observation_regular

end AsymptoticRegularTrace
