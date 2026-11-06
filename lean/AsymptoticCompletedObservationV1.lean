module

public import AsymptoticRegularObservationNormalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap InnerProductSpace

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- Completing the normal operator by the identity off an isometrically
embedded source preserves its action on that source. -/
theorem completedNormal_on_source (S : G →L[ℂ] H) (hS : S.adjoint.comp S=1)
    (R : G →L[ℂ] H) (L : H →L[ℂ] J) (g : G) :
    completedNormal (S.comp S.adjoint) (R.comp S.adjoint) L (S g)=S (normal R L g) := by
  have hs : S.adjoint (S g)=g := congrArg (fun T : G →L[ℂ] G => T g) hS
  simp only [completedNormal,normal,sub_apply,add_apply,comp_apply,adjoint_comp,adjoint_adjoint,
    ContinuousLinearMap.one_def,id_apply,hs,map_add]
  abel

/-- The completed inverse on the ambient space gives exactly the same
positive operator as the inverse on the terminal source. -/
theorem operator_eq_completed (S : G →L[ℂ] H) (hS : S.adjoint.comp S=1)
    (R : G →L[ℂ] H) (L : H →L[ℂ] J) (hR : ∀ g,‖g‖≤‖R g‖)
    (I : H →L[ℂ] H)
    (hI : I.comp (completedNormal (S.comp S.adjoint) (R.comp S.adjoint) L)=1) :
    operator R L hR=(R.comp S.adjoint).comp (I.comp (R.comp S.adjoint).adjoint) := by
  apply ContinuousLinearMap.ext
  intro x
  let g := (normalEquiv R L hR).symm (R.adjoint x)
  have hg : normal R L g=R.adjoint x := (normalEquiv R L hR).apply_symm_apply _
  have hi := congrArg (fun T : H →L[ℂ] H => T (S g)) hI
  change I (completedNormal (S.comp S.adjoint) (R.comp S.adjoint) L (S g))=S g at hi
  rw [completedNormal_on_source S hS R L g,hg] at hi
  have hs : S.adjoint (S g)=g := congrArg (fun T : G →L[ℂ] G => T g) hS
  have he := congrArg (fun y : H => R (S.adjoint y)) hi
  rw [hs] at he
  change R g=(R.comp S.adjoint) (I ((R.comp S.adjoint).adjoint x))
  simpa only [adjoint_comp,adjoint_adjoint,comp_apply] using he.symm

#print axioms completedNormal_on_source
#print axioms operator_eq_completed

end AsymptoticObservation
