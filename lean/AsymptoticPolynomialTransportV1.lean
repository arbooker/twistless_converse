module

public import AsymptoticCompletedObservationV1
public import AsymptoticInversePolynomialV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCoerciveNeumann

open ContinuousLinearMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The finite inverse polynomial respects an exact intertwining, using
the same scalar coefficients on both Hilbert spaces. -/
theorem polynomial_intertwines (C : ℝ) (M : E →L[ℂ] E) (N : F →L[ℂ] F)
    (S : E →L[ℂ] F) (h : N.comp S=S.comp M) (n : ℕ) :
    (polynomial C N n).comp S=S.comp (polynomial C M n) := by
  have hstep (x : E) : step C N (S x)=S (step C M x) := by
    have he := congrArg (fun T : E →L[ℂ] F => T x) h
    change N (S x)=S (M x) at he
    simp only [step,sub_apply,one_def,id_apply,smul_apply,map_sub,map_smul,he]
  have hp (j : ℕ) (x : E) : ((step C N)^j) (S x)=S (((step C M)^j) x) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ',pow_succ']
      change step C N (((step C N)^j) (S x))=S (step C M (((step C M)^j) x))
      rw [ih,hstep]
  ext1 x
  simp only [polynomial,comp_apply,smul_apply,sum_apply,map_sum,map_smul,hp]

end AsymptoticCoerciveNeumann

namespace AsymptoticObservation

open ContinuousLinearMap

variable {G E H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem normal_isometric_output (U : E →L[ℂ] H) (hU : U.adjoint.comp U=1)
    (R : G →L[ℂ] E) (L : H →L[ℂ] J) :
    normal (U.comp R) L=normal R (L.comp U) := by
  ext1 g
  have hu (x : E) : U.adjoint (U x)=x := congrArg (fun T : E →L[ℂ] E => T x) hU
  simp only [normal,adjoint_comp,comp_apply,add_apply,hu]

/-- Transport a completed normal polynomial through the terminal and
output isometries. This is an operator identity, with no trace premise. -/
theorem completed_polynomial_sandwich (S : G →L[ℂ] H) (hS : S.adjoint.comp S=1)
    (U : E →L[ℂ] H) (hU : U.adjoint.comp U=1) (R : G →L[ℂ] E) (L : H →L[ℂ] J)
    (C : ℝ) (n : ℕ) :
    let A := U.comp (R.comp S.adjoint)
    A.comp ((AsymptoticCoerciveNeumann.polynomial C (completedNormal (S.comp S.adjoint) A L) n).comp A.adjoint)=
      U.comp ((R.comp ((AsymptoticCoerciveNeumann.polynomial C (normal R (L.comp U)) n).comp R.adjoint)).comp U.adjoint) := by
  let A := U.comp (R.comp S.adjoint)
  let M := completedNormal (S.comp S.adjoint) A L
  let N := normal R (L.comp U)
  have hi : M.comp S=S.comp N := by
    ext1 g
    exact (completedNormal_on_source S hS (U.comp R) L g).trans
      (congrArg (fun T : G →L[ℂ] G => S (T g)) (normal_isometric_output U hU R L))
  have hp := AsymptoticCoerciveNeumann.polynomial_intertwines C N M S hi n
  have hsa (g : G) : S.adjoint (S g)=g := congrArg (fun T : G →L[ℂ] G => T g) hS
  ext1 x
  have he := congrArg (fun T : G →L[ℂ] H => T (R.adjoint (U.adjoint x))) hp
  change AsymptoticCoerciveNeumann.polynomial C M n (S (R.adjoint (U.adjoint x)))=
    S (AsymptoticCoerciveNeumann.polynomial C N n (R.adjoint (U.adjoint x))) at he
  change U (R (S.adjoint (AsymptoticCoerciveNeumann.polynomial C M n (A.adjoint x))))=_
  simp only [A,adjoint_comp,adjoint_adjoint,comp_apply]
  rw [he,hsa]

#print axioms AsymptoticCoerciveNeumann.polynomial_intertwines
#print axioms normal_isometric_output
#print axioms completed_polynomial_sandwich

end AsymptoticObservation
