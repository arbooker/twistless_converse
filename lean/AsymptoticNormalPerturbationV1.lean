module

public import AsymptoticRegularObservationNormalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem gram_sub_norm_le (R S : G →L[ℂ] H) :
    ‖R.adjoint.comp R-S.adjoint.comp S‖≤(‖R‖+‖S‖)*‖R-S‖ := by
  have he : R.adjoint.comp R-S.adjoint.comp S=
      R.adjoint.comp (R-S)+(R.adjoint-S.adjoint).comp S := by
    apply ContinuousLinearMap.ext
    intro g
    simp only [sub_apply,add_apply,comp_apply,map_sub]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)).trans_eq
  rw [← map_sub,ContinuousLinearMap.adjoint.norm_map,ContinuousLinearMap.adjoint.norm_map]
  ring

theorem normal_sub_norm_le (R S : G →L[ℂ] H) (L : H →L[ℂ] J) :
    ‖normal R L-normal S L‖≤(‖R‖+‖S‖)*(1+‖L‖^2)*‖R-S‖ := by
  have he : normal R L-normal S L=
      (R.adjoint.comp R-S.adjoint.comp S)+
        ((L.comp R).adjoint.comp (L.comp R)-(L.comp S).adjoint.comp (L.comp S)) := by
    unfold normal
    abel
  have hd : ‖L.comp R-L.comp S‖≤‖L‖*‖R-S‖ := by
    rw [← comp_sub]
    exact opNorm_comp_le _ _
  have hs : ‖L.comp R‖+‖L.comp S‖≤‖L‖*(‖R‖+‖S‖) := by
    simpa only [mul_add] using add_le_add (opNorm_comp_le L R) (opNorm_comp_le L S)
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (gram_sub_norm_le R S) (gram_sub_norm_le (L.comp R) (L.comp S))).trans
  apply (add_le_add le_rfl (mul_le_mul hs hd (norm_nonneg _) (by positivity))).trans_eq
  ring

theorem completedNormal_sub_norm_le (P R S : H →L[ℂ] H) (L : H →L[ℂ] J) :
    ‖completedNormal P R L-completedNormal P S L‖≤(‖R‖+‖S‖)*(1+‖L‖^2)*‖R-S‖ := by
  have he : completedNormal P R L-completedNormal P S L=normal R L-normal S L := by
    unfold completedNormal
    abel
  rw [he]
  exact normal_sub_norm_le R S L

omit [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] [CompleteSpace H] in
theorem inverse_sub_identity (M N I J : H →L[ℂ] H) (hI : I.comp M=1) (hJ : N.comp J=1) :
    I-J=I.comp ((N-M).comp J) := by
  apply ContinuousLinearMap.ext
  intro x
  have hi : I (M (J x))=J x := congrArg (fun T : H →L[ℂ] H => T (J x)) hI
  have hj : N (J x)=x := congrArg (fun T : H →L[ℂ] H => T x) hJ
  change I x-J x=I ((N-M) (J x))
  rw [sub_apply,map_sub,hj,hi]

omit [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] [CompleteSpace H] in
theorem inverse_sub_norm_le (M N I J : H →L[ℂ] H) (hI : I.comp M=1) (hJ : N.comp J=1)
    (hi : ‖I‖≤1) (hj : ‖J‖≤1) : ‖I-J‖≤‖M-N‖ := by
  rw [inverse_sub_identity M N I J hI hJ]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans
  rw [one_mul]
  apply (opNorm_comp_le _ _).trans
  simpa only [mul_one,norm_sub_rev] using mul_le_mul_of_nonneg_left hj (norm_nonneg (N-M))

#print axioms gram_sub_norm_le
#print axioms normal_sub_norm_le
#print axioms completedNormal_sub_norm_le
#print axioms inverse_sub_identity
#print axioms inverse_sub_norm_le

end AsymptoticObservation
