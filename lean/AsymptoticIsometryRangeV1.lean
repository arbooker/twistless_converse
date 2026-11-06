module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
@[expose] public section

namespace AsymptoticIsometryRange

open ContinuousLinearMap
open scoped InnerProduct

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

noncomputable instance range_complete (I : H →ₗᵢ[ℂ] J) : CompleteSpace I.toLinearMap.range :=
  I.isometry.isClosedEmbedding.isClosed_range.completeSpace_coe

/-- An isometric Hilbert-space embedding identifies its cogram with the
orthogonal projection onto its actual (closed) range. -/
theorem cogram (I : H →ₗᵢ[ℂ] J) :
    I.toContinuousLinearMap.comp I.toContinuousLinearMap.adjoint=I.toLinearMap.range.starProjection := by
  let V := I.toContinuousLinearMap
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨V.adjoint x,rfl⟩
  · rintro y ⟨w,rfl⟩
    change inner ℂ (x-V (V.adjoint x)) (V w)=0
    rw [← V.adjoint_inner_left,map_sub]
    have he := congrArg (fun B : H →L[ℂ] H => B (V.adjoint x)) I.adjoint_comp_self
    change V.adjoint (V (V.adjoint x))=V.adjoint x at he
    rw [he,sub_self,inner_zero_left]

#print axioms cogram

end AsymptoticIsometryRange
