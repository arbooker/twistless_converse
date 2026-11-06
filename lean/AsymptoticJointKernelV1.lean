module

public import AsymptoticQuotientEquivarianceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticJointKernel

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The positive sum of two Gram operators has exactly their common
kernel, including in infinite-dimensional Hilbert space. -/
theorem mem_ker_gram_add (B C : E →L[ℂ] E) (v : E) :
    v∈((B.adjoint.comp B)+(C.adjoint.comp C)).ker ↔ B v=0 ∧ C v=0 := by
  change (B.adjoint.comp B+C.adjoint.comp C) v=0 ↔ _
  constructor
  · intro hz
    have he := congrArg (fun w : E => (⟪v,w⟫_ℂ).re) hz
    change (⟪v,B.adjoint (B v)+C.adjoint (C v)⟫_ℂ).re=(⟪v,0⟫_ℂ).re at he
    rw [inner_add_right,Complex.add_re,adjoint_inner_right,adjoint_inner_right,
      inner_zero_right,Complex.zero_re] at he
    have hbq : (⟪B v,B v⟫_ℂ).re=‖B v‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) (B v)
    have hcq : (⟪C v,C v⟫_ℂ).re=‖C v‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) (C v)
    rw [hbq,hcq] at he
    have hb : ‖B v‖=0 := by nlinarith [sq_nonneg ‖C v‖,norm_nonneg (B v)]
    have hc : ‖C v‖=0 := by nlinarith [sq_nonneg ‖B v‖,norm_nonneg (C v)]
    exact ⟨norm_eq_zero.mp hb,norm_eq_zero.mp hc⟩
  · rintro ⟨hb,hc⟩
    simp only [add_apply,comp_apply,hb,hc,map_zero,add_zero]

theorem ker_gram_add (B C : E →L[ℂ] E) :
    ((B.adjoint.comp B)+(C.adjoint.comp C)).ker=B.ker⊓C.ker := by
  ext v
  exact mem_ker_gram_add B C v

#print axioms mem_ker_gram_add
#print axioms ker_gram_add

end AsymptoticJointKernel
