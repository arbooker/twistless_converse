module

public import AsymptoticFiberIsometryV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiberIsometry

open AsymptoticRegularTrace ContinuousLinearMap InnerProductSpace
open scoped lp InnerProduct ComplexConjugate Classical

variable {ι κ : Type*} (p : ι → κ) (r : ι → ℂ)
variable (hr : ∀ y,HasSum (fun i : {i // p i=y} => ‖r i.val‖^2) 1)

noncomputable def operator : ℓ²(κ,ℂ) →L[ℂ] ℓ²(ι,ℂ) :=
  (isometry p r hr).toContinuousLinearMap

theorem operator_apply (f : ℓ²(κ,ℂ)) (i : ι) : operator p r hr f i=r i*f (p i) := rfl

theorem adjoint_delta (i : ι) :
    (operator p r hr).adjoint (delta i)=conj (r i) • delta (p i) := by
  apply ext_inner_right ℂ
  intro f
  rw [adjoint_inner_left,inner_smul_left,delta_inner,delta_inner,operator_apply]
  simp

theorem adjoint_comp : (operator p r hr).adjoint.comp (operator p r hr)=1 :=
  (norm_map_iff_adjoint_comp_self _).mp (linear_norm p r hr)

/-- The matrix of the orthogonal range projection has rank one on
each fibre and vanishes between distinct fibres. -/
theorem projection_apply_delta (i j : ι) :
    ((operator p r hr).comp (operator p r hr).adjoint) (delta j) i=
      if p i=p j then r i*conj (r j) else 0 := by
  classical
  rw [comp_apply,adjoint_delta,operator_apply]
  change r i*(conj (r j)*delta (p j) (p i))=_
  by_cases hij : p i=p j
  · simp [delta,hij]
  · simp [delta,hij]

theorem projection_diagonal (i : ι) :
    (((operator p r hr).comp (operator p r hr).adjoint) (delta i) i).re=‖r i‖^2 := by
  rw [projection_apply_delta,ite_eq_left rfl]
  rw [Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]

noncomputable instance range_complete : CompleteSpace (operator p r hr).range :=
  (isometry p r hr).isometry.isClosedEmbedding.isClosed_range.completeSpace_coe

theorem operator_cogram : (operator p r hr).comp (operator p r hr).adjoint=
    (operator p r hr).range.starProjection := by
  let V := operator p r hr
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨V.adjoint x,rfl⟩
  · rintro y ⟨w,rfl⟩
    change ⟪x-V (V.adjoint x),V w⟫_ℂ=0
    rw [← V.adjoint_inner_left,map_sub]
    have he := congrArg (fun B : ℓ²(κ,ℂ) →L[ℂ] ℓ²(κ,ℂ) => B (V.adjoint x))
      (adjoint_comp p r hr)
    change V.adjoint (V (V.adjoint x))=V.adjoint x at he
    rw [he,sub_self,inner_zero_left]

#print axioms operator_apply
#print axioms adjoint_delta
#print axioms adjoint_comp
#print axioms projection_apply_delta
#print axioms projection_diagonal
#print axioms operator_cogram

end AsymptoticFiberIsometry
