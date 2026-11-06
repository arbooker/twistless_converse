module

public import AsymptoticFiberProjectionV1
public import AsymptoticIsometryRangeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiberIsometry

open ContinuousLinearMap AsymptoticRegularTrace
open scoped lp ComplexConjugate

variable {ι κ : Type*} (p : ι → κ) (r : ι → ℂ)
variable (hr : ∀ y,HasSum (fun i : {i // p i=y} => ‖r i.val‖^2) 1)

/-- Matrix coefficients of an operator transported by the normalized
fibre isometry, including the actual source and target amplitudes. -/
theorem compression_matrix (B : ℓ²(κ,ℂ) →L[ℂ] ℓ²(κ,ℂ)) (i j : ι) :
    ((operator p r hr).comp B |>.comp (operator p r hr).adjoint) (delta j) i=
      r i*conj (r j)*(B (delta (p j)) (p i)) := by
  rw [comp_apply,comp_apply,adjoint_delta,map_smul,operator_apply]
  change r i*(conj (r j)*B (delta (p j)) (p i))=_
  ring

#print axioms compression_matrix

end AsymptoticFiberIsometry

namespace AsymptoticIsometryRange

open ContinuousLinearMap

variable {H J K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem cogram_comp (I : J →ₗᵢ[ℂ] K) (U : H →ₗᵢ[ℂ] J) :
    (I.comp U).toLinearMap.range.starProjection=
      (I.toContinuousLinearMap.comp U.toLinearMap.range.starProjection).comp
        I.toContinuousLinearMap.adjoint := by
  rw [← cogram,← cogram]
  change (I.toContinuousLinearMap.comp U.toContinuousLinearMap).comp
    (I.toContinuousLinearMap.comp U.toContinuousLinearMap).adjoint=_
  rw [adjoint_comp]
  simp only [comp_assoc]

#print axioms cogram_comp

end AsymptoticIsometryRange
