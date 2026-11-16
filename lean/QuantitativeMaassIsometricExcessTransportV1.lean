module

public import QuantitativeMaassHilbertSchmidtIdealV1
public import QuantitativeMaassRectangularIdealV1
public import QuantitativeMaassTerminalTranslationIsometryV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap
open scoped InnerProduct BigOperators
namespace QuantitativeMaass

variable {E F ι κ τ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Extension by an actual output isometry and its adjoint preserves energy. -/
theorem isometry_extension_energy (U : E →ₗᵢ[ℂ] F)
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    (B : E →L[ℂ] E) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    let C := U.toContinuousLinearMap.comp (B.comp U.toContinuousLinearMap.adjoint)
    Summable (fun j => ‖C (c j)‖^2) ∧ hilbertSchmidtEnergy c C=hilbertSchmidtEnergy b B := by
  obtain ⟨hs,he⟩ := adjoint_energy_eq b B hB
  have hR : Summable (fun i => ‖(U.toContinuousLinearMap.comp B.adjoint) (b i)‖^2) := by
    simpa only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,U.norm_map] using hs
  obtain ⟨hc,hcE⟩ := rectangular_adjoint_energy_eq b c (U.toContinuousLinearMap.comp B.adjoint) hR
  simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,U.norm_map] at hc hcE
  dsimp only
  simp only [hilbertSchmidtEnergy,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,U.norm_map]
  exact ⟨hc,hcE.trans he⟩

/-- The filtered orthogonal excess is preserved by the same extension;
the complement in the larger space is killed by the extended packet/filter. -/
theorem isometry_extension_filtered_excess (U : E →ₗᵢ[ℂ] F) (B L P : E →L[ℂ] E) :
    let V := U.toContinuousLinearMap
    (V.comp (B.comp V.adjoint)).comp
      ((V.comp (L.comp V.adjoint)).comp (1-V.comp (P.comp V.adjoint)))=
      V.comp (((B.comp L).comp (1-P)).comp V.adjoint) := by
  have hu (x : E) : U.toContinuousLinearMap.adjoint (U x)=x := by
    apply ext_inner_left ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact U.inner_map_map y x
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,sub_apply,one_apply_eq_self,map_sub,
    LinearIsometry.coe_toContinuousLinearMap,hu]

#print axioms rectangular_finite_adjoint_energy_le
#print axioms rectangular_adjoint_energy_le
#print axioms rectangular_adjoint_energy_eq
#print axioms isometry_extension_energy
#print axioms isometry_extension_filtered_excess
end QuantitativeMaass
