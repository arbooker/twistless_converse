module

public import AsymptoticRegularTraceSandwichV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped lp ENNReal

variable {G α : Type*} [Group G] [MeasurableSpace α]

theorem trace_sandwich_le_range_gram (μ : Measure α)
    (F I : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hi : ∀ x,‖I x‖≤1) :
    trace μ (fun x => (F x).comp ((I x).comp (F x).adjoint))≤
      trace μ (fun x => (F x).comp (F x).adjoint) := by
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  have he : matrix ((F x).comp ((I x).comp (F x).adjoint)) 1 1=
      ⟪(F x).adjoint (delta 1),I x ((F x).adjoint (delta 1))⟫_ℂ := by
    simpa only [adjoint_adjoint,comp_apply] using matrix_cross (F x).adjoint ((I x).comp (F x).adjoint) 1
  have hg := matrix_gram (F x).adjoint 1
  simp only [adjoint_adjoint] at hg
  rw [he,hg]
  have hn : ‖I x ((F x).adjoint (delta 1))‖≤‖(F x).adjoint (delta 1)‖ := by
    simpa only [one_mul] using (I x).le_of_opNorm_le (hi x) ((F x).adjoint (delta 1))
  have hc := re_inner_le_norm (𝕜:=ℂ) ((F x).adjoint (delta 1)) (I x ((F x).adjoint (delta 1)))
  change (⟪(F x).adjoint (delta 1),I x ((F x).adjoint (delta 1))⟫_ℂ).re≤
    ‖(F x).adjoint (delta 1)‖*‖I x ((F x).adjoint (delta 1))‖ at hc
  apply hc.trans
  simpa only [pow_two] using mul_le_mul_of_nonneg_left hn (norm_nonneg ((F x).adjoint (delta 1)))

#print axioms trace_sandwich_le_range_gram

end AsymptoticRegularTrace
