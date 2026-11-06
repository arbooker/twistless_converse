module

public import FinitenessAllLevelFredholmReductionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFredholmReduction

open ContinuousLinearMap Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {T₀ : X →L[ℂ] X} (P : T₀.FredholmPackage)

omit [CompleteSpace X] in
theorem block_differentiableAt {T : ℂ → X →L[ℂ] X} {z : ℂ}
    (hT : DifferentiableAt ℂ T z) : DifferentiableAt ℂ (fun w => block P (T w)) z := by
  unfold block
  exact (differentiableAt_const _).clm_comp (hT.clm_comp (differentiableAt_const _))

theorem inverse_block_differentiableAt {T : ℂ → X →L[ℂ] X} {z : ℂ}
    (hT : DifferentiableAt ℂ T z) (h : (block P (T z)).IsInvertible) :
    DifferentiableAt ℂ (fun w => (block P (T w)).inverse) z := by
  have : CompleteSpace P.decDom.X₁ := P.decDom.isTopCompl.isClosed.completeSpace_coe
  have hu : IsUnit ((P.equiv.symm : P.decCodom.X₁ →L[ℂ] P.decDom.X₁) ∘L block P (T z)) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr (P.equiv.symm.bijective.comp h.bijective)
  simp_rw [ContinuousLinearMap.inverse_eq_ringInverse P.equiv]
  exact (((differentiableAt_const _).clm_comp (block_differentiableAt P hT)).inverse hu).clm_comp
    (differentiableAt_const _)

theorem lift_differentiableAt {T : ℂ → X →L[ℂ] X} {z : ℂ}
    (hT : DifferentiableAt ℂ T z) (h : (block P (T z)).IsInvertible) :
    DifferentiableAt ℂ (fun w => lift P (T w)) z := by
  have hB : DifferentiableAt ℂ (fun w => offBlock P (T w)) z :=
    (differentiableAt_const _).clm_comp (hT.clm_comp (differentiableAt_const _))
  have hJ : DifferentiableAt ℂ (fun w =>
      P.decDom.X₁.subtypeL ∘L (block P (T w)).inverse ∘L offBlock P (T w)) z :=
    (differentiableAt_const _).clm_comp ((inverse_block_differentiableAt P hT h).clm_comp hB)
  unfold lift
  exact DifferentiableAt.sub (𝕜 := ℂ) (F := P.decDom.X₀ →L[ℂ] X)
    (differentiableAt_const _) hJ

theorem matrix_differentiableAt {T : ℂ → X →L[ℂ] X} {z : ℂ}
    (hT : DifferentiableAt ℂ T z) (h : (block P (T z)).IsInvertible) :
    DifferentiableAt ℂ (fun w => matrix P (T w)) z := by
  exact (differentiableAt_const _).clm_comp (hT.clm_comp (lift_differentiableAt P hT h))

/-- A common open neighborhood with a holomorphic reconstruction map and
a finite-dimensional holomorphic obstruction matrix. The equivalence is
exact for every Banach vector, not only for known original solutions. -/
theorem local_reduction (T : ℂ → X →L[ℂ] X) (hT : Differentiable ℂ T) {z : ℂ}
    (h₀ : T z = T₀) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      AnalyticOnNhd ℂ (fun w => lift P (T w)) U ∧
      AnalyticOnNhd ℂ (fun w => matrix P (T w)) U ∧
      ∀ w ∈ U, ∀ x : X,
        T w x = 0 ↔ ∃ v : P.decDom.X₀, matrix P (T w) v = 0 ∧ x = lift P (T w) v := by
  obtain ⟨U, hU, ho, hz⟩ := mem_nhds_iff.mp (eventually_block P T (hT z).continuousAt h₀)
  have : CompleteSpace P.decCodom.X₀ := P.decCodom.isTopCompl.isClosed'.completeSpace_coe
  refine ⟨U, ho, hz, ?_, ?_, fun w hw x => kernel_iff P _ (hU hw) x⟩
  · exact DifferentiableOn.analyticOnNhd (fun w hw => (lift_differentiableAt P (hT w) (hU hw)).differentiableWithinAt
      : DifferentiableOn ℂ (fun w => lift P (T w)) U) ho
  · exact DifferentiableOn.analyticOnNhd (fun w hw => (matrix_differentiableAt P (hT w) (hU hw)).differentiableWithinAt
      : DifferentiableOn ℂ (fun w => matrix P (T w)) U) ho

#print axioms inverse_block_differentiableAt
#print axioms lift_differentiableAt
#print axioms matrix_differentiableAt
#print axioms local_reduction

end FinitenessAllLevelFredholmReduction
