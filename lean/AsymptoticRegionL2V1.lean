module

public import AsymptoticL2MultiplierV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegionL2

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

omit [MeasurableSpace α] in
theorem indicator_norm (s : Set α) (x : α) : ‖s.indicator (fun _ => (1 : ℂ)) x‖≤1 := by
  classical
  by_cases hx : x∈s <;> simp [hx]

/-- Orthogonal restriction, extended by zero, on an actual L² space. -/
noncomputable def projection (s : Set α) (hs : MeasurableSet s) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  AsymptoticL2Multiplier.operator (s.indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator hs).aestronglyMeasurable
    (Filter.Eventually.of_forall (indicator_norm s))

theorem projection_coeFn (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    projection μ s hs f =ᵐ[μ] s.indicator f := by
  have hh := AsymptoticL2Multiplier.operator_coeFn (s.indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator hs).aestronglyMeasurable
    (Filter.Eventually.of_forall (indicator_norm s)) f
  filter_upwards [hh] with x hx
  exact hx.trans (by classical by_cases hsx : x∈s <;> simp [hsx])

theorem projection_norm_le (s : Set α) (hs : MeasurableSet s) : ‖projection μ s hs‖≤1 :=
  AsymptoticL2Multiplier.operator_norm_le _ _ zero_le_one _

theorem projection_idempotent (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    projection μ s hs (projection μ s hs f)=projection μ s hs f := by
  apply Lp.ext
  filter_upwards [projection_coeFn μ s hs (projection μ s hs f),projection_coeFn μ s hs f]
    with x hx hf
  classical
  by_cases hxs : x∈s <;> simp [hxs] at hx hf ⊢ <;> simp [hx,hf]

theorem projection_adjoint (s : Set α) (hs : MeasurableSet s) :
    (projection μ s hs).adjoint=projection μ s hs :=
  AsymptoticL2Multiplier.operator_adjoint _ _ _ (Filter.Eventually.of_forall (by
    intro x
    classical
    by_cases hx : x∈s <;> simp [hx]))

theorem projection_eq_self_iff (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    projection μ s hs f=f ↔ ∀ᵐ x ∂μ, x∉s → f x=0 := by
  constructor
  · intro hf
    have he := projection_coeFn μ s hs f
    rw [hf] at he
    filter_upwards [he] with x hx hxs
    simpa [hxs] using hx
  · intro hf
    apply Lp.ext
    filter_upwards [projection_coeFn μ s hs f,hf] with x hx hfx
    classical
    by_cases hxs : x∈s
    · simpa [hxs] using hx
    · simpa [hxs,hfx hxs] using hx

theorem projection_eq_zero_iff (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    projection μ s hs f=0 ↔ ∀ᵐ x ∂μ, x∈s → f x=0 := by
  constructor
  · intro hf
    have he := projection_coeFn μ s hs f
    rw [hf] at he
    filter_upwards [he,Lp.coeFn_zero ℂ 2 μ] with x hx hz hxs
    change ((0 : Lp ℂ 2 μ) : α → ℂ) x=0 at hz
    rw [hz] at hx
    simpa [hxs,hz] using hx.symm
  · intro hf
    apply Lp.ext
    filter_upwards [projection_coeFn μ s hs f,hf,Lp.coeFn_zero ℂ 2 μ] with x hx hfx hz
    change ((0 : Lp ℂ 2 μ) : α → ℂ) x=0 at hz
    rw [hz]
    classical
    by_cases hxs : x∈s <;> simp [hxs,hfx] at hx ⊢ <;> exact hx

/-- The terminal data space is a closed subspace of hyperbolic L²,
defined as the fixed space of the actual terminal restriction. -/
noncomputable def Space (s : Set α) (hs : MeasurableSet s) : Submodule ℂ (Lp ℂ 2 μ) :=
  (projection μ s hs-ContinuousLinearMap.id ℂ _).ker

theorem mem_space (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    f∈Space μ s hs ↔ projection μ s hs f=f := by
  change projection μ s hs f-f=0 ↔ _
  exact sub_eq_zero

instance space_complete (s : Set α) (hs : MeasurableSet s) : CompleteSpace (Space μ s hs) :=
  (projection μ s hs-ContinuousLinearMap.id ℂ _).isClosed_ker.completeSpace_coe

noncomputable def restrict (s : Set α) (hs : MeasurableSet s) : Lp ℂ 2 μ →L[ℂ] Space μ s hs :=
  (projection μ s hs).codRestrict (Space μ s hs) (fun f =>
    (mem_space μ s hs _).mpr (projection_idempotent μ s hs f))

theorem restrict_coe (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    ((restrict μ s hs f : Space μ s hs) : Lp ℂ 2 μ)=projection μ s hs f := rfl

#print axioms projection_norm_le
#print axioms projection_adjoint
#print axioms projection_eq_self_iff
#print axioms projection_eq_zero_iff
#print axioms restrict

end AsymptoticRegionL2
