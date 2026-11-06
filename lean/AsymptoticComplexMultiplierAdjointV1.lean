module

public import AsymptoticL2MultiplierV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticL2Multiplier

open MeasureTheory Filter ContinuousLinearMap
open scoped ComplexConjugate InnerProduct

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem operator_conj_adjoint (c : α → ℂ) (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ,‖c x‖≤C) :
    (operator c hc hC).adjoint=
      operator (C := C) (fun x => conj (c x)) (Complex.continuous_conj.comp_aestronglyMeasurable hc)
        (hC.mono (fun x hx => by simpa only [RCLike.norm_conj] using hx)) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_coeFn c hc hC g,
    operator_coeFn (C := C) (fun x => conj (c x)) (Complex.continuous_conj.comp_aestronglyMeasurable hc)
      (hC.mono (fun x hx => by simpa only [RCLike.norm_conj] using hx)) f] with x hg hf
  simp only [RCLike.inner_apply]
  rw [hf,hg]
  simp only [star_mul,starRingEnd_apply,star_star]
  ring

#print axioms operator_conj_adjoint

end AsymptoticL2Multiplier
