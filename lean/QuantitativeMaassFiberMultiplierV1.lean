module

public import QuantitativeMaassFiberAverageV1
public import AsymptoticL2MultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Filter

namespace QuantitativeMaass.FiberAverage

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The actual L2 pullback intertwines bounded measurable scalar multipliers. -/
theorem lift_multiplier (μ : Measure X) (τ : X → Y) (hτ : Measurable τ)
    (c : Y → ℂ) (hc : Measurable c) (C : ℝ) (hC : ∀ y,‖c y‖≤C)
    (f : Lp ℂ 2 (μ.map τ)) :
    lift μ τ hτ (AsymptoticL2Multiplier.operator c hc.aestronglyMeasurable
      (Eventually.of_forall hC) f)=
    AsymptoticL2Multiplier.operator (fun x => c (τ x)) (hc.comp hτ).aestronglyMeasurable
      (Eventually.of_forall (fun x => hC (τ x))) (lift μ τ hτ f) := by
  let H := AsymptoticL2Multiplier.operator (μ:=μ.map τ) c hc.aestronglyMeasurable (Eventually.of_forall hC)
  have hm : MeasurePreserving τ μ (μ.map τ) := ⟨hτ,rfl⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (H f) hm,
    hm.quasiMeasurePreserving.ae (AsymptoticL2Multiplier.operator_coeFn c hc.aestronglyMeasurable
      (Eventually.of_forall hC) f),
    AsymptoticL2Multiplier.operator_coeFn (fun x => c (τ x)) (hc.comp hτ).aestronglyMeasurable
      (Eventually.of_forall (fun x => hC (τ x))) (lift μ τ hτ f),
    Lp.coeFn_compMeasurePreserving f hm] with x h1 h2 h3 h4
  change lift μ τ hτ (H f) x=(AsymptoticL2Multiplier.operator _ _ _ (lift μ τ hτ f)) x
  change lift μ τ hτ (H f) x=H f (τ x) at h1
  change H f (τ x)=c (τ x)*f (τ x) at h2
  change lift μ τ hτ f x=f (τ x) at h4
  rw [h1,h2,h3,h4]

/-- A real height multiplier commutes through the bounded fiber average.
This includes arbitrary measurable height cutoffs, not just smooth ones. -/
theorem average_multiplier (μ : Measure X) (τ : X → Y) (hτ : Measurable τ)
    (c : Y → ℂ) (hc : Measurable c) (C : ℝ) (hC : ∀ y,‖c y‖≤C)
    (hr : ∀ y,star (c y)=c y) (f : Lp ℂ 2 μ) :
    average μ τ hτ
      (AsymptoticL2Multiplier.operator (fun x => c (τ x)) (hc.comp hτ).aestronglyMeasurable
        (Eventually.of_forall (fun x => hC (τ x))) f)=
    AsymptoticL2Multiplier.operator c hc.aestronglyMeasurable (Eventually.of_forall hC)
      (average μ τ hτ f) := by
  let H := AsymptoticL2Multiplier.operator (μ:=μ.map τ) c hc.aestronglyMeasurable (Eventually.of_forall hC)
  let G := AsymptoticL2Multiplier.operator (μ:=μ) (fun x => c (τ x)) (hc.comp hτ).aestronglyMeasurable
    (Eventually.of_forall (fun x => hC (τ x)))
  have he : (lift μ τ hτ).toContinuousLinearMap.comp H=G.comp (lift μ τ hτ).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro g
    exact lift_multiplier μ τ hτ c hc C hC g
  have hH : H.adjoint=H := AsymptoticL2Multiplier.operator_adjoint c hc.aestronglyMeasurable
    (Eventually.of_forall hC) (Eventually.of_forall hr)
  have hG : G.adjoint=G := AsymptoticL2Multiplier.operator_adjoint _ (hc.comp hτ).aestronglyMeasurable
    (Eventually.of_forall (fun x => hC (τ x))) (Eventually.of_forall (fun x => hr (τ x)))
  have hh := congrArg ContinuousLinearMap.adjoint he
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,hH,hG] at hh
  exact (congrArg (fun T => T f) hh).symm

#print axioms lift_multiplier
#print axioms average_multiplier

end QuantitativeMaass.FiberAverage
