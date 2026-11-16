module

public import AsymptoticL2MultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Actual bounded scalar multipliers commute on L2. -/
theorem l2Multipliers_commute (c d : α → ℂ)
    (hc : AEStronglyMeasurable c μ) (hd : AEStronglyMeasurable d μ)
    {C D : ℝ} (hC : ∀ᵐ x ∂μ, ‖c x‖≤C) (hD : ∀ᵐ x ∂μ, ‖d x‖≤D) :
    Commute (AsymptoticL2Multiplier.operator c hc hC) (AsymptoticL2Multiplier.operator d hd hD) := by
  change AsymptoticL2Multiplier.operator c hc hC*AsymptoticL2Multiplier.operator d hd hD=
    AsymptoticL2Multiplier.operator d hd hD*AsymptoticL2Multiplier.operator c hc hC
  apply DFunLike.coe_injective
  funext f
  apply Lp.ext
  filter_upwards [AsymptoticL2Multiplier.operator_coeFn c hc hC
      (AsymptoticL2Multiplier.operator d hd hD f),
    AsymptoticL2Multiplier.operator_coeFn d hd hD
      (AsymptoticL2Multiplier.operator c hc hC f),
    AsymptoticL2Multiplier.operator_coeFn c hc hC f,
    AsymptoticL2Multiplier.operator_coeFn d hd hD f] with x hcd hdc hcf hdf
  change (AsymptoticL2Multiplier.operator c hc hC
      (AsymptoticL2Multiplier.operator d hd hD f)) x=
    (AsymptoticL2Multiplier.operator d hd hD
      (AsymptoticL2Multiplier.operator c hc hC f)) x
  rw [hcd,hdc,hcf,hdf]
  ring

theorem l2Multiplier_symmetric (c : α → ℂ) (hc : AEStronglyMeasurable c μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖c x‖≤C) (hr : ∀ᵐ x ∂μ, star (c x)=c x)
    (f g : Lp ℂ 2 μ) :
    inner ℂ (AsymptoticL2Multiplier.operator c hc hC f) g=
      inner ℂ f (AsymptoticL2Multiplier.operator c hc hC g) := by
  have hs := AsymptoticL2Multiplier.operator_adjoint c hc hC hr
  simpa only [hs] using (AsymptoticL2Multiplier.operator c hc hC).adjoint_inner_left g f

#print axioms l2Multipliers_commute
#print axioms l2Multiplier_symmetric

end QuantitativeMaass
