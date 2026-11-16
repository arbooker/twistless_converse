module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.FiberAverage

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Pullback along a measurable map, with its actual pushforward measure. -/
def lift (μ : Measure A) (τ : A → B) (hτ : Measurable τ) :
    Lp ℂ 2 (μ.map τ) →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ τ ⟨hτ,rfl⟩

/-- The bounded fiber average is the adjoint of the isometric pullback.
Its defining measure is explicit, so no boundedness hypothesis is required. -/
def average (μ : Measure A) (τ : A → B) (hτ : Measurable τ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.map τ) :=
  (lift μ τ hτ).toContinuousLinearMap.adjoint

theorem average_pairing (μ : Measure A) (τ : A → B) (hτ : Measurable τ)
    (g : Lp ℂ 2 (μ.map τ)) (f : Lp ℂ 2 μ) :
    inner ℂ g (average μ τ hτ f)=inner ℂ (lift μ τ hτ g) f :=
  (lift μ τ hτ).toContinuousLinearMap.adjoint_inner_right g f

theorem average_lift (μ : Measure A) (τ : A → B) (hτ : Measurable τ)
    (g : Lp ℂ 2 (μ.map τ)) : average μ τ hτ (lift μ τ hτ g)=g := by
  apply ext_inner_left ℂ
  intro h
  rw [average_pairing,(lift μ τ hτ).inner_map_map]

theorem average_norm_le (μ : Measure A) (τ : A → B) (hτ : Measurable τ) :
    ‖average μ τ hτ‖≤1 := by
  rw [average,ContinuousLinearMap.adjoint.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖lift μ τ hτ f‖≤1*‖f‖
  rw [(lift μ τ hτ).norm_map,one_mul]

theorem average_apply_norm_le (μ : Measure A) (τ : A → B) (hτ : Measurable τ)
    (f : Lp ℂ 2 μ) : ‖average μ τ hτ f‖≤‖f‖ := by
  apply ((average μ τ hτ).le_opNorm f).trans
  have h := mul_le_mul_of_nonneg_right (average_norm_le μ τ hτ) (norm_nonneg f)
  simpa only [one_mul] using h

/-- Exact integral characterization of the fiber average on L2 classes. -/
theorem average_pairing_integral (μ : Measure A) (τ : A → B) (hτ : Measurable τ)
    (g : Lp ℂ 2 (μ.map τ)) (f : Lp ℂ 2 μ) :
    inner ℂ g (average μ τ hτ f)=∫ x, star (g (τ x))*f x ∂μ := by
  rw [average_pairing,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving g (show MeasurePreserving τ μ (μ.map τ) from ⟨hτ,rfl⟩)] with x hx
  change inner ℂ (lift μ τ hτ g x) (f x)=_
  rw [show lift μ τ hτ g x=g (τ x) from hx]
  simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]

#print axioms average_apply_norm_le
#print axioms average_lift
#print axioms average_pairing_integral

end QuantitativeMaass.FiberAverage
