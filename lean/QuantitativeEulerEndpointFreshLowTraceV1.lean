module

public import QuantitativeSpectralFreshStepV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open MeasureTheory ContinuousLinearMap InnerProductSpace AsymptoticRegularTrace AsymptoticObservationStack
open AsymptoticPolarIsometry AsymptoticMixing AsymptoticSubgroupSupport
open QuantitativeSpectralCutPolar QuantitativeSpectralCornerCutRow QuantitativeSpectralFreshStep
open QuantitativeSpectralFreshMixing QuantitativeSpectralObservability QuantitativeSpectralStepTrace
open scoped lp ENNReal

variable {G α ι : Type*} [Group G] [Countable G] [Fintype ι]
  [MeasurableSpace α] [MulAction G α]

/-- Fresh mixing only needs a bound on the trace of the actual compressed
low space. This permits a proved geometric tail cost in the target. -/
theorem fresh_step_of_low_trace (μ : Measure α)
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (S : Subgroup G) (a : ι → G) (ha : ∀ i j, i ≠ j → a j * (a i)⁻¹ ∉ S)
    (hι : 0 < Fintype.card ι)
    (P : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x, CompleteSpace (P x)]
    (hmP : ∀ g h, Measurable (fun x => matrix (P x).starProjection g h))
    (hcP : Covariant (fun x => (P x).starProjection))
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h, Measurable (fun x => matrix (L x i) g h))
    (hc : ∀ i, Covariant (fun x => L x i))
    (hL : ∀ x i, Supported S (L x i))
    (hP : ∀ x i, (L x i).comp (P x).starProjection = L x i)
    (M : ℝ) (hM : ∀ x, ‖stack (L x)‖ ≤ M)
    (hf : trace μ (fun x => (P x).starProjection) < ∞)
    {c d theta : ℝ} (hcpos : 0 < c) (hd : 0 < d)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hscale : d^2 = c^2*theta/(2*(Fintype.card ι)))
    (target : ℝ)
    (hlow : (trace μ (fun x =>
      (nextSpace (P x) (absolute (stack (L x))) c).starProjection)).toReal≤target) :
    ((1-theta)/(Fintype.card ι)) *
      ((trace μ (fun x => (P x).starProjection)).toReal -
        target) ≤
      (trace μ (fun x => (P x).starProjection)).toReal -
        (trace μ (fun x => (nextSpace (P x) (normalizedMixed a (L x)) d).starProjection)).toReal := by
  let B := fun x => absolute (stack (L x))
  have hb := stack_absolute_regular L hm hc M hM
  have hBn (x : α) : ‖B x‖ ≤ M := by
    dsimp only [B]
    rw [absolute_opNorm]
    exact hM x
  have hBP (x : α) : (B x).comp (P x).starProjection = B x :=
    absolute_comp_projection (P x) (stack (L x)) (stack_comp_projection (P x) (L x) (hP x))
  have htr := removedSpace_trace μ P B hmP hcP hb.1 hb.2 M hBn hcpos hf
  have he (x : α) : removedSpace (P x) (B x) c = cutSpace (stack (L x)) c := by
    unfold removedSpace restricted cutSpace
    change QuantitativeSpectralCut.highAt (star ((B x).comp (P x).starProjection) *
      ((B x).comp (P x).starProjection)) (c^2) = _
    rw [hBP]
    congr 1
    exact absolute_gram (stack (L x))
  have heP (x : α) : (removedSpace (P x) (B x) c).starProjection =
      (cutSpace (stack (L x)) c).starProjection := starProjection_congr _ _ (he x)
  simp only [heP] at htr
  have hdetect : (trace μ (fun x => (P x).starProjection)).toReal -
        target ≤
      (trace μ (fun x => (cutSpace (stack (L x)) c).starProjection)).toReal := by
    linarith [hlow]
  have hfresh := fresh_mixed_high_trace μ hmp S a ha hι P L hm hc hL hP M hM hf hcpos htheta
  have hA := normalizedMixed_regular a L hm hc
  have hAn (x : α) : ‖normalizedMixed a (L x)‖ ≤ M := (normalizedMixed_norm a (L x)).trans (hM x)
  have hAP (x : α) : (normalizedMixed a (L x)).comp (P x).starProjection =
      normalizedMixed a (L x) := normalizedMixed_comp_projection (P x) a (L x) (hP x)
  have hremove := removedSpace_trace μ P (fun x => normalizedMixed a (L x)) hmP hcP
    hA.1 hA.2 M hAn hd hf
  have heA (x : α) : (removedSpace (P x) (normalizedMixed a (L x)) d).starProjection =
      (QuantitativeSpectralCut.highAt ((normalizedMixed a (L x)).adjoint.comp
        (normalizedMixed a (L x))) (c^2*theta/(2*(Fintype.card ι)))).starProjection := by
    unfold removedSpace restricted
    change (QuantitativeSpectralCut.highAt (star ((normalizedMixed a (L x)).comp (P x).starProjection) *
      ((normalizedMixed a (L x)).comp (P x).starProjection)) (d^2)).starProjection = _
    rw [hAP, hscale]
    rfl
  simp only [heA] at hremove
  rw [hremove] at hfresh
  have hw : 0 ≤ (1-theta)/(Fintype.card ι:ℝ) := div_nonneg (sub_nonneg.mpr htheta1) (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_left hdetect hw
  exact hh.trans (by simpa only [div_mul_eq_mul_div] using hfresh)

#print axioms absolute_comp_projection
#print axioms fresh_step_of_low_trace
end QuantitativeEulerEndpointPrepared
