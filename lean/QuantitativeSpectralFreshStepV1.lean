module

public import QuantitativeSpectralFreshMixingV1
public import QuantitativeSpectralObservabilityV1
public import QuantitativeSpectralStepTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralFreshStep

open MeasureTheory ContinuousLinearMap InnerProductSpace AsymptoticRegularTrace AsymptoticObservationStack
open AsymptoticPolarIsometry AsymptoticMixing AsymptoticSubgroupSupport
open QuantitativeSpectralCutPolar QuantitativeSpectralCornerCutRow
open QuantitativeSpectralFreshMixing QuantitativeSpectralObservability QuantitativeSpectralStepTrace
open scoped lp ENNReal

section Hilbert
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem absolute_comp_projection (P : Submodule ℂ H) [CompleteSpace P]
    (X : H →L[ℂ] J) (hX : X.comp P.starProjection = X) :
    (absolute X).comp P.starProjection = absolute X := by
  apply ContinuousLinearMap.ext
  intro v
  have hz : X (v-P.starProjection v) = 0 := by
    rw [map_sub, show X (P.starProjection v) = X v from congrArg (fun T : H →L[ℂ] J => T v) hX,
      sub_self]
  have hn : absolute X (v-P.starProjection v) = 0 := by
    apply norm_eq_zero.mp
    rw [← absolute_norm, hz, norm_zero]
  rw [map_sub, sub_eq_zero] at hn
  exact hn.symm

end Hilbert

variable {G α ι : Type*} [Group G] [Countable G] [Fintype ι]
  [MeasurableSpace α] [MulAction G α]

/-- One actual fresh spectral deflation step, derived from geometric norm
observability, subgroup separation, and regularity of the original rows.
The conclusion is a trace decrease of the constructed survivor, not an
assumed dimension-loss hypothesis. -/
theorem observable_fresh_step (μ : Measure α)
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (S : Subgroup G) (a : ι → G) (ha : ∀ i j, i ≠ j → a j * (a i)⁻¹ ∉ S)
    (hι : 0 < Fintype.card ι)
    (P V : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x, CompleteSpace (P x)] [∀ x, CompleteSpace (V x)]
    (hmP : ∀ g h, Measurable (fun x => matrix (P x).starProjection g h))
    (hcP : Covariant (fun x => (P x).starProjection))
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h, Measurable (fun x => matrix (L x i) g h))
    (hc : ∀ i, Covariant (fun x => L x i))
    (hL : ∀ x i, Supported S (L x i))
    (hP : ∀ x i, (L x i).comp (P x).starProjection = L x i)
    (C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmC : ∀ g h, Measurable (fun x => matrix (C x) g h)) (hcC : Covariant C)
    (M N : ℝ) (hM : ∀ x, ‖stack (L x)‖ ≤ M) (hN : ∀ x, ‖C x‖ ≤ N)
    (hf : trace μ (fun x => (P x).starProjection) < ∞)
    (hfV : trace μ (fun x => (V x).starProjection) < ∞)
    {c d K theta : ℝ} (hcpos : 0 < c) (hd : 0 < d)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hscale : d^2 = c^2*theta/(2*(Fintype.card ι)))
    (hK : 0 ≤ K) (hsmall : K*c^2 < 1)
    (hobs : ∀ x v, v ∈ P x → ‖v‖^2 ≤ K*(‖stack (L x) v‖^2+‖C x v‖^2))
    (hmap : ∀ x v, v ∈ P x → C x v ∈ V x) :
    ((1-theta)/(Fintype.card ι)) *
      ((trace μ (fun x => (P x).starProjection)).toReal -
        (trace μ (fun x => (V x).starProjection)).toReal) ≤
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
  have hob (x : α) (v : ℓ²(G,ℂ)) (hv : v ∈ P x) :
      ‖v‖^2 ≤ K*(‖B x v‖^2+‖C x v‖^2) := by
    change ‖v‖^2 ≤ K*(‖absolute (stack (L x)) v‖^2+‖C x v‖^2)
    rw [← absolute_norm]
    exact hobs x v hv
  have hl := observable_low_trace μ hmp P V hmP hcP B C hb.1 hb.2 hmC hcC
    M N hBn hN hcpos hK hsmall hob hmap
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
        (trace μ (fun x => (V x).starProjection)).toReal ≤
      (trace μ (fun x => (cutSpace (stack (L x)) c).starProjection)).toReal := by
    have hh := ENNReal.toReal_mono hfV.ne hl
    linarith
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
#print axioms observable_fresh_step

end QuantitativeSpectralFreshStep
