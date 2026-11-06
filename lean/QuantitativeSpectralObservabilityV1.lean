module

public import QuantitativeSpectralRegularCornerStepV1
public import AsymptoticRegularEmbeddingTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open MeasureTheory ContinuousLinearMap InnerProductSpace AsymptoticRegularTrace
open AsymptoticPolarIsometry QuantitativeSpectralCut QuantitativeSpectralCutRow
open QuantitativeSpectralCornerCutRow QuantitativeSpectralRegularCornerStep
open scoped lp ENNReal InnerProduct

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete norm observability inequality makes the target sampling map
injective on the actual low-residual survivor. -/
theorem observable_low_injective (P : Submodule ℂ H) [CompleteSpace P]
    (B C : H →L[ℂ] H) {c K : ℝ} (hK : 0 ≤ K) (hsmall : K*c^2 < 1)
    (hobs : ∀ v ∈ P, ‖v‖^2 ≤ K*(‖B v‖^2+‖C v‖^2))
    {v : H} (hv : v ∈ nextSpace P B c) (hz : C v = 0) : v = 0 := by
  have hp := nextSpace_le P B c hv
  have he : restricted P B v = B v := by
    change B (P.starProjection v) = B v
    rw [P.starProjection_eq_self_iff.mpr hp]
  have hl := quadratic_le_on_lowAt _ (IsSelfAdjoint.star_mul_self (restricted P B))
    (c^2) (nextSpace_low P B c hv)
  change (⟪((restricted P B).adjoint.comp (restricted P B)) v,v⟫_ℂ).re ≤ _ at hl
  rw [comp_apply, adjoint_inner_left] at hl
  have hquad : (⟪restricted P B v, restricted P B v⟫_ℂ).re = ‖restricted P B v‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (restricted P B v)).symm
  rw [hquad, he] at hl
  have ho := hobs v hp
  rw [hz, norm_zero, zero_pow (by decide : (2:ℕ)≠0), add_zero] at ho
  have hh := ho.trans (mul_le_mul_of_nonneg_left hl hK)
  have hn : ‖v‖^2 ≤ 0 := le_of_not_gt (fun hpos => by
    have hstrict := mul_lt_mul_of_pos_right hsmall hpos
    rw [one_mul] at hstrict
    exact (not_lt_of_ge hh) (by simpa only [mul_assoc] using hstrict))
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg v]
end Hilbert

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Quantitative detector from an actual norm inequality, rather than an
assumed spectral dimension inequality. Concrete geometric applications must
supply the sampling map and prove the displayed observability estimate. -/
theorem observable_low_trace (μ : Measure α)
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (P V : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x, CompleteSpace (P x)] [∀ x, CompleteSpace (V x)]
    (hmP : ∀ g h, Measurable (fun x => matrix (P x).starProjection g h))
    (hcP : Covariant (fun x => (P x).starProjection))
    (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmB : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hcB : Covariant B)
    (hmC : ∀ g h, Measurable (fun x => matrix (C x) g h)) (hcC : Covariant C)
    (M N : ℝ) (hM : ∀ x, ‖B x‖ ≤ M) (hN : ∀ x, ‖C x‖ ≤ N)
    {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hsmall : K*c^2 < 1)
    (hobs : ∀ x v, v ∈ P x → ‖v‖^2 ≤ K*(‖B x v‖^2+‖C x v‖^2))
    (hmap : ∀ x v, v ∈ P x → C x v ∈ V x) :
    trace μ (fun x => (nextSpace (P x) (B x) c).starProjection) ≤
      trace μ (fun x => (V x).starProjection) := by
  have hr := (step_regular P B hmP hcP hmB hcB M hM c hc).1
  exact trace_le_of_injective_map μ hmp _ V hr.1 hr.2 C hmC hcC N hN
    (fun x _ hv hz => observable_low_injective (P x) (B x) (C x) hK hsmall (hobs x) hv hz)
    (fun x _ hv => hmap x _ (nextSpace_le (P x) (B x) c hv))

#print axioms observable_low_injective
#print axioms observable_low_trace

end QuantitativeSpectralObservability
