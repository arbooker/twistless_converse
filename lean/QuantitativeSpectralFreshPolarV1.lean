module

public import QuantitativeSpectralRegularTraceV1
public import QuantitativeSpectralCutRegularityV1
public import QuantitativeSpectralCutPolarV1
public import AsymptoticMixingRankV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralFreshPolar

open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticObservationStack
open AsymptoticPolarIsometry AsymptoticMixing AsymptoticSubgroupSupport
open QuantitativeSpectralCut QuantitativeSpectralCutRegularity QuantitativeSpectralRegularTrace
open scoped lp ENNReal

variable {G α ι : Type*} [Group G] [Countable G] [Fintype ι]
  [MeasurableSpace α] [MulAction G α]

/-- The polar mixed Gram has a genuine adjustable high cut of rooted trace
at least `(1-theta)/card` times the original stack support. All measurability,
covariance, the contraction bound, and the fresh first moment are derived
from the observation rows and subgroup separation. -/
theorem fresh_polar_high_trace (μ : Measure α) (S : Subgroup G) (a : ι → G)
    (ha : ∀ i j, i ≠ j → a j * (a i)⁻¹ ∉ S) (hι : 0 < Fintype.card ι)
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h, Measurable (fun x => matrix (L x i) g h))
    (hc : ∀ i, Covariant (fun x => L x i))
    (hL : ∀ x i, Supported S (L x i)) (M : ℝ) (hM : ∀ x, ‖stack (L x)‖ ≤ M)
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hfinite : trace μ (fun x => (stack (L x)).kerᗮ.starProjection) < ∞) :
    (1-theta) * (trace μ (fun x => (stack (L x)).kerᗮ.starProjection)).toReal /
      (Fintype.card ι : ℝ) ≤
      (trace μ (fun x => (highAt
        ((normalizedMixed a (polarRow (L x))).adjoint.comp
          (normalizedMixed a (polarRow (L x)))) (theta/(Fintype.card ι))).starProjection)).toReal := by
  let V := fun x => normalizedMixed a (polarRow (L x))
  let E := fun x => (V x).adjoint.comp (V x)
  have hp := stack_polarRow_regular L hm hc M hM
  have hv := normalizedMixed_regular a (fun x => polarRow (L x))
    (fun i => (hp i).1) (fun i => (hp i).2)
  have he := And.intro
    (matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hv.1) hv.1)
    (covariant_comp _ _ (covariant_adjoint _ hv.2) hv.2)
  have hsa (x : α) : IsSelfAdjoint (E x) := by
    rw [isSelfAdjoint_iff']
    simp only [E, adjoint_comp, adjoint_adjoint]
  have hnorm (x : α) : ‖E x‖ ≤ 1 := by
    dsimp only [E]
    rw [norm_adjoint_comp_self]
    have hn := normalizedMixed_polar_norm a (L x)
    have hn0 := norm_nonneg (V x)
    change ‖V x‖ ≤ 1 at hn
    nlinarith
  have hproj := stack_gram_regular (fun x => polarRow (L x))
    (fun i => (hp i).1) (fun i => (hp i).2)
  have hmeas : Measurable (fun x => matrix (stack (L x)).kerᗮ.starProjection 1 1) := by
    have hh := hproj.1 1 1
    have hid (x : α) : stack (polarRow (L x)) = polar (stack (L x)) := stack_component _
    simp only [hid, polar_gram] at hh
    exact hh
  have hcut := highAt_regular E he.1 he.2 hsa 1 hnorm (theta/(Fintype.card ι))
  have hsource (x : α) : (E x).comp (stack (L x)).kerᗮ.starProjection = E x := by
    have hp0 : (polar (stack (L x))).comp (stack (L x)).kerᗮ.starProjection =
        polar (stack (L x)) := by
      apply ContinuousLinearMap.ext
      intro v
      have hk : v - (stack (L x)).kerᗮ.starProjection v ∈ (stack (L x)).ker := by
        have hh := (stack (L x)).kerᗮ.sub_starProjection_mem_orthogonal v
        rwa [Submodule.orthogonal_orthogonal] at hh
      have hz := polar_zero_on_kernel (stack (L x)) hk
      rw [map_sub, sub_eq_zero] at hz
      exact hz.symm
    have hv0 : (V x).comp (stack (L x)).kerᗮ.starProjection = V x := by
      change ((normalizedAggregation a).comp (stack (component (polar (stack (L x)))))).comp _ = _
      rw [stack_component, comp_assoc, hp0]
      rfl
    dsimp [E]
    rw [comp_assoc, hv0]
  have hf := normalizedMixed_polar_trace μ S a ha L hL
  have hfirst : (trace μ E).toReal =
      (trace μ (fun x => (stack (L x)).kerᗮ.starProjection)).toReal / (Fintype.card ι:ℝ) := by
    rw [show trace μ E = _ from hf, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    ring
  exact fresh_cut_trace μ E hsa (fun x => (stack (L x)).kerᗮ)
    (by exact_mod_cast hι) htheta hnorm hsource hmeas (hcut.1 1 1) hfinite hfirst

#print axioms fresh_polar_high_trace

end QuantitativeSpectralFreshPolar
