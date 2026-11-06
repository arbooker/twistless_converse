module

public import QuantitativeSpectralFreshCutDataV1
public import QuantitativeSpectralWhiteningMinmaxV1
public import AsymptoticMixingCornerV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralFreshMixing

open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticObservationStack
open AsymptoticPolarIsometry AsymptoticMixing AsymptoticSubgroupSupport
open QuantitativeSpectralCut QuantitativeSpectralCutPolar QuantitativeSpectralCutWhitening
open QuantitativeSpectralFreshCutData QuantitativeSpectralFreshPolar
open QuantitativeSpectralWhiteningMinmax
open scoped lp ENNReal

variable {G α ι : Type*} [Group G] [Countable G] [Fintype ι]
  [MeasurableSpace α] [MulAction G α]

/-- Sharp fresh-prime spectral extraction for the original averaged equation.
The individual high cut and its polar whitening are constructed from the
actual rows. The retained factor approaches `1/card` as `theta` tends to zero;
only the threshold, not the rank factor, pays for the individual coercivity. -/
theorem fresh_mixed_high_trace (μ : Measure α)
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (S : Subgroup G) (a : ι → G) (ha : ∀ i j, i ≠ j → a j * (a i)⁻¹ ∉ S)
    (hι : 0 < Fintype.card ι)
    (P : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x, CompleteSpace (P x)]
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h, Measurable (fun x => matrix (L x i) g h))
    (hc : ∀ i, Covariant (fun x => L x i))
    (hL : ∀ x i, Supported S (L x i))
    (hP : ∀ x i, (L x i).comp (P x).starProjection = L x i)
    (M : ℝ) (hM : ∀ x, ‖stack (L x)‖ ≤ M)
    (hf : trace μ (fun x => (P x).starProjection) < ∞)
    {c theta : ℝ} (hcpos : 0 < c) (htheta : 0 < theta) :
    (1-theta) * (trace μ (fun x => (cutSpace (stack (L x)) c).starProjection)).toReal /
      (Fintype.card ι : ℝ) ≤
      (trace μ (fun x => (highAt
        ((normalizedMixed a (L x)).adjoint.comp (normalizedMixed a (L x)))
        (c^2*theta/(2*(Fintype.card ι)))).starProjection)).toReal := by
  let A := fun x => normalizedMixed a (L x)
  let Q := fun x => normalizedMixed a (polarRow (cutRows (L x) c))
  let J := fun x => cutWhitening (stack (L x)) c
  have hcut := cutRows_regular L hm hc M hM c
  have hpol := stack_polarRow_regular (fun x => cutRows (L x) c)
    (fun i => (hcut i).1) (fun i => (hcut i).2) M
    (fun x => (cutRows_norm (L x) c).trans (hM x))
  have hA := normalizedMixed_regular a L hm hc
  have hQ := normalizedMixed_regular a (fun x => polarRow (cutRows (L x) c))
    (fun i => (hpol i).1) (fun i => (hpol i).2)
  have hJ := cutWhitening_regular L hm hc M hM hcpos
  have hfactor (x : α) : (A x).comp (J x) = Q x := by
    change ((normalizedAggregation a).comp (stack (L x))).comp (cutWhitening (stack (L x)) c) =
      (normalizedAggregation a).comp (stack (component (polar (stack (cutRows (L x) c)))))
    rw [stack_component, stack_cutRows, comp_assoc, cutWhitening_factor _ hcpos]
  have hn : 0 < (Fintype.card ι:ℝ) := by exact_mod_cast hι
  have hth : 0 ≤ c^2*theta/(2*(Fintype.card ι:ℝ)) := by positivity
  have hgap : (c^2*theta/(2*(Fintype.card ι:ℝ)))*(c⁻¹)^2 < theta/(Fintype.card ι:ℝ) := by
    have he : (c^2*theta/(2*(Fintype.card ι:ℝ)))*(c⁻¹)^2 = (theta/(Fintype.card ι:ℝ))/2 := by
      field_simp
    rw [he]
    exact half_lt_self (div_pos htheta hn)
  have hcompare := whitening_high_trace μ hmp A Q J hA.1 hA.2 hQ.1 hQ.2 hJ.1 hJ.2 M 1
    (fun x => (normalizedMixed_norm a (L x)).trans (hM x))
    (fun x => normalizedMixed_polar_norm a (cutRows (L x) c)) hfactor hth
    (inv_nonneg.mpr hcpos.le) (fun x => cutWhitening_norm (stack (L x)) hcpos) hgap
  have hgram (T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) : IsSelfAdjoint (T.adjoint.comp T) := by
    rw [isSelfAdjoint_iff']
    simp only [adjoint_comp, adjoint_adjoint]
  have hAP (x : α) : ((A x).adjoint.comp (A x)).comp (P x).starProjection =
      (A x).adjoint.comp (A x) := by
    rw [comp_assoc, normalizedMixed_comp_projection (P x) a (L x) (hP x)]
  have hfinA := projection_trace_finite_of_le μ
    (fun x => highAt ((A x).adjoint.comp (A x)) (c^2*theta/(2*(Fintype.card ι)))) P
    (fun x => highAt_le_corner _ (hgram (A x)) (P x) hth (hAP x)) hf
  have hfinR : trace μ (fun x => (cutSpace (stack (L x)) c).starProjection) < ∞ := by
    apply projection_trace_finite_of_le μ _ P _ hf
    intro x
    apply highAt_le_corner _ _ (P x) (sq_nonneg c)
    · rw [comp_assoc, stack_comp_projection (P x) (L x) (hP x)]
    · rw [isSelfAdjoint_iff']; simp only [adjoint_comp, adjoint_adjoint]
  have hs (x : α) : (stack (cutRows (L x) c)).kerᗮ.starProjection =
      (cutSpace (stack (L x)) c).starProjection := by
    rw [stack_cutRows]
    congr 1
    exact cutOperator_support _ hcpos
  have hfcut : trace μ (fun x => (stack (cutRows (L x) c)).kerᗮ.starProjection) < ∞ := by
    simpa only [hs] using hfinR
  have hl := fresh_polar_high_trace μ S a ha hι (fun x => cutRows (L x) c)
    (fun i => (hcut i).1) (fun i => (hcut i).2)
    (fun x i => cutRows_supported S (L x) (hL x) c i) M
    (fun x => (cutRows_norm (L x) c).trans (hM x)) htheta.le hfcut
  simp only [hs] at hl
  exact hl.trans (ENNReal.toReal_mono hfinA.ne hcompare)

#print axioms fresh_mixed_high_trace

end QuantitativeSpectralFreshMixing
