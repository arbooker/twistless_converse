module

public import QuantitativeEulerEndpointHighInverseV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointHighInverse
open ContinuousLinearMap QuantitativeSpectralCut AsymptoticRegularTrace MeasureTheory
open QuantitativeSpectralCutRegularity QuantitativeSpectralWhiteningMinmax
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

theorem highInverse_regular (A : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h, Measurable (fun x => matrix (A x) g h)) (hc : Covariant A)
    (hsa : ∀ x, IsSelfAdjoint (A x)) (M : ℝ) (hM : ∀ x, ‖A x‖≤M)
    {a : ℝ} (ha : 0<a) :
    (∀ g h, Measurable (fun x => matrix (highInverse (A x) a) g h)) ∧
      Covariant (fun x => highInverse (A x) a) := by
  have hf := cfc_regular A hm hc hsa M hM (clippedInverse a) (clippedInverse_continuous ha)
  have hp := highAt_regular A hm hc hsa M hM a
  exact ⟨matrix_comp_measurable _ _ hf.1 hp.1,covariant_comp _ _ hf.2 hp.2⟩

/-- Exact high-spectrum transfer from a hard subcorner to the same soft
source. The bounded inverse on its high cut costs only a threshold factor;
there is no Hilbert--Schmidt perturbation or rank-loss hypothesis. -/
theorem hard_to_soft_high_trace (μ : Measure α)
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (A B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmA : ∀ g h, Measurable (fun x => matrix (A x) g h)) (hcA : Covariant A)
    (hmB : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hcB : Covariant B)
    (hsa : ∀ x, IsSelfAdjoint (A x)) (M N : ℝ)
    (hM : ∀ x, ‖A x‖≤M) (hN : ∀ x, ‖B x‖≤N)
    {a lam beta : ℝ} (ha : 0<a) (hlam : 0≤lam) (hgap : lam*(a⁻¹)^2<beta) :
    let P := fun x => (highAt (A x) a).starProjection
    trace μ (fun x => (highAt ((B x*P x).adjoint.comp (B x*P x)) beta).starProjection)≤
      trace μ (fun x => (highAt ((B x*A x).adjoint.comp (B x*A x)) lam).starProjection) := by
  let P := fun x => (highAt (A x) a).starProjection
  have hp := highAt_regular A hmA hcA hsa M hM a
  have hi := highInverse_regular A hmA hcA hsa M hM ha
  apply whitening_high_trace μ hmp (fun x => B x*A x) (fun x => B x*P x)
    (fun x => highInverse (A x) a)
    (matrix_comp_measurable _ _ hmB hmA) (covariant_comp _ _ hcB hcA)
    (matrix_comp_measurable _ _ hmB hp.1) (covariant_comp _ _ hcB hp.2)
    hi.1 hi.2 (N*M) N
  · intro x
    exact norm_mul_le_of_le (hN x) (hM x)
  · intro x
    exact (norm_mul_le_of_le (hN x) (highAt (A x) a).starProjection_norm_le).trans_eq (mul_one N)
  · intro x
    change (B x*A x)*highInverse (A x) a=B x*P x
    rw [mul_assoc,highInverse_factor _ (hsa x) ha]
  · exact hlam
  · exact inv_nonneg.mpr ha.le
  · intro x
    exact highInverse_norm _ ha
  · exact hgap

#print axioms highInverse_regular
#print axioms hard_to_soft_high_trace
end QuantitativeEulerEndpointHighInverse
