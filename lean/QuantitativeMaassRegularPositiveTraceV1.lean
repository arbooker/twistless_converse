module

public import QuantitativeMaassRegularPositiveGramV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal
namespace AsymptoticRegularTrace
variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
    [TopologicalSpace α] [DiscreteTopology α]

/-- Weighted positive finite regular families have integrable rooted diagonals. -/
theorem positive_weight_diagonal_integrable (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (F B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hF : ∀ g h,Measurable (fun x => matrix (F x) g h))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hcF : Covariant F) (hcB : Covariant B) (hp : ∀ x,0≤F x)
    {K C : ℝ} (hn : ∀ x,‖F x‖≤K) (hb : ∀ x,‖B x‖≤C)
    (hf : trace μ F<∞) :
    Integrable (fun x => (matrix ((B x).comp (F x)) 1 1).re) μ := by
  obtain ⟨R,hR,hcR,_,hRR⟩ := positive_regular_gram_factor (fun g => (hmp g).measurable) F hF hcF hn hp
  have hr : trace μ (fun x => (R x).adjoint.comp (R x))<∞ := by simpa only [hRR] using hf
  have hh := weighted_gram_diagonal_integrable μ hmp R B hR hB hcR hcB hr hb
  simpa only [hRR] using hh

/-- A bounded covariant sandwich of a positive finite regular family remains
finite, even when its range is not contained in a finite geometric corner. -/
theorem positive_sandwich_trace_finite (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (F D : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hF : ∀ g h,Measurable (fun x => matrix (F x) g h))
    (hD : ∀ g h,Measurable (fun x => matrix (D x) g h))
    (hcF : Covariant F) (hcD : Covariant D) (hp : ∀ x,0≤F x)
    {K C : ℝ} (hn : ∀ x,‖F x‖≤K) (hd : ∀ x,‖D x‖≤C)
    (hf : trace μ F<∞) :
    trace μ (fun x => (D x).adjoint.comp ((F x).comp (D x)))<∞ := by
  obtain ⟨R,hR,hcR,_,hRR⟩ := positive_regular_gram_factor (fun g => (hmp g).measurable) F hF hcF hn hp
  have hr : trace μ (fun x => (R x).adjoint.comp (R x))<∞ := by simpa only [hRR] using hf
  have hh := trace_gram_right_comp_finite μ hmp R D hR hD hcR hcD hr hd
  have he (x : α) : ((R x).comp (D x)).adjoint.comp ((R x).comp (D x))=
      (D x).adjoint.comp ((F x).comp (D x)) := by
    rw [adjoint_comp]
    simp only [comp_assoc]
    rw [←comp_assoc (R x).adjoint (R x) (D x),hRR]
  simpa only [he] using hh

#print axioms positive_weight_diagonal_integrable
#print axioms positive_sandwich_trace_finite
end AsymptoticRegularTrace
