module

public import QuantitativeMaassColumnLinearTraceV1
public import QuantitativeMaassFilteredExcessOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped ENNReal

namespace QuantitativeMaass

variable {α V H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact excess admits a cogram factorization before any trace is
taken. The target appears only linearly. -/
theorem embedding_excess_cogram (K : V→L[ℂ]H)
    {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (F : H→L[ℂ]H) (hFK : ∀ x,F (K x)=K x) (hF : IsSelfAdjoint F) :
    (F-embeddingGramProjection K).comp (F-embeddingGramProjection K).adjoint=
      F*F-embeddingGramProjection K := by
  have hk := lower_energy_injective_closed (H := V) (K := H) K ha hK
  let : CompleteSpace K.range := hk.2.completeSpace_coe
  have hp : K.range.starProjection=embeddingGramProjection K := embedding_projection_gram_formula K ha hK
  let Q := embeddingGramProjection K
  have hQ : IsSelfAdjoint Q := by dsimp only [Q]; rw [←hp]; exact isSelfAdjoint_starProjection K.range
  have hQQ : Q*Q=Q := by dsimp only [Q]; rw [←hp]; exact K.range.isIdempotentElem_starProjection
  have hFQ : F*Q=Q := embedding_filter_projection K F hFK
  have hQF : Q*F=Q := by
    have hh := congrArg ContinuousLinearMap.adjoint hFQ
    change (F.comp Q).adjoint=Q.adjoint at hh
    rw [ContinuousLinearMap.mul_def]
    simpa only [ContinuousLinearMap.adjoint_comp,hF.adjoint_eq,hQ.adjoint_eq] using hh
  change (F-Q).comp (F-Q).adjoint=F*F-Q
  rw [(hF.sub hQ).adjoint_eq,←ContinuousLinearMap.mul_def,sub_mul,mul_sub,mul_sub,hFQ,hQF,hQQ]
  abel

/-- Actual filtered excess energy equals the integral of the linear
finite-column trace density. No operator trace estimate is assumed. -/
theorem column_excess_energy_trace {ι : Type*} [Countable ι]
    (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ) (basis : HilbertBasis ι ℂ H)
    (K : V→L[ℂ]H) {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (F : H→L[ℂ]H) (hFK : ∀ x,F (K x)=K x) (hF : IsSelfAdjoint F) :
    (∑' i,‖finiteEnergyColumnOperator μ c hc ((F-embeddingGramProjection K) (basis i))‖^2)=
      columnLinearTrace μ c (F*F-embeddingGramProjection K) := by
  rw [←embedding_excess_cogram K ha hK F hFK hF,columnLinearTrace_cogram μ c hc basis]

/-- Linear approximation of the exact excess in the actual column
integral, with the error controlled by the unfiltered column energy. -/
theorem column_excess_energy_approx {ι : Type*} [Countable ι]
    (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ) (basis : HilbertBasis ι ℂ H)
    (K : V→L[ℂ]H) {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (F : H→L[ℂ]H) (hFK : ∀ x,F (K x)=K x) (hF : IsSelfAdjoint F)
    (T : H→L[ℂ]H) {δ : ℝ} (hδ : ‖F*F-embeddingGramProjection K-T‖≤δ) :
    |(∑' i,‖finiteEnergyColumnOperator μ c hc ((F-embeddingGramProjection K) (basis i))‖^2)-
      columnLinearTrace μ c T|≤δ*(∫ x,‖c x‖^2 ∂μ) := by
  rw [column_excess_energy_trace μ c hc basis K ha hK F hFK hF]
  exact columnLinearTrace_approx μ c hc _ T hδ

#print axioms embedding_excess_cogram
#print axioms column_excess_energy_trace
#print axioms column_excess_energy_approx

end QuantitativeMaass
