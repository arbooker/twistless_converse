module

public import QuantitativeMaassColumnExcessTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open MeasureTheory ContinuousLinearMap
namespace QuantitativeMaass

variable {α G H V E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Rectangular input maps retain the exact real column-energy identity. -/
theorem rectangular_column_input_energy {ι : Type*} [Countable ι]
    (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (b : HilbertBasis ι ℂ G) (A : G→L[ℂ]H) :
    (∑' i,‖finiteEnergyColumnOperator μ c hc (A (b i))‖^2)=
      columnLinearTrace μ c (A.comp A.adjoint) := by
  have hh := finiteEnergyColumn_input_real_energy μ (fun x => A.adjoint (c x))
    (finiteEnergyColumn_input_memLp μ c hc A) b 1
  rw [←finiteEnergyColumnOperator_comp μ c hc A] at hh
  simp only [one_apply_eq_self,adjoint_one,comp_apply] at hh
  rw [hh,columnLinearTrace]
  apply integral_congr_ae
  filter_upwards with x
  rw [comp_apply,←A.adjoint_inner_right]
  exact norm_sq_eq_re_inner (𝕜:=ℂ) _

/-- A bounded output map costs only its squared norm in the exact rectangular
column trace. No trace estimate or finiteness hypothesis is assumed. -/
theorem rectangular_column_output_bound {ι : Type*} [Countable ι]
    (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (b : HilbertBasis ι ℂ G) (A : G→L[ℂ]H) (L : Lp ℂ 2 μ→L[ℂ]E) :
    (∑' i,‖L (finiteEnergyColumnOperator μ c hc (A (b i)))‖^2)≤
      ‖L‖^2*columnLinearTrace μ c (A.comp A.adjoint) := by
  have hs := finiteEnergyColumn_composition_summable μ c hc b A L
  have hi := finiteEnergyColumnOperator_summable μ (fun x => A.adjoint (c x))
    (finiteEnergyColumn_input_memLp μ c hc A) b
  rw [←finiteEnergyColumnOperator_comp μ c hc A] at hi
  rw [←rectangular_column_input_energy μ c hc b A,←tsum_mul_left]
  apply hs.tsum_le_tsum _ (hi.mul_left (‖L‖^2))
  intro i
  simpa only [mul_pow,comp_apply] using pow_le_pow_left₀ (norm_nonneg _)
    (L.le_opNorm (finiteEnergyColumnOperator μ c hc (A (b i)))) 2

/-- The actual excess after a reconstruction isometry has a linear ambient
trace, allowing finite rational-branch approximation of its filter and target. -/
theorem isometric_column_excess_bound {ι : Type*} [Countable ι]
    (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (b : HilbertBasis ι ℂ G) (U : G→ₗᵢ[ℂ]H) (K : V→L[ℂ]G)
    {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (F : G→L[ℂ]G) (hFK : ∀ x,F (K x)=K x) (hF : IsSelfAdjoint F)
    (L : Lp ℂ 2 μ→L[ℂ]E) :
    (∑' i,‖L (finiteEnergyColumnOperator μ c hc
      (U (F ((1-embeddingGramProjection K) (b i)))))‖^2)≤
      ‖L‖^2*columnLinearTrace μ c
        (U.toContinuousLinearMap.comp ((F*F-embeddingGramProjection K).comp
          U.toContinuousLinearMap.adjoint)) := by
  have hp : F.comp (1-embeddingGramProjection K)=F-embeddingGramProjection K := by
    rw [comp_sub]
    change F-F.comp (embeddingGramProjection K)=F-embeddingGramProjection K
    rw [embedding_filter_projection K F hFK]
  have hh := rectangular_column_output_bound μ c hc b
    (U.toContinuousLinearMap.comp (F-embeddingGramProjection K)) L
  have hg : (U.toContinuousLinearMap.comp (F-embeddingGramProjection K)).comp
      (U.toContinuousLinearMap.comp (F-embeddingGramProjection K)).adjoint=
      U.toContinuousLinearMap.comp ((F*F-embeddingGramProjection K).comp U.toContinuousLinearMap.adjoint) := by
    rw [adjoint_comp,comp_assoc,←comp_assoc (F-embeddingGramProjection K),
      embedding_excess_cogram K ha hK F hFK hF]
  rw [hg,←hp] at hh
  exact hh

#print axioms rectangular_column_input_energy
#print axioms rectangular_column_output_bound
#print axioms isometric_column_excess_bound
end QuantitativeMaass
