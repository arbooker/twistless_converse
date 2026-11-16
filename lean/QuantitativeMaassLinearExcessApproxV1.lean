module

public import QuantitativeMaassLinearPacketTraceV1
public import QuantitativeMaassFilteredExcessSplitV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem embedding_target_linearTrace (K : V→L[ℂ]H)
    {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (b : HilbertBasis ι ℂ H) (B : H→L[ℂ]H) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    linearPacketTrace b B (embeddingGramProjection K)=
      hilbertSchmidtEnergy b (B.comp (embeddingGramProjection K)) := by
  have hk := lower_energy_injective_closed (H := V) (K := H) K ha hK
  let : CompleteSpace K.range := hk.2.completeSpace_coe
  have hp : K.range.starProjection=embeddingGramProjection K := embedding_projection_gram_formula K ha hK
  rw [←hp]
  exact linearPacketTrace_projection b B hB K.range

/-- Linear approximation of the exact filtered excess. The approximant
need not be positive or a projection, and the error has no leading-factor loss. -/
theorem embedding_filtered_excess_linear_approx (K : V→L[ℂ]H)
    {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (F B T : H→L[ℂ]H) (hFK : ∀ x,F (K x)=K x)
    (b : HilbertBasis ι ℂ H) (hB : Summable (fun i => ‖B (b i)‖^2))
    {δ : ℝ} (hδ : ‖T-embeddingGramProjection K‖≤δ) :
    |hilbertSchmidtEnergy b ((B.comp F).comp (1-embeddingGramProjection K))-
      (hilbertSchmidtEnergy b (B.comp F)-linearPacketTrace b B T)|≤δ*hilbertSchmidtEnergy b B := by
  rw [embedding_filtered_excess_energy_sub K ha hK F B hFK b hB,
    ←embedding_target_linearTrace K ha hK b B hB]
  have he : hilbertSchmidtEnergy b (B.comp F)-linearPacketTrace b B (embeddingGramProjection K)-
      (hilbertSchmidtEnergy b (B.comp F)-linearPacketTrace b B T)=
        linearPacketTrace b B T-linearPacketTrace b B (embeddingGramProjection K) := by ring
  rw [he]
  exact linearPacketTrace_approx b B T (embeddingGramProjection K) hB hδ

#print axioms embedding_target_linearTrace
#print axioms embedding_filtered_excess_linear_approx

end QuantitativeMaass
