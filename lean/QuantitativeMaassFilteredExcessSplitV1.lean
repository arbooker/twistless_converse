module

public import QuantitativeMaassWeightedTargetProjectionV1
public import QuantitativeMaassHilbertSchmidtIdealV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem embedding_filter_projection (K : V→L[ℂ]H) (F : H→L[ℂ]H)
    (hFK : ∀ x,F (K x)=K x) : F.comp (embeddingGramProjection K)=embeddingGramProjection K := by
  ext x
  change F (K _)=K _
  exact hFK _

/-- Exact subtraction at the Hilbert--Schmidt trace level. The target
projection enters linearly, even when the packet is not self-adjoint. -/
theorem embedding_filtered_excess_energy_split (K : V→L[ℂ]H)
    {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (F B : H→L[ℂ]H) (hFK : ∀ x,F (K x)=K x)
    (b : HilbertBasis ι ℂ H) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    hilbertSchmidtEnergy b (B.comp F)=
      hilbertSchmidtEnergy b (B.comp (embeddingGramProjection K))+
      hilbertSchmidtEnergy b ((B.comp F).comp (1-embeddingGramProjection K)) := by
  have hk := lower_energy_injective_closed (H := V) (K := H) K ha hK
  let : CompleteSpace K.range := hk.2.completeSpace_coe
  have hp : K.range.starProjection=embeddingGramProjection K := embedding_projection_gram_formula K ha hK
  have hs := (right_comp_energy_bound b B F hB).1
  rw [source_projection_energy_split b K.range (B.comp F) hs,
    Submodule.starProjection_orthogonal',hp]
  rw [ContinuousLinearMap.comp_assoc,embedding_filter_projection K F hFK]

theorem embedding_filtered_excess_energy_sub (K : V→L[ℂ]H)
    {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (F B : H→L[ℂ]H) (hFK : ∀ x,F (K x)=K x)
    (b : HilbertBasis ι ℂ H) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    hilbertSchmidtEnergy b ((B.comp F).comp (1-embeddingGramProjection K))=
      hilbertSchmidtEnergy b (B.comp F)-hilbertSchmidtEnergy b (B.comp (embeddingGramProjection K)) := by
  have hh := embedding_filtered_excess_energy_split K ha hK F B hFK b hB
  linarith

#print axioms embedding_filter_projection
#print axioms embedding_filtered_excess_energy_split
#print axioms embedding_filtered_excess_energy_sub

end QuantitativeMaass
