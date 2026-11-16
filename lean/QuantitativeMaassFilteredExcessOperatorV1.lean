module

public import QuantitativeMaassLinearExcessApproxV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem linearPacketTrace_cogram (b : HilbertBasis ι ℂ H) (B F : H→L[ℂ]H)
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    linearPacketTrace b B (F.comp F.adjoint)=hilbertSchmidtEnergy b (B.comp F) := by
  have hs := (right_comp_energy_bound b B F hB).1
  have he := (adjoint_energy_eq b (B.comp F) hs).2
  rw [ContinuousLinearMap.adjoint_comp] at he
  rw [←he]
  apply tsum_congr
  intro i
  change (inner ℂ (F (F.adjoint (B.adjoint (b i)))) (B.adjoint (b i))).re=
    ‖F.adjoint (B.adjoint (b i))‖^2
  rw [←F.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

theorem embedding_filtered_excess_linearTrace (K : V→L[ℂ]H)
    {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (F B : H→L[ℂ]H) (hFK : ∀ x,F (K x)=K x) (hF : IsSelfAdjoint F)
    (b : HilbertBasis ι ℂ H) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    hilbertSchmidtEnergy b ((B.comp F).comp (1-embeddingGramProjection K))=
      linearPacketTrace b B (F*F-embeddingGramProjection K) := by
  rw [linearPacketTrace_sub b B _ _ hB,embedding_target_linearTrace K ha hK b B hB]
  have he := linearPacketTrace_cogram b B F hB
  rw [hF.adjoint_eq] at he
  rw [ContinuousLinearMap.mul_def,he]
  exact embedding_filtered_excess_energy_sub K ha hK F B hFK b hB

/-- The exact excess is a positive square; finite polynomial approximants
to the target projection need not inherit this positivity. -/
theorem embedding_filtered_excess_positive (K : V→L[ℂ]H)
    {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (F : H→L[ℂ]H) (hFK : ∀ x,F (K x)=K x) (hF : IsSelfAdjoint F) :
    0≤F*F-embeddingGramProjection K := by
  have hk := lower_energy_injective_closed (H := V) (K := H) K ha hK
  let : CompleteSpace K.range := hk.2.completeSpace_coe
  have hp : K.range.starProjection=embeddingGramProjection K := embedding_projection_gram_formula K ha hK
  let Q := embeddingGramProjection K
  have hQ : IsSelfAdjoint Q := by dsimp only [Q]; rw [←hp]; exact isSelfAdjoint_starProjection K.range
  have hQQ : Q*Q=Q := by dsimp only [Q]; rw [←hp]; exact K.range.isIdempotentElem_starProjection
  have hFQ : F*Q=Q := embedding_filter_projection K F hFK
  have hQF : Q*F=Q := by
    have he := congrArg ContinuousLinearMap.adjoint hFQ
    change (F.comp Q).adjoint=Q.adjoint at he
    rw [ContinuousLinearMap.mul_def]
    simpa only [ContinuousLinearMap.adjoint_comp,hF.adjoint_eq,hQ.adjoint_eq] using he
  have he : (F-Q)*(F-Q)=F*F-Q := by
    rw [sub_mul,mul_sub,mul_sub,hFQ,hQF,hQQ]
    abel
  have hn : 0≤star (F-Q)*(F-Q) := star_mul_self_nonneg _
  rw [(hF.sub hQ).star_eq,he] at hn
  exact hn

#print axioms linearPacketTrace_cogram
#print axioms embedding_filtered_excess_linearTrace
#print axioms embedding_filtered_excess_positive

end QuantitativeMaass
