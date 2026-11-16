module

public import QuantitativeMaassLinearExcessApproxV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap
namespace QuantitativeMaass

variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A trace supported on a self-adjoint corner sees only the packet on
that corner. This identity does not require an ambient packet norm bound. -/
theorem linearPacketTrace_supported (b : HilbertBasis ι ℂ H) (B Q T : H→L[ℂ]H)
    (hQ : IsSelfAdjoint Q) (hT : Q.comp (T.comp Q)=T) :
    linearPacketTrace b B T=linearPacketTrace b (B.comp Q) T := by
  unfold linearPacketTrace
  simp only [adjoint_comp,hQ.adjoint_eq,comp_apply]
  apply tsum_congr
  intro i
  apply congrArg Complex.re
  have ht := congrArg (fun A : H→L[ℂ]H => A (B.adjoint (b i))) hT
  change Q (T (Q (B.adjoint (b i))))=T (B.adjoint (b i)) at ht
  rw [←ht]
  simpa only [hQ.adjoint_eq] using
    (Q.adjoint_inner_right (T (Q (B.adjoint (b i)))) (B.adjoint (b i))).symm

/-- When both the target and its approximation are supported on the same
orthogonal corner, the error costs only the canonical packet energy. -/
theorem linearPacketTrace_supported_approx (b : HilbertBasis ι ℂ H) (B Q T : H→L[ℂ]H)
    (hQ : IsSelfAdjoint Q) (hQQ : Q.comp Q=Q) (hT : Q.comp (T.comp Q)=T)
    (hB : Summable (fun i => ‖B (b i)‖^2)) {δ : ℝ} (hδ : ‖T-Q‖≤δ) :
    |linearPacketTrace b B T-linearPacketTrace b B Q|≤δ*hilbertSchmidtEnergy b (B.comp Q) := by
  have hD : Q.comp ((T-Q).comp Q)=T-Q := by
    rw [sub_comp,comp_sub,hT,hQQ,hQQ]
  rw [←linearPacketTrace_sub b B T Q hB,linearPacketTrace_supported b B Q (T-Q) hQ hD]
  exact (linearPacketTrace_bound b (B.comp Q) (T-Q) (right_comp_energy_bound b B Q hB).1).trans
    (mul_le_mul_of_nonneg_right hδ (tsum_nonneg (fun _ => sq_nonneg _)))

/-- Every cogram whose reconstruction is fixed by the corner is supported
on that corner on both sides. -/
theorem cogram_supported_of_fixed (Q : H→L[ℂ]H) (hQ : IsSelfAdjoint Q)
    (S : V→L[ℂ]H) (hS : Q.comp S=S) :
    Q.comp ((S.comp S.adjoint).comp Q)=S.comp S.adjoint := by
  have hs : S.adjoint.comp Q=S.adjoint := by
    simpa only [adjoint_comp,hQ.adjoint_eq] using congrArg ContinuousLinearMap.adjoint hS
  calc
    _ = (Q.comp S).comp (S.adjoint.comp Q) := rfl
    _ = _ := by rw [hS,hs]

/-- The exact filtered excess admits target-supported linear approximation
with the smaller target packet energy as its error factor. -/
theorem embedding_filtered_excess_supported_approx (K : V→L[ℂ]H)
    {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (F B T : H→L[ℂ]H) (hFK : ∀ x,F (K x)=K x)
    (b : HilbertBasis ι ℂ H) (hB : Summable (fun i => ‖B (b i)‖^2))
    (hT : (embeddingGramProjection K).comp (T.comp (embeddingGramProjection K))=T)
    {δ : ℝ} (hδ : ‖T-embeddingGramProjection K‖≤δ) :
    |hilbertSchmidtEnergy b ((B.comp F).comp (1-embeddingGramProjection K))-
      (hilbertSchmidtEnergy b (B.comp F)-linearPacketTrace b B T)|≤
      δ*hilbertSchmidtEnergy b (B.comp (embeddingGramProjection K)) := by
  have hk := lower_energy_injective_closed (H := V) (K := H) K ha hK
  let : CompleteSpace K.range := hk.2.completeSpace_coe
  have hp : K.range.starProjection=embeddingGramProjection K := embedding_projection_gram_formula K ha hK
  have hQ : IsSelfAdjoint (embeddingGramProjection K) := by
    rw [←hp]
    exact isSelfAdjoint_starProjection K.range
  have hQQ : (embeddingGramProjection K).comp (embeddingGramProjection K)=embeddingGramProjection K := by
    rw [←hp,←mul_def]
    exact K.range.isIdempotentElem_starProjection
  rw [embedding_filtered_excess_energy_sub K ha hK F B hFK b hB,
    ←embedding_target_linearTrace K ha hK b B hB]
  have he : hilbertSchmidtEnergy b (B.comp F)-linearPacketTrace b B (embeddingGramProjection K)-
      (hilbertSchmidtEnergy b (B.comp F)-linearPacketTrace b B T)=
        linearPacketTrace b B T-linearPacketTrace b B (embeddingGramProjection K) := by ring
  rw [he]
  simpa only [embedding_target_linearTrace K ha hK b B hB] using
    linearPacketTrace_supported_approx b B (embeddingGramProjection K) T hQ hQQ hT hB hδ

/-- Every finite reconstruction through the embedding has target-supported
cogram, including all inverse-square-root Newton polynomials. -/
theorem embedding_reconstruction_cogram_supported (K : V→L[ℂ]H)
    {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2) (P : V→L[ℂ]V) :
    (embeddingGramProjection K).comp
      (((K.comp P).comp (K.comp P).adjoint).comp (embeddingGramProjection K))=
        (K.comp P).comp (K.comp P).adjoint := by
  have hk := lower_energy_injective_closed (H := V) (K := H) K ha hK
  let : CompleteSpace K.range := hk.2.completeSpace_coe
  have hp : K.range.starProjection=embeddingGramProjection K := embedding_projection_gram_formula K ha hK
  have hQ : IsSelfAdjoint (embeddingGramProjection K) := by
    rw [←hp]
    exact isSelfAdjoint_starProjection K.range
  apply cogram_supported_of_fixed _ hQ
  apply ContinuousLinearMap.ext
  intro x
  rw [←hp]
  exact K.range.starProjection_eq_self_iff.mpr ⟨P x,rfl⟩

#print axioms linearPacketTrace_supported
#print axioms linearPacketTrace_supported_approx
#print axioms cogram_supported_of_fixed
#print axioms embedding_filtered_excess_supported_approx
#print axioms embedding_reconstruction_cogram_supported
end QuantitativeMaass
