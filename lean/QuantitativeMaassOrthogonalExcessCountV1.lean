module

public import QuantitativeMaassEmbeddingTargetCountV1
public import QuantitativeMaassHilbertSchmidtIdealV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

open ContinuousLinearMap

namespace QuantitativeMaass

variable {H V ι κ : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Removing an invariant opposite-parity space from the output removes
its entire contribution to the excess, even when the operator is not self-adjoint. -/
theorem remove_invariant_space_energy (W : Submodule ℂ H) [CompleteSpace W]
    (b : HilbertBasis ι ℂ H) (B P : H→L[ℂ]H)
    (hBW : ∀ x∈W,B x∈W) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    hilbertSchmidtEnergy b (((1-W.starProjection).comp B).comp (1-P))≤
      hilbertSchmidtEnergy b (B.comp (1-P-W.starProjection)) := by
  let Q := W.starProjection
  have hfix (x : H) : Q (B (Q x))=B (Q x) :=
    Submodule.starProjection_eq_self_iff.mpr (hBW _ (W.starProjection_apply_mem x))
  have he : ((1-Q).comp B).comp (1-P)=
      (1-Q).comp (B.comp (1-P-Q)) := by
    apply ContinuousLinearMap.ext
    intro x
    change B (x-P x)-Q (B (x-P x))=
      B (x-P x-Q x)-Q (B (x-P x-Q x))
    simp only [map_sub,hfix]
    abel
  have hQ : ‖(1:H→L[ℂ]H)-Q‖≤1 := by
    rw [←W.starProjection_orthogonal']
    exact Wᗮ.starProjection_norm_le
  have hs := (right_comp_energy_bound b B (1-P-Q) hB).1
  rw [he]
  apply (left_comp_energy_bound b (1-Q) (B.comp (1-P-Q)) hs).2.trans
  have hn : 0≤hilbertSchmidtEnergy b (B.comp (1-P-Q)) :=
    tsum_nonneg (fun _ => sq_nonneg _)
  simpa only [one_mul,one_pow] using
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg (1-Q)) hQ 2) hn

/-- Independent eigenvectors orthogonal to another invariant space are
counted using only their own canonical target and the excess outside both
spaces. In applications the excluded space is the opposite parity. -/
theorem exists_embedding_target_count_orthogonal (K : V→L[ℂ]H)
    {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ V)
    (W : Submodule ℂ H) [CompleteSpace W] (hKW : ∀ x,K x∈Wᗮ) :
    ∃ C : ℝ,0≤C ∧ ∀ (B : H→L[ℂ]H) (D : V→L[ℂ]V),
      (∀ x,B (K x)=K (D x)) → (∀ x∈W,B x∈W) →
      ∀ (η : Type*) (v : η→H), LinearIndependent ℂ v → (∀ i,v i∈Wᗮ) →
      ∀ h : η→ℝ, (∀ i,B (v i)=(h i:ℂ) • v i) → (∀ i,1≤h i) →
      Summable (fun i => ‖B (b i)‖^2) →
      Finite η ∧ (Nat.card η:ℝ)≤hilbertSchmidtEnergy c D+
        C*hilbertSchmidtEnergy b (B.comp (1-embeddingGramProjection K-W.starProjection)) := by
  obtain ⟨C,hC,hcount⟩ := exists_embedding_target_count K ha hK b c
  refine ⟨C,hC,?_⟩
  intro B D hBD hBW η v hv hvW h he hl hB
  let B' := (1-W.starProjection).comp B
  have hBD' (x : V) : B' (K x)=K (D x) := by
    change B (K x)-W.starProjection (B (K x))=_
    rw [hBD,(W.starProjection_apply_eq_zero_iff).mpr (hKW (D x)),sub_zero]
  have he' (i : η) : B' (v i)=(h i:ℂ) • v i := by
    change B (v i)-W.starProjection (B (v i))=_
    rw [he,map_smul,(W.starProjection_apply_eq_zero_iff).mpr (hvW i),smul_zero,sub_zero]
  have hc := hcount B' D hBD' η v hv h he' hl
    (left_comp_energy_bound b (1-W.starProjection) B hB).1
  refine ⟨hc.1,hc.2.trans ?_⟩
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left
    (remove_invariant_space_energy W b B (embeddingGramProjection K) hBW hB) hC

#print axioms remove_invariant_space_energy
#print axioms exists_embedding_target_count_orthogonal

end QuantitativeMaass
