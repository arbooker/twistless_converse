module

public import QuantitativeMaassTargetTraceV1
public import QuantitativeMaassWeightedTargetProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

def EmbeddingTargetCount {H V ι κ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (K : V →L[ℂ] H) (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ V) : Prop :=
    ∃ C : ℝ,0≤C ∧ ∀ (B : H →L[ℂ] H) (D : V →L[ℂ] V),
      (∀ x,B (K x)=K (D x)) → ∀ (η : Type*) (v : η → H),
      LinearIndependent ℂ v → ∀ h : η → ℝ,
      (∀ i,B (v i)=(h i:ℂ) • v i) → (∀ i,1≤h i) →
      Summable (fun i => ‖B (b i)‖^2) →
      Finite η ∧ (Nat.card η:ℝ)≤hilbertSchmidtEnergy c D+
        C*hilbertSchmidtEnergy b (B.comp (1-embeddingGramProjection K))

/-- A lower bounded target embedding gives a fixed excess constant for
all intertwining finite-energy operators and all independent eigenfamilies. -/
theorem exists_embedding_target_count {H V ι κ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (K : V →L[ℂ] H) {a : ℝ} (ha : 0<a) (hK : ∀ x,a*‖x‖^2≤‖K x‖^2)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ V) :
    EmbeddingTargetCount K b c := by
  unfold EmbeddingTargetCount
  have hk := lower_energy_injective_closed (H := V) (K := H) K ha hK
  let W := K.range
  let : CompleteSpace W := hk.2.completeSpace_coe
  let J : V ≃L[ℂ] W := ContinuousLinearMap.equivRange (f := K) hk.1 hk.2
  have hJ (x : V) : a*‖x‖^2≤‖J x‖^2 := hK x
  let L := targetMetric W J ha hJ
  refine ⟨‖L.toContinuousLinearMap‖^2,sq_nonneg _,?_⟩
  intro B D hBD η v hv h he hl hB
  have hcount := count_target_canonical_excess W J ha hJ b c B D hBD v hv h he hl hB
  have hp : Wᗮ.starProjection=1-embeddingGramProjection K := by
    have hg := embedding_projection_gram_formula K ha hK
    change W.starProjection=embeddingGramProjection K at hg
    ext x
    rw [W.starProjection_orthogonal_val,hg]
    rfl
  rw [hp] at hcount
  exact hcount

#print axioms exists_embedding_target_count

end QuantitativeMaass
