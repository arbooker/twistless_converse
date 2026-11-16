module

public import QuantitativeMaassSimilarityCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeMaass

variable {H K ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Pulling a metric-transformed canonical cogram back removes the metric
exactly. No inverse Gram or commutation with an observation operator occurs. -/
theorem metric_cogram_pullback (L : H≃L[ℂ]H) (J : K→L[ℂ]H) :
    (L.symm.toContinuousLinearMap.comp
      ((L.toContinuousLinearMap.comp J).comp (L.toContinuousLinearMap.comp J).adjoint)).comp
        L.symm.toContinuousLinearMap.adjoint=J.comp J.adjoint := by
  have h : L.symm.toContinuousLinearMap.comp (L.toContinuousLinearMap.comp J)=J := by
    ext x
    exact L.symm_apply_apply (J x)
  calc
    _ = (L.symm.toContinuousLinearMap.comp (L.toContinuousLinearMap.comp J)).comp
        (L.symm.toContinuousLinearMap.comp (L.toContinuousLinearMap.comp J)).adjoint := by
      simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_assoc]
    _ = _ := by rw [h]

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
/-- Only the observed excess is charged the norm of the metric. -/
theorem metric_excess_energy_bound (b : HilbertBasis ι ℂ H)
    (L : H≃L[ℂ]H) (B E : H→L[ℂ]H)
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    hilbertSchmidtEnergy b ((similarityOperator L B).comp E)≤
      ‖L.toContinuousLinearMap‖^2 *
        hilbertSchmidtEnergy b (B.comp (L.symm.toContinuousLinearMap.comp E)) := by
  have hs := (right_comp_energy_bound b B (L.symm.toContinuousLinearMap.comp E) hB).1
  simpa only [similarityOperator,ContinuousLinearMap.comp_assoc] using
    (left_comp_energy_bound b L.toContinuousLinearMap
      (B.comp (L.symm.toContinuousLinearMap.comp E)) hs).2

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
/-- The difference of nested source projections is the exact orthogonal
excess. This identity retains a coefficient of one on the target energy. -/
theorem nested_source_energy_split (b : HilbertBasis ι ℂ H)
    (B : H→L[ℂ]H) (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hVU : V≤U)
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    hilbertSchmidtEnergy b (B.comp U.starProjection)=
      hilbertSchmidtEnergy b (B.comp V.starProjection)+
      hilbertSchmidtEnergy b (B.comp (U.starProjection-V.starProjection)) := by
  have hp : U.starProjection.comp V.starProjection=V.starProjection := by
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr (hVU (V.starProjection_apply_mem x))
  have hq : U.starProjection.comp Vᗮ.starProjection=U.starProjection-V.starProjection := by
    rw [Submodule.starProjection_orthogonal',ContinuousLinearMap.comp_sub,hp]
    rfl
  have hs := (right_comp_energy_bound b B U.starProjection hB).1
  simpa only [ContinuousLinearMap.comp_assoc,hp,hq] using
    source_projection_energy_split b V (B.comp U.starProjection) hs

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
/-- Counting in the actual transformed source, with the metric constant only
on its excess over the canonical subspace. No condition that the inverse
metric fix an orthogonal complement is required. -/
theorem similarity_count_nested_source (b : HilbertBasis ι ℂ H)
    (L : H≃L[ℂ]H) (B : H→L[ℂ]H)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hVU : V≤U) (v : κ→H) (hv : LinearIndependent ℂ v)
    (hU : ∀ i,L (v i)∈U) (a : κ→ℝ)
    (he : ∀ i,B (v i)=(a i:ℂ) • v i) (ha : ∀ i,1≤a i)
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    Finite κ ∧ (Nat.card κ:ℝ)≤
      hilbertSchmidtEnergy b ((similarityOperator L B).comp V.starProjection)+
      ‖L.toContinuousLinearMap‖^2 * hilbertSchmidtEnergy b
        (B.comp (L.symm.toContinuousLinearMap.comp (U.starProjection-V.starProjection))) := by
  have hvL : LinearIndependent ℂ (fun i => L (v i)) :=
    (L.toLinearMap.linearIndependent_iff_of_injOn L.injective.injOn).mpr hv
  have hs := similarityOperator_summable b L B hB
  have hsU := (right_comp_energy_bound b (similarityOperator L B) U.starProjection hs).1
  have heU (i : κ) : ((similarityOperator L B).comp U.starProjection) (L (v i))=
      (a i:ℂ) • L (v i) := by
    rw [ContinuousLinearMap.comp_apply,Submodule.starProjection_eq_self_iff.mpr (hU i)]
    exact similarityOperator_eigen L B _ _ (he i)
  obtain ⟨hf,hc⟩ := independent_eigenfamily_finite b
    ((similarityOperator L B).comp U.starProjection) _ hvL a heU ha hsU
  rw [nested_source_energy_split b (similarityOperator L B) U V hVU hs] at hc
  exact ⟨hf,hc.trans (add_le_add le_rfl
    (metric_excess_energy_bound b L B (U.starProjection-V.starProjection) hB))⟩

#print axioms metric_cogram_pullback
#print axioms metric_excess_energy_bound
#print axioms nested_source_energy_split
#print axioms similarity_count_nested_source
end QuantitativeMaass
