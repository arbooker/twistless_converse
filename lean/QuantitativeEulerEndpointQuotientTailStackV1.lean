module

public import QuantitativeSpectralObservabilityOldTailSurvivorV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticRegularTrace AsymptoticCongruenceQuotient AsymptoticObservationStack AsymptoticPolarIsometry
open QuantitativeSpectralObservability AsymptoticCornerKernel
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

variable {I : Type*} [Fintype I]

def quotientTailRow (N : ℕ) (H : I → ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (B : ℍ → I → Space →L[ℂ] Space) (x : ℍ) (i : I) : Space →L[ℂ] Space :=
  (fundamentalSubsetProjection N hε ht (fundamentalTail N (H i)) x).comp (B x i)

def quotientTailStack (N : ℕ) (H : I → ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (B : ℍ → I → Space →L[ℂ] Space) (x : ℍ) : Space →L[ℂ] PiLp 2 (fun _ : I => Space) :=
  stack (quotientTailRow N H hε ht B x)

omit [Fintype I] in
theorem quotientTailRow_regular (N : ℕ) (hN : 0<N) (H : I → ℝ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (B : ℍ → I → Space →L[ℂ] Space)
    (hm : ∀ i g k, Measurable (fun x => matrix (B x i) g k))
    (hc : ∀ i, Covariant (fun x => B x i)) (i : I) :
    (∀ g k, Measurable (fun x => matrix (quotientTailRow N H hε ht B x i) g k)) ∧
      Covariant (fun x => quotientTailRow N H hε ht B x i) := by
  have hq := fundamentalSubsetProjection_regular N hN hε ht (fundamentalTail_measurable N hN (H i))
  exact ⟨matrix_comp_measurable _ _ hq.1 (hm i),covariant_comp _ _ hq.2 (hc i)⟩

omit [Fintype I] in
theorem quotientTailRow_norm (N : ℕ) (H : I → ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (B : ℍ → I → Space →L[ℂ] Space) (x : ℍ) (i : I) :
    ‖quotientTailRow N H hε ht B x i‖≤‖B x i‖ := by
  apply (opNorm_comp_le _ _).trans
  simpa only [fundamentalTail,one_mul] using mul_le_mul_of_nonneg_right
    (fundamentalSubsetProjection_norm N hε ht Set.inter_subset_left x) (norm_nonneg (B x i))

theorem quotientTailStack_bounded (N : ℕ) (H : I → ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (B : ℍ → I → Space →L[ℂ] Space)
    (M : I → ℝ) (hM : ∀ i, 0≤M i) (hb : ∀ x i, ‖B x i‖≤M i) :
    ∃ K : ℝ, 0≤K ∧ ∀ x, ‖quotientTailStack N H hε ht B x‖≤K := by
  refine ⟨‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => Space)).symm.toContinuousLinearMap‖*
    ∑ i,M i,mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun i _ => hM i)),?_⟩
  intro x
  exact stack_norm_le _ M hM (fun i => (quotientTailRow_norm N H hε ht B x i).trans (hb x i))

theorem quotientTailStack_absolute_regular (N : ℕ) (hN : 0<N) (H : I → ℝ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (B : ℍ → I → Space →L[ℂ] Space)
    (hm : ∀ i g k, Measurable (fun x => matrix (B x i) g k))
    (hc : ∀ i, Covariant (fun x => B x i))
    (M : I → ℝ) (hM : ∀ i, 0≤M i) (hb : ∀ x i, ‖B x i‖≤M i) :
    ∃ K : ℝ, 0≤K ∧ (∀ x, ‖absolute (quotientTailStack N H hε ht B x)‖≤K) ∧
      (∀ g k, Measurable (fun x => matrix (absolute (quotientTailStack N H hε ht B x)) g k)) ∧
      Covariant (fun x => absolute (quotientTailStack N H hε ht B x)) := by
  obtain ⟨K,hK,hbound⟩ := quotientTailStack_bounded N H hε ht B M hM hb
  have hr := quotientTailRow_regular N hN H hε ht B hm hc
  have he := stack_absolute_regular (quotientTailRow N H hε ht B)
    (fun i => (hr i).1) (fun i => (hr i).2) K hbound
  exact ⟨K,hK,fun x => by simpa only [absolute_opNorm] using hbound x,he⟩

theorem quotientTailStack_source_rank (N : ℕ) (hN : 0<N) (H : I → ℝ) (hH : ∀ i, 0<H i)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (B : ℍ → I → Space →L[ℂ] Space)
    (hm : ∀ i g k, Measurable (fun x => matrix (B x i) g k))
    (hc : ∀ i, Covariant (fun x => B x i))
    (M : I → ℝ) (hM : ∀ i, 0≤M i) (hb : ∀ x i, ‖B x i‖≤M i) :
    trace volume (fun x => (quotientTailStack N H hε ht B x).kerᗮ.starProjection)≤
      ∑ i,(CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (H i)⁻¹) := by
  obtain ⟨K,_hK,hbound⟩ := quotientTailStack_bounded N H hε ht B M hM hb
  have hr := quotientTailRow_regular N hN H hε ht B hm hc
  apply (stack_rank_le_sum volume AsymptoticRationalGroup.measurePreserving
    (quotientTailRow N H hε ht B) (fun i => (hr i).1) (fun i => (hr i).2) K hbound).trans
  exact Finset.sum_le_sum (fun i _ => fundamentalTail_source_rank N hN hε ht (hH i)
    (fun x => B x i) (hm i) (hc i) (M i) (fun x => hb x i))

/-- Any finite collection of actual quotient-row tail errors is removed
with its proved sum of input-rank costs, including old and sign rows. -/
theorem quotientTailStack_survivor_trace (N : ℕ) (hN : 0<N) (H : I → ℝ) (hH : ∀ i, 0<H i)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (B : ℍ → I → Space →L[ℂ] Space)
    (hm : ∀ i g k, Measurable (fun x => matrix (B x i) g k))
    (hc : ∀ i, Covariant (fun x => B x i))
    (M : I → ℝ) (hM : ∀ i, 0≤M i) (hb : ∀ x i, ‖B x i‖≤M i)
    (P : ℍ → Submodule ℂ Space) [∀ x, CompleteSpace (P x)]
    (hmP : ∀ g k, Measurable (fun x => matrix (P x).starProjection g k))
    (hcP : Covariant (fun x => (P x).starProjection)) :
    trace volume (fun x => (P x).starProjection)≤
      trace volume (fun x => (remaining (P x) (quotientTailStack N H hε ht B x)).starProjection)+
        ∑ i,(CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (H i)⁻¹) := by
  obtain ⟨K,_hK,hbound,hr⟩ := quotientTailStack_absolute_regular N hN H hε ht B hm hc M hM hb
  have he := source_trace_le_remaining_add_rank P hmP hcP
    (fun x => absolute (quotientTailStack N H hε ht B x)) hr.1 hr.2 K hbound
  simp only [remaining,absolute_ker] at he
  exact he.trans (add_le_add le_rfl (quotientTailStack_source_rank N hN H hH hε ht B hm hc M hM hb))

theorem quotientTailStack_survivor_regular (N : ℕ) (hN : 0<N) (H : I → ℝ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (B : ℍ → I → Space →L[ℂ] Space)
    (hm : ∀ i g k, Measurable (fun x => matrix (B x i) g k))
    (hc : ∀ i, Covariant (fun x => B x i))
    (M : I → ℝ) (hM : ∀ i, 0≤M i) (hb : ∀ x i, ‖B x i‖≤M i)
    (P : ℍ → Submodule ℂ Space) [∀ x, CompleteSpace (P x)]
    (hmP : ∀ g k, Measurable (fun x => matrix (P x).starProjection g k))
    (hcP : Covariant (fun x => (P x).starProjection)) :
    (∀ g k, Measurable (fun x => matrix
      (remaining (P x) (quotientTailStack N H hε ht B x)).starProjection g k)) ∧
      Covariant (fun x => (remaining (P x) (quotientTailStack N H hε ht B x)).starProjection) := by
  obtain ⟨K,_hK,hbound,hr⟩ := quotientTailStack_absolute_regular N hN H hε ht B hm hc M hM hb
  have he := remaining_regular P hmP hcP
    (fun x => absolute (quotientTailStack N H hε ht B x)) hr.1 hr.2 K hbound
  simpa only [remaining,absolute_ker] using he

#print axioms quotientTailStack_survivor_regular

#print axioms quotientTailStack_absolute_regular
#print axioms quotientTailStack_source_rank
#print axioms quotientTailStack_survivor_trace
end QuantitativeEulerEndpointPrepared
