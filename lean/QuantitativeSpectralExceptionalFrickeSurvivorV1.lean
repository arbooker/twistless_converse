module

public import QuantitativeSpectralExceptionalFrickeControlV1

set_option autoImplicit false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalFricke

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticRegularTrace AsymptoticCornerKernel
open QuantitativeSpectralObservability QuantitativeSpectralObservabilitySampling
open QuantitativeSpectralCoverUnweight QuantitativeNewGap
open scoped MatrixGroups lp ENNReal

theorem tailRow_bounded_regular (N : ℕ) (hN : 0<N) (sign : ℝ)
    {Y : ℝ} (hY : 0≤Y) (H : ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    ∃ M : ℝ, (∀ x, ‖tailRow N hN sign Y H hε ht x‖≤M) ∧
      (∀ g k, Measurable (fun x => matrix (tailRow N hN sign Y H hε ht x) g k)) ∧
      Covariant (tailRow N hN sign Y H hε ht) := by
  have hq := fundamentalSubsetProjection_regular N hN hε ht (fundamentalTail_measurable N hN H)
  have hr := sampledRow_regular N hN sign Y hε ht
  refine ⟨‖countingRow N hN sign‖*(samplingBound N hN Y ε t*(8*coverBound N hN*(Y+3)+5)),?_,
    matrix_comp_measurable _ _ hq.1 hr.1,covariant_comp _ _ hq.2 hr.2⟩
  intro x
  calc
    _ ≤ ‖fundamentalSubsetProjection N hε ht (fundamentalTail N H) x‖*
        ‖sampledRow N hN sign Y hε ht x‖ := opNorm_comp_le _ _
    _ ≤ 1*‖sampledRow N hN sign Y hε ht x‖ := mul_le_mul_of_nonneg_right
      (fundamentalSubsetProjection_norm N hε ht Set.inter_subset_left x) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using sampledRow_norm N hN sign Y hY hε ht x

variable (N : ℕ) (hN : 0<N) (sign : ℝ) (S : Finset SL(2,ℤ))
  (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)

/-- The literal intersection of the old-tail survivor with the Fricke
tail kernel. No regular-root restriction is needed in its definition. -/
def survivor (Y : ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (P : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) (x : ℍ) : Submodule ℂ ℓ²(OrbitGroup,ℂ) :=
  remaining (remaining (P x)
    (oldTailStack N hN (primeOldGroup N hN) (primeOld_le N hN) Y
      (fun i => Y/(primeOldData N hN S hS i).C) hε ht x))
    (tailRow N hN sign Y (Y/(residualData N hN sign S hS).C) hε ht x)

instance survivor_complete (Y : ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (P : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (P x)] (x : ℍ) :
    CompleteSpace (survivor N hN sign S hS Y hε ht P x) := by
  unfold survivor
  infer_instance

theorem survivor_regular {Y : ℝ} (hY : 0≤Y) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (P : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (P x)]
    (hmP : ∀ g k, Measurable (fun x => matrix (P x).starProjection g k))
    (hcP : Covariant (fun x => (P x).starProjection)) :
    (∀ g k, Measurable (fun x => matrix (survivor N hN sign S hS Y hε ht P x).starProjection g k)) ∧
      Covariant (fun x => (survivor N hN sign S hS Y hε ht P x).starProjection) := by
  have ho := oldTailStack_survivor_regular N hN (primeOldGroup N hN) (primeOld_le N hN)
    hY (fun i => Y/(primeOldData N hN S hS i).C) hε ht P hmP hcP
  obtain ⟨M,hM,hm,hc⟩ := tailRow_bounded_regular N hN sign hY
    (Y/(residualData N hN sign S hS).C) hε ht
  exact remaining_regular _ ho.1 ho.2 _ hm hc M hM

/-- The joint tail survivor loses only the sum of the actual old-tail
areas and one actual Fricke-tail area. -/
theorem survivor_trace {Y : ℝ} (hY : 0<Y) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (P : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (P x)]
    (hmP : ∀ g k, Measurable (fun x => matrix (P x).starProjection g k))
    (hcP : Covariant (fun x => (P x).starProjection)) :
    trace volume (fun x => (P x).starProjection)≤
      trace volume (fun x => (survivor N hN sign S hS Y hε ht P x).starProjection)+
        ((∑ i, (CongruenceSubgroup.Gamma0 N).index*
          (3*ENNReal.ofReal (Y/(primeOldData N hN S hS i).C)⁻¹))+
          (CongruenceSubgroup.Gamma0 N).index*
          (3*ENNReal.ofReal (Y/(residualData N hN sign S hS).C)⁻¹)) := by
  let H := fun i => Y/(primeOldData N hN S hS i).C
  let Q := fun x => remaining (P x)
    (oldTailStack N hN (primeOldGroup N hN) (primeOld_le N hN) Y H hε ht x)
  have hQ := oldTailStack_survivor_regular N hN (primeOldGroup N hN) (primeOld_le N hN)
    hY.le H hε ht P hmP hcP
  have ho := oldTailStack_survivor_trace N hN (primeOldGroup N hN) (primeOld_le N hN)
    hY.le H (fun i => div_pos hY (primeOldData N hN S hS i).C_pos) hε ht P hmP hcP
  obtain ⟨M,hM,hm,hc⟩ := tailRow_bounded_regular N hN sign hY.le
    (Y/(residualData N hN sign S hS).C) hε ht
  have hf := source_trace_le_remaining_add_rank Q hQ.1 hQ.2
    (tailRow N hN sign Y (Y/(residualData N hN sign S hS).C) hε ht) hm hc M hM
  have hr := sampledTail_source_rank N hN sign hY.le hε ht
    (div_pos hY (residualData N hN sign S hS).C_pos)
  have hf' := hf.trans (add_le_add le_rfl hr)
  exact ho.trans ((add_le_add hf' le_rfl).trans_eq (by simp only [survivor,Q,H]; ac_rfl))

#print axioms tailRow_bounded_regular
#print axioms survivor_regular
#print axioms survivor_trace

end QuantitativeSpectralExceptionalFricke
