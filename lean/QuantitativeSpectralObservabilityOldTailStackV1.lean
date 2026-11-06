module

public import QuantitativeSpectralObservabilityOldTailRowsV1
public import AsymptoticRankSubadditivityV1
public import AsymptoticRegularStackPolarV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticRegularTrace AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open AsymptoticObservationStack AsymptoticPolarIsometry
open QuantitativeSpectralObservabilitySampling QuantitativeSpectralCoverUnweight
open scoped lp ENNReal

variable {I : Type*} [Fintype I]

def oldTailStack (N : ℕ) (hN : 0<N) (J : I → Subgroup OrbitGroup)
    (hJ : ∀ i, gamma N≤J i) [∀ i, Finite (J i ⧸ (gamma N).subgroupOf (J i))]
    (Y : ℝ) (H : I → ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) :
    ℓ²(OrbitGroup,ℂ) →L[ℂ] PiLp 2 (fun _ : I => ℓ²(OrbitGroup,ℂ)) :=
  stack (fun i => oldTailRow N hN (J i) (hJ i) Y (H i) hε ht x)

theorem oldTailStack_bounded (N : ℕ) (hN : 0<N) (J : I → Subgroup OrbitGroup)
    (hJ : ∀ i, gamma N≤J i) [∀ i, Finite (J i ⧸ (gamma N).subgroupOf (J i))]
    {Y : ℝ} (hY : 0≤Y) (H : I → ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    ∃ M : ℝ, 0≤M ∧ ∀ x, ‖oldTailStack N hN J hJ Y H hε ht x‖≤M := by
  let B := max 0 (samplingBound N hN Y ε t*(8*coverBound N hN*(Y+3)+5))
  have hB : 0≤B := le_max_left _ _
  refine ⟨‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℓ²(OrbitGroup,ℂ))).symm.toContinuousLinearMap‖*
    ∑ _i : I, B,mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => hB)),?_⟩
  intro x
  apply stack_norm_le _ (fun _ => B) (fun _ => hB)
  intro i
  exact (oldTailRow_norm_le_sampling N hN (J i) (hJ i) Y (H i) hε ht x).trans
    ((fundamentalSampling_norm N hN Y hY hε ht x).trans (le_max_right _ _))

omit [Fintype I] in
theorem oldTailStack_eq_zero_iff (N : ℕ) (hN : 0<N) (J : I → Subgroup OrbitGroup)
    (hJ : ∀ i, gamma N≤J i) [∀ i, Finite (J i ⧸ (gamma N).subgroupOf (J i))]
    (Y : ℝ) (H : I → ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (x : ℍ) (v : ℓ²(OrbitGroup,ℂ)) :
    oldTailStack N hN J hJ Y H hε ht x v=0 ↔
      ∀ i, oldTailRow N hN (J i) (hJ i) Y (H i) hε ht x v=0 :=
  stack_eq_zero_iff _ _

/-- Discard all actual old-row tail errors at once. The source rank cost
is at most the sum of the concrete tail areas, without a closed-range
or a supplied rank hypothesis. -/
theorem oldTailStack_source_rank (N : ℕ) (hN : 0<N) (J : I → Subgroup OrbitGroup)
    (hJ : ∀ i, gamma N≤J i) [∀ i, Finite (J i ⧸ (gamma N).subgroupOf (J i))]
    {Y : ℝ} (hY : 0≤Y) (H : I → ℝ) (hH : ∀ i, 0<H i)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    trace volume (fun x => (oldTailStack N hN J hJ Y H hε ht x).kerᗮ.starProjection)≤
      ∑ i, (CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (H i)⁻¹) := by
  obtain ⟨M,_hM,hbound⟩ := oldTailStack_bounded N hN J hJ hY H hε ht
  apply (stack_rank_le_sum volume AsymptoticRationalGroup.measurePreserving
    (fun x i => oldTailRow N hN (J i) (hJ i) Y (H i) hε ht x)
    (fun i => (oldTailRow_regular N hN (J i) (hJ i) Y (H i) hε ht).1)
    (fun i => (oldTailRow_regular N hN (J i) (hJ i) Y (H i) hε ht).2) M hbound).trans
  exact Finset.sum_le_sum (fun i _ => oldSampledTail_source_rank N hN (J i) (hJ i) hY hε ht (hH i))

theorem oldTailStack_absolute_regular (N : ℕ) (hN : 0<N) (J : I → Subgroup OrbitGroup)
    (hJ : ∀ i, gamma N≤J i) [∀ i, Finite (J i ⧸ (gamma N).subgroupOf (J i))]
    {Y : ℝ} (hY : 0≤Y) (H : I → ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    ∃ M : ℝ, 0≤M ∧ (∀ x, ‖absolute (oldTailStack N hN J hJ Y H hε ht x)‖≤M) ∧
      (∀ g h, Measurable (fun x => matrix (absolute (oldTailStack N hN J hJ Y H hε ht x)) g h)) ∧
      Covariant (fun x => absolute (oldTailStack N hN J hJ Y H hε ht x)) := by
  obtain ⟨M,hM,hbound⟩ := oldTailStack_bounded N hN J hJ hY H hε ht
  have hr := stack_absolute_regular
    (fun x i => oldTailRow N hN (J i) (hJ i) Y (H i) hε ht x)
    (fun i => (oldTailRow_regular N hN (J i) (hJ i) Y (H i) hε ht).1)
    (fun i => (oldTailRow_regular N hN (J i) (hJ i) Y (H i) hε ht).2) M hbound
  refine ⟨M,hM,?_,hr.1,hr.2⟩
  intro x
  simpa only [absolute_opNorm] using hbound x

#print axioms oldTailStack_source_rank
#print axioms oldTailStack_absolute_regular

end QuantitativeSpectralObservability
