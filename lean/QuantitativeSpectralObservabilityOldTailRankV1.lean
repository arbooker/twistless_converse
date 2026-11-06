module

public import QuantitativeSpectralObservabilityTailRankV1
public import QuantitativeSpectralObservabilityOldCoordinatesV1
public import AsymptoticCongruenceOldTraceV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticRegularTrace AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open QuantitativeSpectralObservabilitySampling QuantitativeSpectralCoverUnweight
open scoped lp ENNReal

theorem fundamentalSubsetProjection_norm (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) {s : Set ℍ} (hs : s⊆fundamentalSet N) (x : ℍ) :
    ‖fundamentalSubsetProjection N hε ht s x‖≤1 := by
  let : CompleteSpace (fundamentalSubsetSpace N hε ht s x) :=
    fundamentalSubsetSpace_complete N hε ht hs x
  rw [← fundamentalSubsetSpace_projection N hε ht hs x]
  exact Submodule.starProjection_norm_le _

/-- The input rank of the actual discarded row obeys the same tail-area
bound. Regularity and a uniform norm bound suffice; no closed-range
assumption or injectivity premise is used. -/
theorem fundamentalTail_source_rank (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) {H : ℝ} (hH : 0<H)
    (B : ℍ → ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ))
    (hm : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hc : Covariant B)
    (M : ℝ) (hM : ∀ x, ‖B x‖≤M) :
    trace volume (fun x =>
      ((fundamentalSubsetProjection N hε ht (fundamentalTail N H) x).comp (B x)).kerᗮ.starProjection)≤
      (CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal H⁻¹) := by
  have hq := fundamentalSubsetProjection_regular N hN hε ht
    (fundamentalTail_measurable N hN H)
  have hb (x : ℍ) :
      ‖(fundamentalSubsetProjection N hε ht (fundamentalTail N H) x).comp (B x)‖≤M := by
    calc
      _ ≤ ‖fundamentalSubsetProjection N hε ht (fundamentalTail N H) x‖*‖B x‖ :=
        opNorm_comp_le _ _
      _ ≤ 1*‖B x‖ := mul_le_mul_of_nonneg_right
        (fundamentalSubsetProjection_norm N hε ht inter_subset_left x) (norm_nonneg _)
      _ ≤ M := by simpa only [one_mul] using hM x
  rw [support_trace_eq volume AsymptoticRationalGroup.measurePreserving _
    (matrix_comp_measurable _ _ hq.1 hm) (covariant_comp _ _ hq.2 hc) M hb]
  exact fundamentalTail_error_rank N hN hε ht hH B

def oldSampledRow (N : ℕ) (hN : 0<N) (J : Subgroup OrbitGroup) (hJ : gamma N≤J)
    [Finite (J ⧸ (gamma N).subgroupOf J)] (Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (AsymptoticCongruenceOldSpace.space N J hJ hε ht x).starProjection.comp
    (fundamentalSampling N hN Y hε ht x)

/-- Concrete old-space rows meet every regularity and boundedness
requirement in the source-rank estimate. -/
theorem oldSampledTail_source_rank (N : ℕ) (hN : 0<N)
    (J : Subgroup OrbitGroup) (hJ : gamma N≤J)
    [Finite (J ⧸ (gamma N).subgroupOf J)] {Y : ℝ} (hY : 0≤Y)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) {H : ℝ} (hH : 0<H) :
    trace volume (fun x => ((fundamentalSubsetProjection N hε ht (fundamentalTail N H) x).comp
      (oldSampledRow N hN J hJ Y hε ht x)).kerᗮ.starProjection)≤
      (CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal H⁻¹) := by
  have hr := fundamentalSampling_regular N hN Y hε ht
  apply fundamentalTail_source_rank N hN hε ht hH _
    (matrix_comp_measurable _ _
      (AsymptoticCongruenceOldSpace.projection_matrix_measurable N J hJ hε ht) hr.1)
    (covariant_comp _ _
      (AsymptoticCongruenceOldSpace.projection_covariant N J hJ hε ht) hr.2)
    (samplingBound N hN Y ε t*(8*coverBound N hN*(Y+3)+5))
  intro x
  calc
    _ ≤ ‖(AsymptoticCongruenceOldSpace.space N J hJ hε ht x).starProjection‖*
        ‖fundamentalSampling N hN Y hε ht x‖ := opNorm_comp_le _ _
    _ ≤ 1*‖fundamentalSampling N hN Y hε ht x‖ :=
      mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le _) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using fundamentalSampling_norm N hN Y hY hε ht x

#print axioms fundamentalTail_source_rank
#print axioms oldSampledTail_source_rank

end QuantitativeSpectralObservability
