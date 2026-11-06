module

public import QuantitativeSpectralObservabilityOldTailRankV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticRegularTrace AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open scoped lp

def oldTailRow (N : ℕ) (hN : 0<N) (J : Subgroup OrbitGroup) (hJ : gamma N≤J)
    [Finite (J ⧸ (gamma N).subgroupOf J)] (Y H : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (fundamentalSubsetProjection N hε ht (fundamentalTail N H) x).comp
    (oldSampledRow N hN J hJ Y hε ht x)

theorem oldTailRow_regular (N : ℕ) (hN : 0<N)
    (J : Subgroup OrbitGroup) (hJ : gamma N≤J)
    [Finite (J ⧸ (gamma N).subgroupOf J)] (Y H : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) :
    (∀ g h, Measurable (fun x => matrix (oldTailRow N hN J hJ Y H hε ht x) g h)) ∧
      Covariant (oldTailRow N hN J hJ Y H hε ht) := by
  have hs := fundamentalSampling_regular N hN Y hε ht
  have hq := fundamentalSubsetProjection_regular N hN hε ht
    (fundamentalTail_measurable N hN H)
  exact ⟨matrix_comp_measurable _ _ hq.1
    (matrix_comp_measurable _ _
      (AsymptoticCongruenceOldSpace.projection_matrix_measurable N J hJ hε ht) hs.1),
    covariant_comp _ _ hq.2 (covariant_comp _ _
      (AsymptoticCongruenceOldSpace.projection_covariant N J hJ hε ht) hs.2)⟩

theorem oldTailRow_norm_le_sampling (N : ℕ) (hN : 0<N)
    (J : Subgroup OrbitGroup) (hJ : gamma N≤J)
    [Finite (J ⧸ (gamma N).subgroupOf J)] (Y H : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) :
    ‖oldTailRow N hN J hJ Y H hε ht x‖≤‖fundamentalSampling N hN Y hε ht x‖ := by
  have hp : ‖oldSampledRow N hN J hJ Y hε ht x‖≤
      ‖fundamentalSampling N hN Y hε ht x‖ := by
    calc
      _ ≤ ‖(AsymptoticCongruenceOldSpace.space N J hJ hε ht x).starProjection‖*
          ‖fundamentalSampling N hN Y hε ht x‖ := opNorm_comp_le _ _
      _ ≤ 1*‖fundamentalSampling N hN Y hε ht x‖ :=
        mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le _) (norm_nonneg _)
      _ = _ := one_mul _
  calc
    _ ≤ ‖fundamentalSubsetProjection N hε ht (fundamentalTail N H) x‖*
        ‖oldSampledRow N hN J hJ Y hε ht x‖ := opNorm_comp_le _ _
    _ ≤ 1*‖oldSampledRow N hN J hJ Y hε ht x‖ :=
      mul_le_mul_of_nonneg_right
        (fundamentalSubsetProjection_norm N hε ht inter_subset_left x) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using hp

#print axioms oldTailRow_regular
#print axioms oldTailRow_norm_le_sampling

end QuantitativeSpectralObservability
