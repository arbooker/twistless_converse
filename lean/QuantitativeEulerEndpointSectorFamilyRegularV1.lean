module

public import QuantitativeEulerEndpointSectorFamilyV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticRegularTrace AsymptoticCongruenceQuotient QuantitativeNewGap
open QuantitativeSpectralObservability QuantitativeSpectralObservabilitySampling QuantitativeSpectralCoverUnweight
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

theorem sectorFamilySampled_regular (N : ℕ) (hN : 0<N) (sector : Sector N)
    (Y : ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (i : SectorFamilyIndex N) :
    (∀ g k, Measurable (fun x => matrix (sectorFamilySampled N hN sector Y hε ht x i) g k)) ∧
      Covariant (fun x => sectorFamilySampled N hN sector Y hε ht x i) := by
  cases i with
  | inl i =>
    have hs := fundamentalSampling_regular N hN Y hε ht
    exact ⟨matrix_comp_measurable _ _
      (AsymptoticCongruenceOldSpace.projection_matrix_measurable N
        (primeOldGroup N hN i) (primeOld_le N hN i) hε ht) hs.1,
      covariant_comp _ _ (AsymptoticCongruenceOldSpace.projection_covariant N
        (primeOldGroup N hN i) (primeOld_le N hN i) hε ht) hs.2⟩
  | inr i => exact sectorSampledRow_regular N hN sector i Y hε ht

theorem sectorFamilySampled_bounded (N : ℕ) (hN : 0<N) (sector : Sector N)
    {Y : ℝ} (hY : 0≤Y) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    ∃ M : SectorFamilyIndex N → ℝ, (∀ i, 0≤M i) ∧
      ∀ x i, ‖sectorFamilySampled N hN sector Y hε ht x i‖≤M i := by
  let A := samplingBound N hN Y ε t*(8*coverBound N hN*(Y+3)+5)
  let M : SectorFamilyIndex N → ℝ
    | .inl _ => max 0 A
    | .inr i => max 0 (‖sectorSignRow N hN sector i‖*A)
  refine ⟨M,?_,?_⟩
  · intro i
    cases i <;> exact le_max_left _ _
  · intro x i
    cases i with
    | inl i =>
      apply le_trans _ (le_max_right 0 A)
      calc
        _ ≤ ‖(AsymptoticCongruenceOldSpace.space N (primeOldGroup N hN i)
              (primeOld_le N hN i) hε ht x).starProjection‖*
            ‖fundamentalSampling N hN Y hε ht x‖ := opNorm_comp_le _ _
        _ ≤ 1*‖fundamentalSampling N hN Y hε ht x‖ :=
          mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le _) (norm_nonneg _)
        _ ≤ A := by simpa only [one_mul] using fundamentalSampling_norm N hN Y hY hε ht x
    | inr i => exact (sectorSampledRow_norm N hN sector i Y hY hε ht x).trans (le_max_right _ _)

#print axioms sectorFamilySampled_regular
#print axioms sectorFamilySampled_bounded
end QuantitativeEulerEndpointPrepared
