module

public import QuantitativeEulerEndpointSectorResidualDataV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticRegularTrace
open QuantitativeNewGap QuantitativeSpectralObservability
open scoped Classical lp

def sectorSampling (N : ℕ) (hN : 0<N) (sector : AsymptoticSectorSigns.Sector N) (Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (AsymptoticQuotientIncidence.space N hN hε ht sector x).starProjection.comp
    (fundamentalSampling N hN Y hε ht x)

theorem sectorSampling_mem (N : ℕ) (hN : 0<N) (sector : AsymptoticSectorSigns.Sector N) (Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ)) :
    sectorSampling N hN sector Y hε ht x v∈AsymptoticQuotientIncidence.space N hN hε ht sector x :=
  Submodule.starProjection_apply_mem _ _

theorem sectorSampling_norm (N : ℕ) (hN : 0<N) (sector : AsymptoticSectorSigns.Sector N) (Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) :
    ‖sectorSampling N hN sector Y hε ht x‖≤‖fundamentalSampling N hN Y hε ht x‖ := by
  calc
    _ ≤ ‖(AsymptoticQuotientIncidence.space N hN hε ht sector x).starProjection‖*
        ‖fundamentalSampling N hN Y hε ht x‖ := opNorm_comp_le _ _
    _ ≤ 1*‖fundamentalSampling N hN Y hε ht x‖ :=
      mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le _) (norm_nonneg _)
    _ = _ := one_mul _

theorem sectorSampling_regular (N : ℕ) (hN : 0<N) (sector : AsymptoticSectorSigns.Sector N) (Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) :
    (∀ g k, Measurable (fun x => matrix (sectorSampling N hN sector Y hε ht x) g k)) ∧
      Covariant (sectorSampling N hN sector Y hε ht) := by
  have hp := incidence_projection_regular N hN sector hε ht
  have hs := fundamentalSampling_regular N hN Y hε ht
  exact ⟨matrix_comp_measurable _ _ hp.1 hs.1,covariant_comp _ _ hp.2 hs.2⟩

def sectorGap (N : ℕ) (hN : 0<N) : ℝ :=
  (incidence_indexed_weighted_gap N hN).choose

theorem sectorGap_pos (N : ℕ) (hN : 0<N) : 0<sectorGap N hN :=
  (incidence_indexed_weighted_gap N hN).choose_spec.1

/-- The literal original-incidence sampler has the proved weight-uniform
gap. Both sums are the actual sampled old and canonical sign rows. -/
theorem sectorSampling_gap (N : ℕ) (hN : 0<N) (sector : Sector N) (Y : ℝ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ)
    (v : ℓ²(OrbitGroup,ℂ)) :
    sectorGap N hN*‖fundamentalSampling N hN Y hε ht x v-sectorSampling N hN sector Y hε ht x v‖^2≤
      (∑ i : PrimeOldIndex N,‖oldSampledRow N hN (primeOldGroup N hN i) (primeOld_le N hN i) Y hε ht x v‖^2)+
      ∑ i : SectorSignIndex N,‖sectorSampledRow N hN sector i Y hε ht x v‖^2 := by
  exact (incidence_indexed_weighted_gap N hN).choose_spec.2 sector hε ht x
    (fundamentalSampling N hN Y hε ht x v) (fundamentalSampling_range N hN Y hε ht x v)

#print axioms sectorSampling_regular
#print axioms sectorSampling_gap
end QuantitativeEulerEndpointPrepared
