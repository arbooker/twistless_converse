module

public import QuantitativeSpectralObservabilityPrimeOldDataV1
public import QuantitativeSpectralObservabilityNewSamplerV1

set_option autoImplicit false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open AsymptoticRegularBranchFamily QuantitativeSpectralFiniteReduction
open QuantitativeSpectralExceptionalReducedRows QuantitativeNewGap
open scoped MatrixGroups lp

def totalNewGap (N : ℕ) (hN : 0<N) : ℝ :=
  (totalNew_indexed_weighted_gap N hN).choose

theorem totalNewGap_pos (N : ℕ) (hN : 0<N) : 0<totalNewGap N hN :=
  (totalNew_indexed_weighted_gap N hN).choose_spec.1

/-- The discarded part of the actual sampler is controlled by the same
single detector on the actual tail kernel. All prime gaps, coset data,
and retained-row factorizations have been instantiated. -/
theorem newSampling_distance_le_detector
    (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {Y : ℝ} (hY : ∀ i, (primeOldData N hN S hS i).B≤Y)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ))
    (hv : oldTailStack N hN (primeOldGroup N hN) (primeOld_le N hN) Y
      (fun i => Y/(primeOldData N hN S hS i).C) hε ht x v=0) :
    let b := fun i => oldBranches (primeOldRepresentatives N hN i)
    let w := fun i => (primeOldData N hN S hS i).w
    let c := fun i => oldCoefficients (I:=PrimeOldClasses N hN i) N (primeOldGroup N hN i)
    let s := fun i => wideCompactCover N (Y/(primeOldData N hN S hS i).C)
    let hs := fun i => wideCompactCover_compact N hN (Y/(primeOldData N hN S hS i).C)
    let hu' := enlargedRegion_compact b w s hs hu
    ‖fundamentalSampling N hN Y hε ht x v-newSampling N hN Y hε ht x v‖^2 ≤
      ((totalNewGap N hN)⁻¹*primeOldCost N hN S hS Y ε t)*
        ‖enlargedDetector (signedGenerators S) b c hu' hε t x v‖^2 := by
  dsimp only
  have hg := (totalNew_indexed_weighted_gap N hN).choose_spec.2 hε ht x
    (fundamentalSampling N hN Y hε ht x v) (fundamentalSampling_range N hN Y hε ht x v)
  have he := old_family_energy_le_detector N hN S (primeOldGroup N hN) (primeOld_le N hN)
    (primeOldRepresentatives N hN) (primeOldData N hN S hS) hY hu hε ht x v hv
  change totalNewGap N hN*
    ‖fundamentalSampling N hN Y hε ht x v-newSampling N hN Y hε ht x v‖^2≤
      ∑ i : PrimeOldIndex N,
        ‖oldSampledRow N hN (primeOldGroup N hN i) (primeOld_le N hN i) Y hε ht x v‖^2 at hg
  have h := mul_le_mul_of_nonneg_left (hg.trans he) (inv_nonneg.mpr (totalNewGap_pos N hN).le)
  simpa only [← mul_assoc,inv_mul_cancel₀ (totalNewGap_pos N hN).ne',one_mul,primeOldCost] using h

#print axioms newSampling_distance_le_detector

end QuantitativeSpectralObservability
