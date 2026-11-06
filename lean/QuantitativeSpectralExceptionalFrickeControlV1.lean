module

public import QuantitativeSpectralExceptionalFrickeFamilyV1
public import QuantitativeSpectralExceptionalFrickeSamplerV1
public import QuantitativeSpectralObservabilityPrimeOldDataV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalFricke

open UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticRegularBranchFamily
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows QuantitativeNewGap
open scoped MatrixGroups lp

def signedGap (N : ℕ) (hN : 0<N) : ℝ := (signedNew_indexed_weighted_gap N hN).choose

theorem signedGap_pos (N : ℕ) (hN : 0<N) : 0<signedGap N hN :=
  (signedNew_indexed_weighted_gap N hN).choose_spec.1

def primeFamilyBranches (N : ℕ) (hN : 0<N) :=
  familyBranches N hN (primeOldGroup N hN) (primeOldRepresentatives N hN)

def primeFamilyCoefficients (N : ℕ) (hN : 0<N) (sign : ℝ) :=
  familyCoefficients (I:=PrimeOldClasses N hN) N sign (primeOldGroup N hN)

variable (N : ℕ) (hN : 0<N) (sign : ℝ) (S : Finset SL(2,ℤ))
  (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)

def primeFamilyWords := familyWords N hN sign S (primeOldGroup N hN) (primeOld_le N hN)
  (primeOldRepresentatives N hN) (primeOldData N hN S hS) (residualData N hN sign S hS)

def primeFamilyRegions := familyRegions N hN sign S (primeOldGroup N hN) (primeOld_le N hN)
  (primeOldRepresentatives N hN) (primeOldData N hN S hS) (residualData N hN sign S hS)

theorem primeFamilyRegions_compact (Y : ℝ) (i : Option (PrimeOldIndex N)) :
    IsCompact (primeFamilyRegions N hN sign S hS Y i) :=
  familyRegions_compact N hN sign S (primeOldGroup N hN) (primeOld_le N hN)
    (primeOldRepresentatives N hN) (primeOldData N hN S hS) (residualData N hN sign S hS) Y i

def primeFamilyCost := familyCost N hN sign S (primeOldGroup N hN) (primeOld_le N hN)
  (primeOldRepresentatives N hN) (primeOldData N hN S hS) (residualData N hN sign S hS)

theorem primeFamilyCost_nonneg (Y ε : ℝ) (t : ℕ) : 0≤primeFamilyCost N hN sign S hS Y ε t :=
  add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)

/-- Actual signed-new distance controlled by the common enlarged detector.
Both the prime old-row data and the Fricke data are constructed here. -/
theorem signedSampling_distance_le_detector (hsign : sign^2=1)
    {Y : ℝ} (hY : ∀ i, (primeOldData N hN S hS i).B≤Y)
    (hfY : (residualData N hN sign S hS).B≤Y)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (x : ℍ) (v : ℓ²(OrbitGroup,ℂ))
    (hv : oldTailStack N hN (primeOldGroup N hN) (primeOld_le N hN) Y
      (fun i => Y/(primeOldData N hN S hS i).C) hε ht x v=0)
    (hvf : tailRow N hN sign Y (Y/(residualData N hN sign S hS).C) hε ht x v=0) :
    let b := primeFamilyBranches N hN
    let c := primeFamilyCoefficients N hN sign
    let w := primeFamilyWords N hN sign S hS
    let hs := primeFamilyRegions_compact N hN sign S hS Y
    let hu' := enlargedRegion_compact b w (primeFamilyRegions N hN sign S hS Y) hs hu
    ‖fundamentalSampling N hN Y hε ht x v-signedSampling N hN sign Y hε ht x v‖^2≤
      ((signedGap N hN)⁻¹*primeFamilyCost N hN sign S hS Y ε t)*
        ‖enlargedDetector (signedGenerators S) b c hu' hε t x v‖^2 := by
  dsimp only
  have hg := (signedNew_indexed_weighted_gap N hN).choose_spec.2 sign hsign hε ht x
    (fundamentalSampling N hN Y hε ht x v) (fundamentalSampling_range N hN Y hε ht x v)
  have he := family_energy_le_detector N hN sign S (primeOldGroup N hN) (primeOld_le N hN)
    (primeOldRepresentatives N hN) (primeOldData N hN S hS) (residualData N hN sign S hS)
    hY hfY hu hε ht x v hv hvf
  change signedGap N hN*
    ‖fundamentalSampling N hN Y hε ht x v-signedSampling N hN sign Y hε ht x v‖^2≤
      (∑ i : PrimeOldIndex N,
        ‖oldSampledRow N hN (primeOldGroup N hN i) (primeOld_le N hN i) Y hε ht x v‖^2)+
        ‖sampledRow N hN sign Y hε ht x v‖^2 at hg
  have h := mul_le_mul_of_nonneg_left (hg.trans he) (inv_nonneg.mpr (signedGap_pos N hN).le)
  simpa only [← mul_assoc,inv_mul_cancel₀ (signedGap_pos N hN).ne',one_mul,
    primeFamilyCost,primeFamilyBranches,primeFamilyCoefficients,primeFamilyWords,
    primeFamilyRegions,primeFamilyRegions_compact] using h

#print axioms signedSampling_distance_le_detector

end QuantitativeSpectralExceptionalFricke
