module

public import QuantitativeSpectralObservabilityNewSourceV1
public import QuantitativeSpectralExceptionalGoodDetectorV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open AsymptoticRegularBranchFamily QuantitativeSpectralFiniteReduction AsymptoticRegularTrace
open QuantitativeSpectralExceptionalReducedRows QuantitativeNewGap AsymptoticCornerKernel
open QuantitativeSpectralCornerCutRow QuantitativeSpectralExceptionalGoodRoot
open QuantitativeSpectralObservabilitySampling QuantitativeSpectralCoverUnweight
open scoped MatrixGroups lp ENNReal

def newObservationCost (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Y ε : ℝ) (t : ℕ) : ℝ :=
  (terminalObservationConstant S W*(1+B^2*(Y+3)^2)^(2*t))*
    (1+(totalNewGap N hN)⁻¹*primeOldCost N hN S hS Y ε t)

theorem newObservationCost_nonneg (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Y ε : ℝ) (t : ℕ) :
    0≤newObservationCost N hN S hS W B Y ε t := by
  have hL := zero_le_one.trans (terminalObservationConstant_ge_one S W)
  have hγ := (totalNewGap_pos N hN).le
  have hA := primeOldCost_nonneg N hN S hS Y ε t
  unfold newObservationCost
  positivity

def primeOldDetector (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (Y : ℝ) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  enlargedDetector (signedGenerators S)
    (fun i => oldBranches (primeOldRepresentatives N hN i))
    (fun i => oldCoefficients (I:=PrimeOldClasses N hN i) N (primeOldGroup N hN i))
    (enlargedRegion_compact (fun i => oldBranches (primeOldRepresentatives N hN i))
      (fun i => (primeOldData N hN S hS i).w)
      (fun i => wideCompactCover N (Y/(primeOldData N hN S hS i).C))
      (fun i => wideCompactCover_compact N hN (Y/(primeOldData N hN S hS i).C))
      (wordRegion_compact W hε Y)) hε t x

/-- The actual low-detector part of the tail survivor has trace at most
the literal total-new space. All analytic observation and range premises
of the spectral trace detector are discharged here. -/
theorem exists_new_source_trace (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (B : ℝ), 1≤B ∧
      ∀ Y : ℝ, max ε⁻¹ 4≤Y → (∀ i, (primeOldData N hN S hS i).B≤Y) →
      ∀ (t : ℕ) (ht : 1≤t)
        (P : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (P x)],
        (∀ g k, Measurable (fun x => matrix (P x).starProjection g k)) →
        Covariant (fun x => (P x).starProjection) →
        (∀ x, P x≤AsymptoticOrbitRegion.Space
          (AsymptoticHyperbolicArea.terminal ε\AsymptoticHyperbolicArea.terminal Y) x) →
      ∀ c : ℝ, 0<c → newObservationCost N hN S hS W B Y ε t*c^2<1 →
        trace volume (fun x =>
          (nextSpace (remaining (P x)
            (oldTailStack N hN (primeOldGroup N hN) (primeOld_le N hN) Y
              (fun i => Y/(primeOldData N hN S hS i).C) hε ht x))
            (primeOldDetector N hN S hS W Y hε t x) c).starProjection) ≤
          trace volume (fun x => (AsymptoticTotalNewCorner.stripSpace N hN hε ht x).starProjection) := by
  obtain ⟨W,B,hB,hobs⟩ := exists_new_source_observability N hN S hS hε
  refine ⟨W,B,hB,?_⟩
  intro Y hY hdata t ht P instP hmP hcP hP c hc hsmall
  have hY0 : 0≤Y := (by norm_num : (0:ℝ)≤4).trans ((le_max_right _ _).trans hY)
  let H := fun i => Y/(primeOldData N hN S hS i).C
  let Q := fun x => remaining (P x)
    (oldTailStack N hN (primeOldGroup N hN) (primeOld_le N hN) Y H hε ht x)
  have hQ := oldTailStack_survivor_regular N hN (primeOldGroup N hN) (primeOld_le N hN)
    hY0 H hε ht P hmP hcP
  obtain ⟨MD,_hMD,hMD,hmD,hcD⟩ := enlargedDetector_regular (signedGenerators S)
    (fun i => oldBranches (primeOldRepresentatives N hN i))
    (fun i => oldCoefficients (I:=PrimeOldClasses N hN i) N (primeOldGroup N hN i))
    (enlargedRegion_compact (fun i => oldBranches (primeOldRepresentatives N hN i))
      (fun i => (primeOldData N hN S hS i).w)
      (fun i => wideCompactCover N (Y/(primeOldData N hN S hS i).C))
      (fun i => wideCompactCover_compact N hN (Y/(primeOldData N hN S hS i).C))
      (wordRegion_compact W hε Y)) hε t
  have hC := newSampling_regular N hN Y hε ht
  let MC := samplingBound N hN Y ε t*(8*coverBound N hN*(Y+3)+5)
  have hMC (x : ℍ) : ‖newSampling N hN Y hε ht x‖≤MC :=
    (newSampling_norm N hN Y hε ht x).trans (fundamentalSampling_norm N hN Y hY0 hε ht x)
  apply observable_low_trace_good N hN Q (AsymptoticTotalNewCorner.stripSpace N hN hε ht)
    hQ.1 hQ.2 (primeOldDetector N hN S hS W Y hε t) (newSampling N hN Y hε ht)
    hmD hcD hC.1 hC.2 MD MC hMD hMC hc
    (newObservationCost_nonneg N hN S hS W B Y ε t) hsmall
  · intro x hx v hv
    exact hobs Y hY hdata t ht x hx v (hP x hv.1) hv.2
  · intro x _hx v _hv
    exact newSampling_mem N hN Y hε ht x v

#print axioms exists_new_source_trace

end QuantitativeSpectralObservability
