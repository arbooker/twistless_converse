module

public import QuantitativeSpectralObservabilityNewControlV1
public import QuantitativeSpectralExceptionalSourceObservabilityV1

set_option autoImplicit false
set_option maxHeartbeats 900000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open AsymptoticRegularBranchFamily QuantitativeSpectralFiniteReduction
open QuantitativeSpectralExceptionalReducedRows QuantitativeNewGap
open scoped MatrixGroups lp

/-- Actual source observability with the sample projected onto the literal
all-prime new space. The detector, old-row words and polynomial costs are
constructed; neither an observability estimate nor an old-gap hypothesis
is supplied. Tail errors vanish by membership in their actual common kernel. -/
theorem exists_new_source_observability (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (B : ℝ), 1≤B ∧
      ∀ Y : ℝ, max ε⁻¹ 4≤Y → (∀ i, (primeOldData N hN S hS i).B≤Y) →
      ∀ (t : ℕ) (ht : 1≤t) (x : ℍ), fundamentalGood N x →
      ∀ v : ℓ²(OrbitGroup,ℂ),
        v∈AsymptoticOrbitRegion.Space
          (AsymptoticHyperbolicArea.terminal ε\AsymptoticHyperbolicArea.terminal Y) x →
        oldTailStack N hN (primeOldGroup N hN) (primeOld_le N hN) Y
          (fun i => Y/(primeOldData N hN S hS i).C) hε ht x v=0 →
      let b := fun i => oldBranches (primeOldRepresentatives N hN i)
      let w := fun i => (primeOldData N hN S hS i).w
      let c := fun i => oldCoefficients (I:=PrimeOldClasses N hN i) N (primeOldGroup N hN i)
      let s := fun i => wideCompactCover N (Y/(primeOldData N hN S hS i).C)
      let hs := fun i => wideCompactCover_compact N hN (Y/(primeOldData N hN S hS i).C)
      let hu := enlargedRegion_compact b w s hs (wordRegion_compact W hε Y)
      ‖v‖^2≤(terminalObservationConstant S W*(1+B^2*(Y+3)^2)^(2*t))*
        (1+(totalNewGap N hN)⁻¹*primeOldCost N hN S hS Y ε t)*
        (‖enlargedDetector (signedGenerators S) b c hu hε t x v‖^2+
          ‖newSampling N hN Y hε ht x v‖^2) := by
  let b := fun i => oldBranches (primeOldRepresentatives N hN i)
  let w := fun i => (primeOldData N hN S hS i).w
  let c := fun i => oldCoefficients (I:=PrimeOldClasses N hN i) N (primeOldGroup N hN i)
  let s := fun Y i => wideCompactCover N (Y/(primeOldData N hN S hS i).C)
  let hs := fun Y i => wideCompactCover_compact N hN (Y/(primeOldData N hN S hS i).C)
  obtain ⟨W,B,hB,_hW,hobs⟩ :=
    exists_enlarged_source_observability N hN S hS b w c s hs hε
  refine ⟨W,B,hB,?_⟩
  intro Y hY hdata t ht x hx v hv htail
  have ho := hobs Y hY t ht x hx _ le_rfl v hv
  have hg := newSampling_distance_le_detector N hN S hS hdata
    (wordRegion_compact W hε Y) hε ht x v htail
  dsimp only at ho hg ⊢
  have hK : 0≤terminalObservationConstant S W*(1+B^2*(Y+3)^2)^(2*t) := by
    have hL := zero_le_one.trans (terminalObservationConstant_ge_one S W)
    positivity
  have hA : 0≤(totalNewGap N hN)⁻¹*primeOldCost N hN S hS Y ε t :=
    mul_nonneg (inv_nonneg.mpr (totalNewGap_pos N hN).le) (primeOldCost_nonneg N hN S hS Y ε t)
  exact observability_projected (AsymptoticTotalNewCorner.stripSpace N hN hε ht x)
    v (fundamentalSampling N hN Y hε ht x v) _ _ _ hK hA ho hg

#print axioms exists_new_source_observability

end QuantitativeSpectralObservability
