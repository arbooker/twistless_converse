module

public import QuantitativeSpectralObservabilityNewTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set ContinuousLinearMap AsymptoticOrbitDiagonal
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open AsymptoticRegularBranchFamily QuantitativeSpectralFiniteReduction
open QuantitativeSpectralExceptionalReducedRows QuantitativeNewGap
open scoped MatrixGroups lp

/-- Removing the exact height-boundary row identifies closed and strict
terminal coordinates pointwise, including exceptional roots. -/
theorem closed_terminal_corner_of_boundary_zero (ε : ℝ) (x : ℍ)
    (v : ℓ²(OrbitGroup,ℂ))
    (hv : corner (AsymptoticCertificateOperators.highStrip ε\AsymptoticHyperbolicArea.terminal ε) x v=0) :
    corner (AsymptoticCertificateOperators.highStrip ε) x v=
      corner (AsymptoticHyperbolicArea.terminal ε) x v := by
  have hs : AsymptoticHyperbolicArea.terminal ε⊆AsymptoticCertificateOperators.highStrip ε :=
    fun _ hz => ⟨hz.1,hz.2.le⟩
  apply lp.ext
  funext g
  by_cases ht : g • x∈AsymptoticHyperbolicArea.terminal ε
  · simp only [corner_apply,ite_eq_left ht,ite_eq_left (hs ht)]
  · by_cases hc : g • x∈AsymptoticCertificateOperators.highStrip ε
    · have hz := congrArg (fun w : ℓ²(OrbitGroup,ℂ) => w g) hv
      have hb : g • x∈AsymptoticCertificateOperators.highStrip ε\AsymptoticHyperbolicArea.terminal ε := ⟨hc,ht⟩
      simp only [corner_apply,ite_eq_left hb,lp.coeFn_zero,Pi.zero_apply] at hz
      simp only [corner_apply,ite_eq_left hc,ite_eq_right ht,hz]
    · simp only [corner_apply,ite_eq_right hc,ite_eq_right ht]

/-- The projected terminal estimate applies to arbitrary reconstructed
vectors, not only vectors supported inside the terminal region. The upper
tail and the actual old-row tails are removed explicitly. -/
theorem exists_new_terminal_observability (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (B : ℝ), 1≤B ∧
      ∀ Y : ℝ, max ε⁻¹ 4≤Y → (∀ i, (primeOldData N hN S hS i).B≤Y) →
      ∀ (t : ℕ) (ht : 1≤t) (x : ℍ), fundamentalGood N x →
      ∀ u : ℓ²(OrbitGroup,ℂ),
        corner (AsymptoticHyperbolicArea.terminal Y) x u=0 →
        oldTailStack N hN (primeOldGroup N hN) (primeOld_le N hN) Y
          (fun i => Y/(primeOldData N hN S hS i).C) hε ht x u=0 →
      ‖corner (AsymptoticHyperbolicArea.terminal ε) x u‖^2≤
        newObservationCost N hN S hS W B Y ε t*
          (‖primeOldDetector N hN S hS W Y hε t x u‖^2+
            ‖newSampling N hN Y hε ht x u‖^2) := by
  let b := fun i => oldBranches (primeOldRepresentatives N hN i)
  let w := fun i => (primeOldData N hN S hS i).w
  let c := fun i => oldCoefficients (I:=PrimeOldClasses N hN i) N (primeOldGroup N hN i)
  let s := fun Y i => wideCompactCover N (Y/(primeOldData N hN S hS i).C)
  let hs := fun Y i => wideCompactCover_compact N hN (Y/(primeOldData N hN S hS i).C)
  obtain ⟨W,B,hB,_hW,hobs⟩ :=
    exists_enlarged_terminal_observability N hN S hS b w c s hs hε
  refine ⟨W,B,hB,?_⟩
  intro Y hY hdata t ht x hx u hupper htail
  have ho := hobs Y hY t ht x hx u
  dsimp only at ho
  rw [hupper,norm_zero,zero_pow (by omega),add_zero] at ho
  have hsum := terminal_word_sum_bound S W B Y
    ‖AsymptoticObservationStack.stack (enlargedRows (signedGenerators S) b c
      (enlargedRegion_compact b w (s Y) (hs Y) (wordRegion_compact W hε Y)) hε t x) u‖
    ‖fundamentalSampling N hN Y hε ht x u‖ t
  have ho' := ho.trans hsum
  rw [← enlargedDetector_norm_apply] at ho'
  have hg := newSampling_distance_le_detector N hN S hS hdata
    (wordRegion_compact W hε Y) hε ht x u htail
  have hK : 0≤terminalObservationConstant S W*(1+B^2*(Y+3)^2)^(2*t) := by
    have hL := zero_le_one.trans (terminalObservationConstant_ge_one S W)
    positivity
  have hA : 0≤(totalNewGap N hN)⁻¹*primeOldCost N hN S hS Y ε t :=
    mul_nonneg (inv_nonneg.mpr (totalNewGap_pos N hN).le) (primeOldCost_nonneg N hN S hS Y ε t)
  exact observability_projected (AsymptoticTotalNewCorner.stripSpace N hN hε ht x)
    (corner (AsymptoticHyperbolicArea.terminal ε) x u)
    (fundamentalSampling N hN Y hε ht x u) _ _ _ hK hA ho' hg

#print axioms closed_terminal_corner_of_boundary_zero
#print axioms exists_new_terminal_observability

end QuantitativeSpectralObservability
