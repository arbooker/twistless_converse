module

public import QuantitativeSpectralObservabilityReconstructionV1
public import QuantitativeSpectralObservabilityNewTerminalV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set ContinuousLinearMap AsymptoticOrbitDiagonal
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticRegularReconstruction
open AsymptoticRegularBranchFamily
open scoped MatrixGroups lp

/-- Concrete observability in the input coordinates of the literal regular
reconstruction filter. Both observations act on the actual normalized
reconstructed vector, just as the original finite row Gram does. The three
removed errors are explicit boundary, upper-height and old-row tails. -/
theorem exists_reconstructed_new_observability {N Q : ℕ} {hQ : 0<Q}
    (A : Certificate N Q hQ) (hN : 0<N) (P : Parameters A) (e : Sector N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := normalizedRegularAmbientCountReconstruction A hN P e
    ∃ (W : Finset (List SL(2,ℤ))) (B : ℝ), 1≤B ∧
      ∀ Y : ℝ, max P'.ε⁻¹ 4≤Y → (∀ i, (primeOldData N hN S hS i).B≤Y) →
      ∀ (x : ℍ), fundamentalGood N x → ∀ v : ℓ²(OrbitGroup,ℂ),
        v∈TerminalSpace A P' x →
        corner (AsymptoticCertificateOperators.highStrip P'.ε\AsymptoticHyperbolicArea.terminal P'.ε) x (U x v)=0 →
        corner (AsymptoticHyperbolicArea.terminal Y) x (U x v)=0 →
        oldTailStack N hN (primeOldGroup N hN) (QuantitativeNewGap.primeOld_le N hN) Y
          (fun i => Y/(primeOldData N hN S hS i).C) P'.epsilon_pos
          (by omega : 1≤P'.s+4) x (U x v)=0 →
      ‖v‖^2≤(countReconstructionBound A P)^2*
        newObservationCost N hN S hS W B Y P'.ε (P'.s+4)*
          (‖primeOldDetector N hN S hS W Y P'.epsilon_pos (P'.s+4) x (U x v)‖^2+
            ‖newSampling N hN Y P'.epsilon_pos (by omega : 1≤P'.s+4) x (U x v)‖^2) := by
  dsimp only
  let P' := AsymptoticReconstructedCount.parameters A P
  let U := normalizedRegularAmbientCountReconstruction A hN P e
  obtain ⟨W,B,hB,hobs⟩ := exists_new_terminal_observability N hN S hS P'.epsilon_pos
  refine ⟨W,B,hB,?_⟩
  intro Y hY hdata x hx v hv hboundary hupper hold
  have ht : 1≤P'.s+4 := by omega
  have hn := terminal_input_le_reconstructed_terminal A hN P e x v hv
  rw [closed_terminal_corner_of_boundary_zero P'.ε x (U x v) hboundary] at hn
  have hn2 := pow_le_pow_left₀ (norm_nonneg v) hn 2
  rw [mul_pow] at hn2
  have ho := hobs Y hY hdata (P'.s+4) ht x hx (U x v) hupper hold
  have hh := mul_le_mul_of_nonneg_left ho (sq_nonneg (countReconstructionBound A P))
  exact hn2.trans (hh.trans_eq (by ring))

#print axioms exists_reconstructed_new_observability

end QuantitativeSpectralObservability
