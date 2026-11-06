module

public import QuantitativeEulerEndpointSectorTerminalV1
public import QuantitativeSpectralObservabilityReconstructionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane ContinuousLinearMap AsymptoticOrbitDiagonal AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularReconstruction
open QuantitativeHolomorphic QuantitativeEulerDensityGenerators
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- Sector observability in the ACTUAL input coordinates of the finite-count
filter. The detector and sampler act on the normalized reconstructed vector.
Boundary, upper and combined old/sign tails remain explicit hypotheses. -/
theorem exists_reconstructed_sector_observability {N Q : ℕ} {hQ : 0<Q}
    (A : Certificate N Q hQ) (hN : 0<N) (P : Parameters A) (sector : Sector N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := normalizedRegularAmbientCountReconstruction A hN P sector
    ∃ (W : Finset (List SL(2,ℤ))) (B : ℝ), 1≤B ∧
      ∀ H : ℝ, max P'.ε⁻¹ 4≤H → (∀ i, sectorFamilyB N hN sector S hS i≤H) →
      ∀ (x : ℍ), fundamentalGood N x → ∀ v : Space,
      v∈TerminalSpace A P' x →
      corner (AsymptoticCertificateOperators.highStrip P'.ε\AsymptoticHyperbolicArea.terminal P'.ε) x (U x v)=0 →
      corner (AsymptoticHyperbolicArea.terminal H) x (U x v)=0 →
      quotientTailStack N (fun i => H/sectorFamilyC N hN sector S hS i) P'.epsilon_pos
        (by omega : 1≤P'.s+4) (sectorFamilySampled N hN sector H P'.epsilon_pos (by omega : 1≤P'.s+4)) x (U x v)=0 →
      ‖v‖^2≤(countReconstructionBound A P)^2*
        sectorObservationCost N hN sector S hS W B H P'.ε (P'.s+4)*
          (‖sectorDetector N hN sector S hS W H P'.epsilon_pos (P'.s+4) x (U x v)‖^2+
            ‖sectorSampling N hN sector H P'.epsilon_pos (by omega : 1≤P'.s+4) x (U x v)‖^2) := by
  dsimp only
  let P' := AsymptoticReconstructedCount.parameters A P
  let U := normalizedRegularAmbientCountReconstruction A hN P sector
  obtain ⟨W,B,hB,hobs⟩ := exists_sector_terminal_observability N hN sector S hS P'.epsilon_pos
  refine ⟨W,B,hB,?_⟩
  intro H hH hdata x hx v hv hboundary hupper htail
  have hn := terminal_input_le_reconstructed_terminal A hN P sector x v hv
  rw [closed_terminal_corner_of_boundary_zero P'.ε x (U x v) hboundary] at hn
  have hn2 := pow_le_pow_left₀ (norm_nonneg v) hn 2
  rw [mul_pow] at hn2
  have ho := hobs H hH hdata (P'.s+4) (by omega) x hx (U x v) hupper htail
  have hh := mul_le_mul_of_nonneg_left ho (sq_nonneg (countReconstructionBound A P))
  exact hn2.trans (hh.trans_eq (by ring))

#print axioms exists_reconstructed_sector_observability
end QuantitativeEulerEndpointPrepared
