module

public import QuantitativeEulerEndpointReconstructedChainV1
public import QuantitativeSpectralExceptionalRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularReconstruction AsymptoticRegularTrace AsymptoticOrbitDiagonal
open AsymptoticFiniteBranch QuantitativeSpectralExceptionalRows MeasureTheory
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

theorem reconstructed_terminal_regular :
    (∀ g k,Measurable (fun z => matrix
      (TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z).starProjection g k)) ∧
    Covariant (fun z => (TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z).starProjection) := by
  simp only [TerminalSpace,region_projection]
  exact ⟨corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable)
    (AsymptoticCertificateOperators.highStrip_measurable _),corner_covariant _⟩

theorem reconstructed_terminal_supported (q : ℕ) [Fact q.Prime] (z : UpperHalfPlane) :
    Supported (integralGroup q)
      (TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z).starProjection := by
  simp only [TerminalSpace,region_projection]
  exact supported_corner _ _ _

theorem terminal_source_trace_le (F : UpperHalfPlane → Submodule ℂ RegularSpace)
    [∀ z,CompleteSpace (F z)]
    (hF : ∀ z,F z≤TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z) :
    trace volume (fun z => (F z).starProjection)≤
      ENNReal.ofReal (AsymptoticReconstructedCount.parameters A P).ε⁻¹ := by
  apply (projection_trace_mono volume F _ hF).trans_eq
  simp only [TerminalSpace,region_projection]
  rw [trace_corner volume (AsymptoticCertificateOperators.highStrip_measurable _)]
  exact AsymptoticHyperbolicArea.closed_terminal_area
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos

variable [NeZero N] (e : Sector N)
variable (F : UpperHalfPlane → Submodule ℂ RegularSpace) [∀ z,CompleteSpace (F z)]
variable (hF : ∀ z,F z≤TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z)

/-- The actual baseline cut cannot increase the original terminal-source
trace. No reconstruction norm factor is introduced. -/
theorem reconstructed_baseline_mass_le
    (hmF : ∀ g k,Measurable (fun z => matrix (F z).starProjection g k))
    (hcF : Covariant (fun z => (F z).starProjection))
    {s : Set UpperHalfPlane} (hs : IsCompact s) (a : ℝ) :
    cornerMass (closedReconstructedBaseline A P e F hF hs a)≤
      (trace volume (fun z => (F z).starProjection)).toReal := by
  have hf := (terminal_source_trace_le A P F hF).trans_lt ENNReal.ofReal_lt_top
  apply ENNReal.toReal_mono hf.ne
  apply (projection_trace_mono volume _ _
    (reconstructed_baseline_le A P e F hF hs a)).trans_eq
  exact reconstructed_image_trace A (NeZero.pos N) P e F hF hmF hcF

#print axioms reconstructed_terminal_regular
#print axioms reconstructed_terminal_supported
#print axioms terminal_source_trace_le
#print axioms reconstructed_baseline_mass_le
end QuantitativeEulerEndpointPrepared
