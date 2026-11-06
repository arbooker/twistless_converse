module

public import QuantitativeEulerEndpointReconstructedPullbackV1
public import QuantitativeSpectralExceptionalRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularReconstruction AsymptoticFiniteBranch AsymptoticRegularTrace
open AsymptoticOrbitDiagonal QuantitativeSpectralExceptionalRows MeasureTheory
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)
variable (hN : 0<N) (P : Parameters A) (e : Sector N)
variable (F V : UpperHalfPlane → Submodule ℂ RegularSpace)
variable [∀ z, CompleteSpace (F z)] [∀ z, CompleteSpace (V z)]
variable (hF : ∀ z,F z≤TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z)
variable (hV : ∀ z,V z≤reconstructedImage A hN P e F hF z)

include hF hV in
/-- Every regular surviving reconstructed subspace has trace bounded by the
fixed terminal area. No band cutoff or finite-trace premise is needed. -/
theorem reconstructed_image_trace_le_terminal
    (hmV : ∀ g k,Measurable (fun z => matrix (V z).starProjection g k))
    (hcV : Covariant (fun z => (V z).starProjection)) :
    trace volume (fun z => (V z).starProjection) ≤
      ENNReal.ofReal (AsymptoticReconstructedCount.parameters A P).ε⁻¹ := by
  rw [← reconstructed_pullback_trace A hN P e F V hF hV hmV hcV]
  calc
    _ ≤ trace volume (fun z => (TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z).starProjection) :=
      projection_trace_mono volume _ _ (fun z =>
        (reconstructed_pullback_le A hN P e F V hF hV z).trans (hF z))
    _ = _ := by
      simp only [TerminalSpace,region_projection]
      rw [trace_corner volume (AsymptoticCertificateOperators.highStrip_measurable _)]
      exact AsymptoticHyperbolicArea.closed_terminal_area
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos

include hF hV in
theorem reconstructed_image_trace_finite
    (hmV : ∀ g k,Measurable (fun z => matrix (V z).starProjection g k))
    (hcV : Covariant (fun z => (V z).starProjection)) :
    trace volume (fun z => (V z).starProjection)<∞ :=
  (reconstructed_image_trace_le_terminal A hN P e F V hF hV hmV hcV).trans_lt ENNReal.ofReal_lt_top

#print axioms reconstructed_image_trace_le_terminal
#print axioms reconstructed_image_trace_finite
end QuantitativeEulerEndpointPrepared
