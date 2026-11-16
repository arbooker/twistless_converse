module

public import QuantitativeMaassFullRegularTailCoreV1
public import QuantitativeSpectralExceptionalReconstructionTailAreaV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeMaass.FullRegularTail

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticRegularTrace AsymptoticCornerKernel AsymptoticOrbitDiagonal
open QuantitativeHolomorphic QuantitativeSpectralObservability QuantitativeSpectralExceptionalRows
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns AsymptoticHyperbolicArea
open scoped lp ENNReal

open QuantitativeSpectralExceptionalReconstructionTail (boundary boundary_measurable boundary_area)
open QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem corner_row_regular (hN : 0<N) (P : Parameters A) (e : Sector N)
    {s : Set ℍ} (hs : MeasurableSet s) :
    (∀ g k, Measurable (fun x => matrix (row A hN P e (corner s) x) g k)) ∧
      Covariant (row A hN P e (corner s)) :=
  row_regular A hN P e _
    (corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable) hs)
    (corner_covariant s)

theorem corner_row_norm (hN : 0<N) (P : Parameters A) (e : Sector N) (s : Set ℍ) (x : ℍ) :
    ‖row A hN P e (corner s) x‖≤1 :=
  (row_norm A hN P e _ x).trans (AsymptoticOrbitRegion.corner_norm_le s x)

theorem corner_rank_le_area (hN : 0<N) (P : Parameters A) (e : Sector N)
    {s : Set ℍ} (hs : MeasurableSet s) :
    trace volume (fun x => (row A hN P e (corner s) x).kerᗮ.starProjection)≤volume s := by
  have hU := normalizedRegularAmbient_regular A hN P e
  exact omitted_rank_le_area volume AsymptoticRationalGroup.measurePreserving hs
    (normalizedRegularAmbient A hN P e) hU.1 hU.2 1
    (normalizedRegularAmbient_norm A hN P e)

/-- The reconstructed high-tail row costs only its output area, with no
reconstruction norm factor. -/
theorem terminal_rank (hN : 0<N) (P : Parameters A) (e : Sector N) {H : ℝ} (hH : 0<H) :
    trace volume (fun x => (row A hN P e (corner (terminal H)) x).kerᗮ.starProjection)≤
      ENNReal.ofReal H⁻¹ :=
  (corner_rank_le_area A hN P e (terminal_measurable H)).trans_eq (terminal_area hH)

theorem boundary_rank (hN : 0<N) (P : Parameters A) (e : Sector N) {ε : ℝ} (hε : 0<ε) :
    trace volume (fun x => (row A hN P e (corner (boundary ε)) x).kerᗮ.starProjection)=0 :=
  le_antisymm ((corner_rank_le_area A hN P e (boundary_measurable ε)).trans_eq (boundary_area hε))
    (by positivity)

theorem corner_survivor_trace (hN : 0<N) (P : Parameters A) (e : Sector N)
    (V : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (V x)]
    (hmV : ∀ g k, Measurable (fun x => matrix (V x).starProjection g k))
    (hcV : Covariant (fun x => (V x).starProjection)) {s : Set ℍ} (hs : MeasurableSet s) :
    trace volume (fun x => (V x).starProjection)≤
      trace volume (fun x => (remaining (V x) (row A hN P e (corner s) x)).starProjection)+volume s := by
  have hr := corner_row_regular A hN P e hs
  exact (source_trace_le_remaining_add_rank V hmV hcV _ hr.1 hr.2 1
    (corner_row_norm A hN P e s)).trans (add_le_add le_rfl (corner_rank_le_area A hN P e hs))

theorem terminal_survivor_trace (hN : 0<N) (P : Parameters A) (e : Sector N)
    (V : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (V x)]
    (hmV : ∀ g k, Measurable (fun x => matrix (V x).starProjection g k))
    (hcV : Covariant (fun x => (V x).starProjection)) {H : ℝ} (hH : 0<H) :
    trace volume (fun x => (V x).starProjection)≤
      trace volume (fun x => (remaining (V x) (row A hN P e (corner (terminal H)) x)).starProjection)+
        ENNReal.ofReal H⁻¹ := by
  simpa only [terminal_area hH] using corner_survivor_trace A hN P e V hmV hcV (terminal_measurable H)

/-- Removing the reconstruction cutoff boundary has exactly zero trace
cost, although the boundary row need not vanish at every orbit root. -/
theorem boundary_survivor_trace (hN : 0<N) (P : Parameters A) (e : Sector N)
    (V : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (V x)]
    (hmV : ∀ g k, Measurable (fun x => matrix (V x).starProjection g k))
    (hcV : Covariant (fun x => (V x).starProjection)) {ε : ℝ} (hε : 0<ε) :
    trace volume (fun x => (V x).starProjection)=
      trace volume (fun x => (remaining (V x) (row A hN P e (corner (boundary ε)) x)).starProjection) := by
  apply le_antisymm
  · simpa only [boundary_area hε,add_zero] using
      corner_survivor_trace A hN P e V hmV hcV (boundary_measurable ε)
  · exact projection_trace_mono volume _ _ (fun _ => inf_le_left)

#print axioms terminal_rank
#print axioms boundary_rank
#print axioms boundary_survivor_trace

end QuantitativeMaass.FullRegularTail
