module

public import QuantitativeArithmeticMaassMovingSpectralCompressionV1
public import QuantitativeArithmeticMaassMovingSmoothingTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

/-- A concrete finite-band column after the moving smooth transfer. -/
def movingBandColumn {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ C D : ℝ) (hδ : 0<δ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (ε : ℝ→ℝ) (G t : ℝ) (z : ℍ) : AutomorphicSpace N :=
  let L := Real.exp (G*Strong.strongScale t)
  let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
  letI : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
    N hN basis e he hgraph _ _
  let A := cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
  ((W.starProjection ((localCuspidalSpace N hN).orthogonalProjectionOnto
    (A (cylinderAutomorphic (column K hc hKe ε t z)))) : localCuspidalSpace N hN) : AutomorphicSpace N)

/-- The actual sharp moving-cutoff trace is approximated by a literal
finite principal-band trace. Neither a spectral tail bound nor a smoothing
error is assumed: both are supplied by the preceding analytic estimates. -/
theorem moving_sharp_finite_band_trace_limit {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (T : ℝ→AutomorphicSpace N→L[ℂ]AutomorphicSpace N)
    (hT : ∀ᶠ t in atTop,‖T t‖≤1)
    (hPT : ∀ᶠ t in atTop,(localCuspidalSpace N hN).starProjection*T t=T t)
    (hTP : ∀ᶠ t in atTop,T t*(localCuspidalSpace N hN).starProjection=T t) (W : ℝ) :
    ∃ D G : ℝ,0≤D ∧ 0<G ∧ Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (columnLinearTrace (quotientMeasure 0)
        (fun z => sharpCutoffTransfer N (movingLowerEdge δ C ε t) t (movingLowerEdge_pos hδ C ε t)
          (cylinderAutomorphic (column K hc hKe ε t z))) (T t)-
       columnLinearTrace (quotientMeasure 0)
        (movingBandColumn N hN basis e he hgraph δ C D hδ K hc hKe ε G t) (T t))/(t*ε t))
      atTop (𝓝 0) := by
  obtain ⟨D,hD,hsm⟩ := moving_sharp_smooth_cutoff_trace_limit K hc hKe hK hm ε hε hp N hδ C hC W T hT
  obtain ⟨G,hG,hsp⟩ := moving_supported_cutoff_spectral_compression N hN basis e he hgraph
    δ C D hδ hC hD K hc hKe hK hm ε hε hp T hT hPT hTP W
  refine ⟨D,G,hD,hG,?_⟩
  have hlim := hsm.add hsp
  simp only [add_zero] at hlim
  convert hlim using 1
  funext t
  have hid : supportedCutoffTraceDifference N hN basis e he hgraph
      (movingLowerEdge δ C ε t) D (movingLowerEdge_pos hδ C ε t) K hc hKe ε T G t =
      columnLinearTrace (quotientMeasure 0)
        (fun z => cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
          (cylinderAutomorphic (column K hc hKe ε t z))) (T t)-
      columnLinearTrace (quotientMeasure 0)
        (movingBandColumn N hN basis e he hgraph δ C D hδ K hc hKe ε G t) (T t) := rfl
  rw [hid]
  ring

#print axioms moving_sharp_finite_band_trace_limit
end QuantitativeMaass.Scheduled
