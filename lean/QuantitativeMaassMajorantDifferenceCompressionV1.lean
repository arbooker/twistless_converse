module

public import QuantitativeMaassMajorantBandColumnV1
public import QuantitativeMaassProjectedObservationV1
public import QuantitativeArithmeticMaassScheduledBroadErrorV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

/-- Square integrability of the actual compressed column, in the original
quotient Hilbert space. -/
theorem originalMajorantBandColumn_memLp {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ C D : ℝ) (hδ : 0<δ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (ε : ℝ→ℝ) (G t : ℝ) :
    MemLp (originalMajorantBandColumn N hN basis e he hgraph δ C D hδ K hc hKe ε G t)
      2 (quotientMeasure 0) := by
  have hx := originalMajorant_cutoff_memLp N hδ C D K hc hKe ε t
  let L := Real.exp (G*Strong.strongScale t)
  let V := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
  let : FiniteDimensional ℂ V := cuspPrincipalWindowSpace_finiteDimensional N hN basis e he hgraph _ _
  exact ((hx.continuousLinearMap_comp (localCuspidalSpace N hN).orthogonalProjectionOnto).continuousLinearMap_comp V.starProjection).continuousLinearMap_comp (localCuspidalSpace N hN).subtypeL

/-- Compress the difference of filtered and canonical traces in one
spectral band. This avoids choosing incompatible bands for two separate
compression estimates. -/
theorem originalMajorant_difference_cutoff_exact_band_compression {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ C D : ℝ) (hδ : 0<δ) (hC : 0≤C) (hD : 0≤D) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (F O : ℝ→AutomorphicSpace N→L[ℂ]AutomorphicSpace N)
    (M : ℝ) (hM : 0<M) (hF : ∀ᶠ t in atTop,‖F t‖≤M)
    (hO : ∀ᶠ t in atTop,‖O t‖≤1)
    (Q : AutomorphicSpace N→L[ℂ]AutomorphicSpace N) (hQ : ‖Q‖≤1)
    (hPQ : (localCuspidalSpace N hN).starProjection.comp Q=Q)
    (hQP : Q.comp (localCuspidalSpace N hN).starProjection=Q) (W : ℝ) :
    ∃ G : ℝ,0<G ∧ Tendsto (fun t =>
      let c := fun z => cutoffTransfer N (movingLowerEdge δ C ε t) D t
        (movingLowerEdge_pos hδ C ε t) (cylinderAutomorphic (originalMajorantColumn K hc hKe ε t z))
      let w := originalMajorantBandColumn N hN basis e he hgraph δ C D hδ K hc hKe ε
        (exactBandParameter G t) t
      Real.exp (W*Strong.strongScale t)*
        ((columnLinearTrace (quotientMeasure 0)
          (fun z => F t ((localCuspidalSpace N hN).starProjection (c z))) (O t)-
          columnLinearTrace (quotientMeasure 0) c Q)-
         (columnLinearTrace (quotientMeasure 0) (fun z => F t (w z)) (O t)-
          columnLinearTrace (quotientMeasure 0) w Q))/(t*ε t)) atTop (𝓝 0) := by
  let A := fun t => projectedObservation (localCuspidalSpace N hN) (F t) (O t)
  let T := fun t => A t-Q
  have hT : ∀ᶠ t in atTop,‖T t‖≤M^2+1 := by
    filter_upwards [hF,hO] with t hFt hOt
    exact (norm_sub_le (A t) Q).trans (add_le_add
      ((projectedObservation_norm _ (F t) (O t) hOt).trans
        (pow_le_pow_left₀ (norm_nonneg (F t)) hFt 2)) hQ)
  have hPT : ∀ᶠ t in atTop,(localCuspidalSpace N hN).starProjection*T t=T t := by
    filter_upwards with t
    change (localCuspidalSpace N hN).starProjection.comp (A t-Q)=A t-Q
    rw [comp_sub,hPQ,show (localCuspidalSpace N hN).starProjection.comp (A t)=A t from
      projectedObservation_left _ (F t) (O t)]
  have hTP : ∀ᶠ t in atTop,T t*(localCuspidalSpace N hN).starProjection=T t := by
    filter_upwards with t
    change (A t-Q).comp (localCuspidalSpace N hN).starProjection=A t-Q
    rw [sub_comp,hQP,show (A t).comp (localCuspidalSpace N hN).starProjection=A t from
      projectedObservation_right _ (F t) (O t)]
  obtain ⟨G,hG,hlim⟩ := originalMajorant_bounded_cutoff_exact_band_compression N hN basis e he hgraph
    δ C D hδ hC hD K hc hKe hK hm ε hε hp T (M^2+1) (by positivity) hT hPT hTP W
  refine ⟨G,hG,?_⟩
  convert hlim using 1
  funext t
  let c := fun z => cutoffTransfer N (movingLowerEdge δ C ε t) D t
    (movingLowerEdge_pos hδ C ε t) (cylinderAutomorphic (originalMajorantColumn K hc hKe ε t z))
  let w := originalMajorantBandColumn N hN basis e he hgraph δ C D hδ K hc hKe ε (exactBandParameter G t) t
  have hc' : MemLp c 2 (quotientMeasure 0) := originalMajorant_cutoff_memLp N hδ C D K hc hKe ε t
  have hw' : MemLp w 2 (quotientMeasure 0) := originalMajorantBandColumn_memLp N hN basis e he hgraph
    δ C D hδ K hc hKe ε _ t
  have hw (z : UpperHalfPlane) : (localCuspidalSpace N hN).starProjection (w z)=w z := by
    apply Submodule.starProjection_eq_self_iff.mpr
    exact (_ : localCuspidalSpace N hN).property
  change _ = Real.exp (W*Strong.strongScale t)*
    (columnLinearTrace (quotientMeasure 0) c (A t-Q)-
     columnLinearTrace (quotientMeasure 0) w (A t-Q))/(t*ε t)
  rw [columnLinearTrace_sub _ _ hc',columnLinearTrace_sub _ _ hw']
  dsimp only [A]
  rw [columnLinearTrace_projectedObservation,columnLinearTrace_projectedObservation]
  simp only [hw]
  rfl

#print axioms originalMajorantBandColumn_memLp
#print axioms originalMajorant_difference_cutoff_exact_band_compression
end QuantitativeMaass.Scheduled
