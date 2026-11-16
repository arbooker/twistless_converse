module

public import QuantitativeMaassMajorantBoundedCompressionV1
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

def originalMajorantBandColumn {ι : Type*} (N : ℕ) (hN : 0<N)
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
    (A (cylinderAutomorphic (originalMajorantColumn K hc hKe ε t z)))) : localCuspidalSpace N hN) : AutomorphicSpace N)

end QuantitativeMaass.Scheduled
