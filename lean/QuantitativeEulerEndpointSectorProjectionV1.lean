module

public import QuantitativeEulerEndpointSectorRowsV1
public import QuantitativeEulerEndpointCutResidualV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSector
open UpperHalfPlane FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticFiniteBranch QuantitativeEulerEndpointPrepared
open AsymptoticCompactObservationCount

variable {N Q : ℕ} {hQ : 0<Q} {A : Certificate N Q hQ}
    (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)

include hN in
theorem physicalSector_finiteDimensional :
    FiniteDimensional ℂ (LinearMap.range (physicalSectorMap P h e)) := by
  let _ := AsymptoticRamifiedSectors.sector_finiteDimensional hN A P h (h+1+P.s) e
  exact Module.Finite.range (physicalSectorMap P h e)

/-- The orthogonal projection onto the ACTUAL lifted coefficient sector. -/
def physicalSectorProjection :
    AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space := by
  let _ := physicalSector_finiteDimensional hN P h e
  exact (LinearMap.range (physicalSectorMap P h e)).starProjection

theorem physicalSectorProjection_mem (u : AsymptoticHyperbolicSlash.Space) :
    physicalSectorProjection hN P h e u ∈ LinearMap.range (physicalSectorMap P h e) := by
  let _ := physicalSector_finiteDimensional hN P h e
  exact (LinearMap.range (physicalSectorMap P h e)).starProjection_apply_mem u

theorem physicalSectorProjection_norm : ‖physicalSectorProjection hN P h e‖≤1 := by
  let _ := physicalSector_finiteDimensional hN P h e
  exact (LinearMap.range (physicalSectorMap P h e)).starProjection_norm_le

theorem row_projection_zero (r : Row N) {s : Set ℍ} (hs : IsCompact s) :
    holomorphicSum (rowExpression hN r e hs P.epsilon_pos (P.s+4)) (h+1)*
      physicalSectorProjection hN P h e=0 := by
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨a,ha⟩ := physicalSectorProjection_mem hN P h e u
  change holomorphicSum _ _ (physicalSectorProjection hN P h e u)=0
  rw [←ha]
  exact row_sector_zero hN P h e r hs a

theorem packet_projection_zero (q : ℕ) (hq : q.Prime) (hqN : ¬q∣N)
    {s : Set ℍ} (hs : IsCompact s) :
    holomorphicSum (originalPacketExpression hs P.epsilon_pos N q hN hq.pos
      (sign e.1) (P.s+4)) (h+1)*physicalSectorProjection hN P h e=0 := by
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨a,ha⟩ := physicalSectorProjection_mem hN P h e u
  change holomorphicSum _ _ (physicalSectorProjection hN P h e u)=0
  rw [←ha]
  exact packet_sector_zero hN P h e q hq hqN hs a

variable [NeZero N]

theorem baseline_projection_zero {s : Set ℍ} (hs : IsCompact s) (i : NewBaselineIndex N) :
    holomorphicSum (originalBaselineExpression N e hs P.epsilon_pos (P.s+4) i) (h+1)*
      physicalSectorProjection hN P h e=0 := by
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨a,ha⟩ := physicalSectorProjection_mem hN P h e u
  change holomorphicSum _ _ (physicalSectorProjection hN P h e u)=0
  rw [←ha]
  exact baseline_sector_zero P h e hs i a

#print axioms physicalSector_finiteDimensional
#print axioms physicalSectorProjection_mem
#print axioms physicalSectorProjection_norm
#print axioms row_projection_zero
#print axioms packet_projection_zero
#print axioms baseline_projection_zero
end QuantitativeEulerEndpointSector
