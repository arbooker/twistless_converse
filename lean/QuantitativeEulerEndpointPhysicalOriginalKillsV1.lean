module

public import QuantitativeEulerEndpointPhysicalGramKillsV1
public import QuantitativeEulerEndpointPhysicalPacketGramV1
public import QuantitativeEulerEndpointInitialUnitExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic
open QuantitativeEulerEndpointBandExpression

/-- The original physical packet Gram vanishes on every band-supported common
solution of the original finite packet rows. -/
theorem original_packet_gram_kills {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (N : ℕ) (hN : 0<N) (w : ℂ) (t : ℕ) (l : List (EligiblePrime N))
    (H : ℝ) (C : ℕ → ℝ) (m : ℕ)
    (T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hPT : holomorphicSum (unitExpression ε H) m*T=T)
    (hET : ∀ i : Fin l.length,holomorphicSum (originalPacketSequenceExpression hs hε N hN w t l i) m*T=0) :
    holomorphicSum (originalPacketGramExpression hs hε N hN w t l H C) m*T=0 := by
  rw [originalPacketGramExpression,holomorphicSum_gramExpression,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [holomorphicSum_scale,holomorphicSum_compose]
  change (star (_ • (holomorphicSum (originalPacketSequenceExpression hs hε N hN w t l i) m*
    holomorphicSum (unitExpression ε H) m)))*(_ • (holomorphicSum
    (originalPacketSequenceExpression hs hε N hN w t l i) m*holomorphicSum (unitExpression ε H) m))*T=0
  rw [mul_assoc,smul_mul_assoc,mul_assoc,hPT,hET i]
  have hz (r : ℂ) : r • (0 : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)=0 := by
    apply ContinuousLinearMap.ext
    intro f
    change r • (0 : AsymptoticHyperbolicSlash.Space)=0
    exact smul_zero r
  rw [hz,mul_zero]

#print axioms original_packet_gram_kills
end QuantitativeEulerEndpointPrepared
namespace QuantitativeEulerEndpointInitialExpression
open UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointBandExpression

/-- The simultaneous original energy kills every band-supported exact common
solution of all original baseline rows. -/
theorem original_energy_kills (N : ℕ) [NeZero N] (sector : Sector N)
    {ι : Type*} [Fintype ι] (regions : ι → Set ℍ) (hs : ∀ i,IsCompact (regions i))
    {ε : ℝ} (hε : 0<ε) (H : ℝ) (t : ι → ℕ) (R Y Hobs a : ι → ℝ) (m : ℕ)
    (T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hPT : holomorphicSum (unitExpression ε H) m*T=T)
    (hET : ∀ i j,holomorphicSum (originalBaselineExpression N sector (hs i) hε (t i) j) m*T=0) :
    holomorphicSum (originalEnergyExpression N sector regions hs hε H t R Y Hobs a) m*T=0 := by
  exact QuantitativeEulerEndpointPhysicalGram.weighted_gram_kills ε H m T _ _ _ hPT hET

#print axioms original_energy_kills
end QuantitativeEulerEndpointInitialExpression
