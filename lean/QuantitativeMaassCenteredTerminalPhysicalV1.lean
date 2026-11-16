module

public import QuantitativeMaassCenteredColumnOriginalV1
public import QuantitativeMaassFiniteEnergyCompositionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped SchwartzMap ContDiff

namespace QuantitativeMaass

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
  (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
  (ε : ℝ) (t : ℕ) (Y : ℝ) (hY : 0<Y)

/-- The centered finite-energy terminal output, extended by zero into
the same physical space used by the actual Euler reconstruction. -/
def physicalCenteredTerminalPacket :
    Lp ℂ 2 (quotientMeasure 0) →L[ℂ] AsymptoticHyperbolicSlash.Space :=
  (AsymptoticZeroExtension.isometry volume
    (AsymptoticCertificateOperators.highStrip Y)
    (AsymptoticCertificateOperators.highStrip_measurable Y)).toContinuousLinearMap.comp
      (cylinderCenteredCappedTerminalPacket f hc he hr R hR hs ε t Y hY)

theorem physicalCenteredTerminalPacket_coeFn (v : Lp ℂ 2 (quotientMeasure 0)) :
    physicalCenteredTerminalPacket f hc he hr R hR hs ε t Y hY v=ᵐ[volume]
      (AsymptoticCertificateOperators.highStrip Y).indicator
        (fun z => inner ℂ (cylinderCenteredCappedColumn f hc he R hR hs ε t z) v) := by
  have hp := cylinderCenteredCappedTerminalPacket_coeFn f hc he hr R hR hs ε t Y hY v
  have hz := AsymptoticZeroExtension.isometry_coeFn volume
    (AsymptoticCertificateOperators.highStrip Y)
    (AsymptoticCertificateOperators.highStrip_measurable Y)
    (cylinderCenteredCappedTerminalPacket f hc he hr R hR hs ε t Y hY v)
  exact hz.trans ((ae_eq_restrict_iff_indicator_ae_eq
    (AsymptoticCertificateOperators.highStrip_measurable Y)).mp hp)

theorem physicalCenteredTerminalPacket_composition_summable {G E ι : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Countable ι]
    (basis : HilbertBasis ι ℂ G) (A : G →L[ℂ] Lp ℂ 2 (quotientMeasure 0))
    (C : AsymptoticHyperbolicSlash.Space →L[ℂ] E) :
    Summable (fun i => ‖C (physicalCenteredTerminalPacket f hc he hr R hR hs ε t Y hY
      (A (basis i)))‖^2) :=
  finiteEnergyColumn_composition_summable _ _
    (cylinderCenteredCappedColumn_memLp f hc he hr R hR hs ε t Y hY) basis A
    (C.comp (AsymptoticZeroExtension.isometry volume
      (AsymptoticCertificateOperators.highStrip Y)
      (AsymptoticCertificateOperators.highStrip_measurable Y)).toContinuousLinearMap)

/-- The constructed Hilbert-Schmidt output agrees exactly with the
terminal restriction of the scalar packet on every original Euler wave. -/
theorem physicalCenteredTerminalPacket_original {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    physicalCenteredTerminalPacket f hc he hr R hR hs P.ε (P.s+3) Y hY
      (principalEulerCylinderLp hN A P r σ hb)=
      cosinePacket f r • AsymptoticCylinderTerminal.hyperProjection Y
        (principalEulerWeightedLp hN A P r σ hb) := by
  apply Lp.ext
  filter_upwards [physicalCenteredTerminalPacket_coeFn f hc he hr R hR hs P.ε (P.s+3) Y hY
    (principalEulerCylinderLp hN A P r σ hb),
    AsymptoticRegionL2.projection_coeFn volume (AsymptoticCertificateOperators.highStrip Y)
      (AsymptoticCertificateOperators.highStrip_measurable Y)
      (principalEulerWeightedLp hN A P r σ hb),
    principalEulerWeightedLp_coeFn hN A P r σ hb,
    Lp.coeFn_smul (cosinePacket f r) (AsymptoticCylinderTerminal.hyperProjection Y
      (principalEulerWeightedLp hN A P r σ hb))] with z h1 h2 h3 h4
  rw [h1,h4]
  change _=cosinePacket f r*AsymptoticCylinderTerminal.hyperProjection Y
    (principalEulerWeightedLp hN A P r σ hb) z
  change AsymptoticCylinderTerminal.hyperProjection Y
    (principalEulerWeightedLp hN A P r σ hb) z=_ at h2
  rw [h2]
  classical
  by_cases hz : z∈AsymptoticCertificateOperators.highStrip Y
  · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz,h3,
      AsymptoticWeightedBranches.stripSection,Set.indicator_of_mem hz.1,weighted_zero_eq_capped]
    exact cylinderCenteredCappedColumn_original hN A P r σ hb f hc he hr R hR hs z
  · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz,mul_zero]

#print axioms physicalCenteredTerminalPacket_coeFn
#print axioms physicalCenteredTerminalPacket_composition_summable
#print axioms physicalCenteredTerminalPacket_original

end QuantitativeMaass
