module

public import QuantitativeMaassCenteredNonzeroColumnV1
public import QuantitativeMaassCenteredTerminalPhysicalV1
public import QuantitativeMaassCylinderPhysicalV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- The actual finite-energy centered operator agrees with terminal
restriction of the capped packet on every nonzero-mode cylinder vector. -/
theorem physicalCenteredTerminalPacket_nonzero (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (ε : ℝ) (hε : 0<ε) (t : ℕ)
    (Y : ℝ) (hY : 0<Y) (v : Lp ℂ 2 (quotientMeasure 0)) (hv : v∈cylinderNonzeroModes) :
    physicalCenteredTerminalPacket f hc he hr R hR hs ε t Y hY v=
      AsymptoticCylinderTerminal.hyperProjection Y (cylinderZeroExtension
        (cylinderCappedTimePacket f (f.smooth ⊤) he hc hr R hR hs ε hε t v)) := by
  let w := cylinderCappedTimePacket f (f.smooth ⊤) he hc hr R hR hs ε hε t v
  have hw := cylinderZeroExtension_coeFn_of_ae w _
    (cylinderCappedTimePacket_column_coeFn f (f.smooth ⊤) he hc hr R hR hs
      (evenCoshLift_support_of_time_support f R hR hs) ε hε t v)
  apply Lp.ext
  filter_upwards [physicalCenteredTerminalPacket_coeFn f hc he hr R hR hs ε t Y hY v,
    AsymptoticRegionL2.projection_coeFn volume (AsymptoticCertificateOperators.highStrip Y)
      (AsymptoticCertificateOperators.highStrip_measurable Y) (cylinderZeroExtension w),hw]
    with z h1 h2 h3
  change AsymptoticCylinderTerminal.hyperProjection Y (cylinderZeroExtension w) z=_ at h2
  rw [h1,h2]
  classical
  by_cases hz : z∈AsymptoticCertificateOperators.highStrip Y
  · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz,h3,Set.indicator_of_mem hz.1]
    exact cylinderCenteredCappedColumn_nonzero f hc he hr R hR hs ε t z v hv
  · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz]

#print axioms physicalCenteredTerminalPacket_nonzero

end QuantitativeMaass
