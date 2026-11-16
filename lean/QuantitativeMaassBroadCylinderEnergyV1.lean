module

public import QuantitativeMaassBroadCrossSourceEnergyV1
public import QuantitativeMaassCylinderSquareKernelV1
public import QuantitativeMaassCylinderPacketKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap ENNReal

namespace QuantitativeMaass

/-- The full infinite-cylinder source integral is controlled by the
compact full-quotient deficit trace for the literal source time packet. -/
theorem broadCross_cylinder_column_energy_le
    (N : ℕ) [NeZero N] (L : ℝ) (hL : 0 < L) (t : ℝ)
    (K : Set ℍ) (hK : IsCompact K) (b : SmoothUpperSeed) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (m : ℕ) (hm : ∀ z : ℍ, ∀ S : Finset (gamma 0),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m)
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hD : IsSelfAdjoint D)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ s, star (f s)=f s)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    (∫⁻ z, ENNReal.ofReal (‖D (broadQuotientPacket N L hL t
      (crossQuotientLocalization N 0 K hK b hbound
        (cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z))))‖^2) ∂quotientMeasure 0) ≤
      ENNReal.ofReal (‖cylinderTimePacket f (f.smooth ⊤) hc‖^2)*ENNReal.ofReal (B^2*(m:ℝ))*
        ∫⁻ w in K, ENNReal.ofReal (‖D (broadAbelColumn N L hL t w)‖^2) := by
  apply broadCross_source_column_energy_le (quotientMeasure 0)
    (cylinderTimePacket f (f.smooth ⊤) hc) (cylinderTimeColumn f hc he R hR hs)
    _ N 0 cylinderAutomorphic L hL t K hK b B hB hbound m hm D hD
  intro v
  exact cylinderTimePacket_column_coeFn f (f.smooth ⊤) he hc hr R hR hs
    (evenCoshLift_support_of_time_support f R hR hs) v

#print axioms broadCross_cylinder_column_energy_le

end QuantitativeMaass
