module

public import QuantitativeMaassCylinderCenteredEnergyV1
public import QuantitativeMaassFiniteEnergyColumnV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap ENNReal

namespace QuantitativeMaass

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
  (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

def cylinderCenteredTimeColumn (z : ℍ) : Lp ℂ 2 (quotientMeasure 0) :=
  cylinderTimeColumn f hc he R hR hs z-
    ∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz)

theorem cylinderCenteredTimeColumn_continuous : Continuous (cylinderCenteredTimeColumn f hc he R hR hs) := by
  have hcol := cylinderAbelColumn_continuous (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) he hc) R hR
    (evenCoshLift_support_of_time_support f R hR hs)
  have hshift : Continuous (fun p : ℍ×ℝ => p.2+ᵥp.1) := by
    apply continuous_induced_rng.mpr
    fun_prop
  have hj := hcol.comp hshift
  have hm := continuous_parametric_integral_of_continuous
    (f:=fun (z : ℍ) (y : ℝ) => cylinderTimeColumn f hc he R hR hs (y+ᵥz))
    hj (μ:=volume) (s:=Icc (0:ℝ) 1) isCompact_Icc
  exact hcol.sub hm

include hr in
/-- The actual centered column is square integrable on every positive
terminal-height cutoff, with no trace or summability assumption. -/
theorem cylinderCenteredTimeColumn_memLp (Y : ℝ) (hY : 0<Y) :
    MemLp (cylinderCenteredTimeColumn f hc he R hR hs) 2
      (volume.restrict (AsymptoticCertificateOperators.highStrip Y)) := by
  have harea : volume (AsymptoticCertificateOperators.highStrip Y)≠⊤ :=
    (AsymptoticHyperbolicArea.closed_terminal_area hY).trans_ne ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (volume.restrict (AsymptoticCertificateOperators.highStrip Y)) :=
    isFiniteMeasure_restrict.mpr harea
  have hm : AEStronglyMeasurable (cylinderCenteredTimeColumn f hc he R hR hs)
      (volume.restrict (AsymptoticCertificateOperators.highStrip Y)) :=
    (cylinderCenteredTimeColumn_continuous f hc he R hR hs).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi : Integrable (fun _z : ℍ => 2*∫ v,‖deriv (parabolicLineProfile
      (abelProfile (evenCoshLift (timeConvolution f f))) 1) v‖)
      (volume.restrict (AsymptoticCertificateOperators.highStrip Y)) := integrable_const _
  apply hi.mono' (hm.norm.pow 2)
  filter_upwards with z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact cylinderTimeColumn_centered_energy_bound f hc he hr R hR hs z

/-- The concrete Hilbert-Schmidt packet with its output horizontal mean
removed and output restricted to positive terminal heights. -/
def cylinderCenteredTerminalPacket (Y : ℝ) (hY : 0<Y) :=
  finiteEnergyColumnOperator (volume.restrict (AsymptoticCertificateOperators.highStrip Y))
    (cylinderCenteredTimeColumn f hc he R hR hs)
    (cylinderCenteredTimeColumn_memLp f hc he hr R hR hs Y hY)

theorem cylinderCenteredTerminalPacket_summable {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0))) (Y : ℝ) (hY : 0<Y) :
    Summable (fun i => ‖cylinderCenteredTerminalPacket f hc he hr R hR hs Y hY (basis i)‖^2) :=
  finiteEnergyColumnOperator_summable _ _ _ basis

theorem cylinderCenteredTerminalPacket_energy_bound {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0))) (Y : ℝ) (hY : 0<Y) :
    (∑' i,ENNReal.ofReal (‖cylinderCenteredTerminalPacket f hc he hr R hR hs Y hY (basis i)‖^2))≤
      ENNReal.ofReal (2*∫ v,‖deriv (parabolicLineProfile
        (abelProfile (evenCoshLift (timeConvolution f f))) 1) v‖)*ENNReal.ofReal Y⁻¹ := by
  rw [cylinderCenteredTerminalPacket,finiteEnergyColumnOperator_energy]
  exact cylinderTimeColumn_centered_tail_bound f hc he hr R hR hs Y hY

#print axioms cylinderCenteredTimeColumn_continuous
#print axioms cylinderCenteredTimeColumn_memLp
#print axioms cylinderCenteredTerminalPacket_summable
#print axioms cylinderCenteredTerminalPacket_energy_bound

end QuantitativeMaass
