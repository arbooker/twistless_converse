module

public import QuantitativeMaassCylinderCenteredOperatorV1
public import QuantitativeMaassConjugatedColumnIntegrableV1
public import QuantitativeMaassConjugatedColumnMeanV1
public import QuantitativeMaassCylinderCappedColumnsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped ContDiff SchwartzMap ENNReal

namespace QuantitativeMaass

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
  (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
  (ε : ℝ) (t : ℕ)

/-- The actual centered Abel column after finite-band capped conjugation. -/
def cylinderCenteredCappedColumn (z : ℍ) : Lp ℂ 2 (quotientMeasure 0) :=
  LogBands.conjugatedColumn (quotientMeasure 0)
    (fun w => Real.log (cappedHeightWeight ε t w)) (cappedHeightWeight_log_measurable ε t)
    (cylinderCenteredTimeColumn f hc he R hR hs) ⌈(t:ℝ)*R+1⌉₊ z

/-- Horizontal averaging commutes with the capped column map because
the weight and the output band depend only on height. -/
theorem cylinderCenteredCappedColumn_eq (z : ℍ) :
    cylinderCenteredCappedColumn f hc he R hR hs ε t z =
      cylinderCappedTimeColumn f (f.smooth ⊤) he hc R hR
        (evenCoshLift_support_of_time_support f R hR hs) ε t z -
      ∫ y in Icc (0:ℝ) 1,
        cylinderCappedTimeColumn f (f.smooth ⊤) he hc R hR
          (evenCoshLift_support_of_time_support f R hR hs) ε t (y+ᵥz) := by
  have hcol := cylinderAbelColumn_continuous (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) he hc) R hR
    (evenCoshLift_support_of_time_support f R hR hs)
  have hi : IntegrableOn (fun y : ℝ => cylinderTimeColumn f hc he R hR hs (y+ᵥz))
      (Icc (0:ℝ) 1) volume :=
    (hcol.comp (cylinder_vadd_continuous z)).continuousOn.integrableOn_compact isCompact_Icc
  have hheight (y : ℝ) :
      Real.log (cappedHeightWeight ε t (y+ᵥz))=Real.log (cappedHeightWeight ε t z) := by
    simp only [cappedHeightWeight,vadd_im]
  change LogBands.conjugatedColumn _ _ _ (cylinderCenteredTimeColumn f hc he R hR hs) _ z =
    LogBands.conjugatedColumn _ _ _ (cylinderTimeColumn f hc he R hR hs) _ z -
      ∫ y in Icc (0:ℝ) 1,
        LogBands.conjugatedColumn _ _ _ (cylinderTimeColumn f hc he R hR hs) _ (y+ᵥz)
  rw [LogBands.conjugatedColumn_curve_mean _ _ _ _ _ z (fun y => y+ᵥz) hheight hi]
  simp only [LogBands.conjugatedColumn,cylinderCenteredTimeColumn,smul_sub,map_sub]

include hr in
theorem cylinderCenteredCappedColumn_memLp (Y : ℝ) (hY : 0<Y) :
    MemLp (cylinderCenteredCappedColumn f hc he R hR hs ε t) 2
      (volume.restrict (AsymptoticCertificateOperators.highStrip Y)) :=
  LogBands.conjugatedColumn_memLp _ _ _ _ _
    (cylinderCenteredTimeColumn_memLp f hc he hr R hR hs Y hY) _

/-- The weighted centered terminal packet is constructed from its actual
columns; its square summability is proved, rather than assumed. -/
def cylinderCenteredCappedTerminalPacket (Y : ℝ) (hY : 0<Y) :=
  finiteEnergyColumnOperator (volume.restrict (AsymptoticCertificateOperators.highStrip Y))
    (cylinderCenteredCappedColumn f hc he R hR hs ε t)
    (cylinderCenteredCappedColumn_memLp f hc he hr R hR hs ε t Y hY)

theorem cylinderCenteredCappedTerminalPacket_coeFn (Y : ℝ) (hY : 0<Y)
    (v : Lp ℂ 2 (quotientMeasure 0)) :
    cylinderCenteredCappedTerminalPacket f hc he hr R hR hs ε t Y hY v
      =ᵐ[volume.restrict (AsymptoticCertificateOperators.highStrip Y)]
        (fun z => inner ℂ (cylinderCenteredCappedColumn f hc he R hR hs ε t z) v) :=
  finiteEnergyColumnOperator_coeFn _ _ _ v

theorem cylinderCenteredCappedTerminalPacket_summable {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0))) (Y : ℝ) (hY : 0<Y) :
    Summable (fun i =>
      ‖cylinderCenteredCappedTerminalPacket f hc he hr R hR hs ε t Y hY (basis i)‖^2) :=
  finiteEnergyColumnOperator_summable _ _ _ basis

theorem cylinderCenteredCappedTerminalPacket_energy {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0))) (Y : ℝ) (hY : 0<Y) :
    (∑' i, ENNReal.ofReal
      (‖cylinderCenteredCappedTerminalPacket f hc he hr R hR hs ε t Y hY (basis i)‖^2)) =
      ∫⁻ z, ENNReal.ofReal (‖cylinderCenteredCappedColumn f hc he R hR hs ε t z‖^2)
        ∂volume.restrict (AsymptoticCertificateOperators.highStrip Y) :=
  finiteEnergyColumnOperator_energy _ _ _ basis

#print axioms cylinderCenteredCappedColumn_eq
#print axioms cylinderCenteredCappedColumn_memLp
#print axioms cylinderCenteredCappedTerminalPacket_coeFn
#print axioms cylinderCenteredCappedTerminalPacket_summable
#print axioms cylinderCenteredCappedTerminalPacket_energy

end QuantitativeMaass
