module

public import QuantitativeMaassLogBandMeasureV1
public import AsymptoticL2MultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- The local inclusion from the positive logarithmic density to Lebesgue L2. -/
def logBandInclusion (w A B : ℝ) (hw : 0<w) :
    Lp ℂ 2 (logBandMeasure w A B) →L[ℝ] Lp ℂ 2 (volume.restrict (Icc A B)) :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (volume_le_logBandMeasure w A B hw)

theorem logBandInclusion_ae (w A B : ℝ) (hw : 0<w)
    (f : Lp ℂ 2 (logBandMeasure w A B)) :
    (logBandInclusion w A B hw f : ℝ → ℂ)=ᵐ[volume.restrict (Icc A B)] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

/-- Exponential pullback followed by a bounded local change of measure. -/
def localLogPullback (w A B : ℝ) (hw : 0<w) :
    Lp ℂ 2 (heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B))) →L[ℝ]
      Lp ℂ 2 (volume.restrict (Icc A B)) :=
  (logBandInclusion w A B hw).comp
    (Lp.compMeasurePreservingₗᵢ ℝ Real.exp (exp_logBand_preserving w A B hw.le)).toContinuousLinearMap

theorem localLogPullback_ae (w A B : ℝ) (hw : 0<w)
    (f : Lp ℂ 2 (heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B)))) :
    (localLogPullback w A B hw f : ℝ → ℂ)=ᵐ[volume.restrict (Icc A B)]
      fun x => f (Real.exp x) := by
  have hac : volume.restrict (Icc A B) ≪ logBandMeasure w A B :=
    Measure.absolutelyContinuous_of_le_smul (volume_le_logBandMeasure w A B hw)
  exact (logBandInclusion_ae w A B hw _).trans
    (hac.ae_eq (Lp.coeFn_compMeasurePreserving f (exp_logBand_preserving w A B hw.le)))

def halfDensityWeight (x : ℝ) : ℂ := (Real.exp (-x/2) : ℂ)

theorem halfDensityWeight_continuous : Continuous halfDensityWeight := by
  unfold halfDensityWeight
  fun_prop

theorem halfDensityWeight_bound (A B : ℝ) :
    ∀ᵐ x ∂volume.restrict (Icc A B), ‖halfDensityWeight x‖≤Real.exp (-A/2) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp only [halfDensityWeight,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  linarith [hx.1]

/-- Actual local half-density map. No global L2 condition on the constant
term is imposed; the target is the specified compact logarithmic band. -/
def localHalfDensity (w A B : ℝ) (hw : 0<w) :
    Lp ℂ 2 (heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B))) →L[ℝ]
      Lp ℂ 2 (volume.restrict (Icc A B)) :=
  ((AsymptoticL2Multiplier.operator halfDensityWeight
    halfDensityWeight_continuous.aestronglyMeasurable
    (halfDensityWeight_bound A B)).restrictScalars ℝ).comp (localLogPullback w A B hw)

theorem localHalfDensity_ae (w A B : ℝ) (hw : 0<w)
    (f : Lp ℂ 2 (heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B)))) :
    (localHalfDensity w A B hw f : ℝ → ℂ)=ᵐ[volume.restrict (Icc A B)]
      fun x => (Real.exp (-x/2):ℂ)*f (Real.exp x) := by
  filter_upwards [AsymptoticL2Multiplier.operator_coeFn halfDensityWeight
    halfDensityWeight_continuous.aestronglyMeasurable (halfDensityWeight_bound A B)
    (localLogPullback w A B hw f),localLogPullback_ae w A B hw f] with x hm hp
  exact hm.trans (congrArg (halfDensityWeight x * ·) hp)

#print axioms localLogPullback_ae
#print axioms localHalfDensity_ae

end QuantitativeMaass
