module

public import QuantitativeMaassColumnTraceLocalizationV1
public import QuantitativeMaassConjugatedColumnBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped SchwartzMap
namespace QuantitativeMaass

theorem cappedHeightWeight_eq_one_above {ε : ℝ} (hε : 0<ε) (m : ℕ)
    (z : ℍ) (hz : ε≤z.im) : cappedHeightWeight ε m z=1 := by
  rw [cappedHeightWeight,min_eq_right ((one_le_div hε).mpr hz),one_pow]

/-- A bounded inverse weight on exactly the finite bands reaching the
terminal region. This is not the unbounded global inverse cap. -/
def terminalInverseWeightBand (ε : ℝ) (m J : ℕ) :=
  LogBands.rowInverseSum (quotientMeasure 0)
    (fun z => Real.log (cappedHeightWeight ε m z)) (cappedHeightWeight_log_measurable ε m) J 0

theorem terminalInverseWeightBand_norm {ε : ℝ} (hε : 0<ε) (m J : ℕ) :
    ‖terminalInverseWeightBand ε m J‖≤((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1) := by
  let z : ℍ := ⟨⟨0,ε⟩,hε⟩
  have hz : cappedHeightWeight ε m z=1 := cappedHeightWeight_eq_one_above hε m z le_rfl
  have hh := LogBands.rowInverseSum_weighted_norm (quotientMeasure 0)
    (fun z => Real.log (cappedHeightWeight ε m z)) (cappedHeightWeight_log_measurable ε m) J z
  simpa only [terminalInverseWeightBand,hz,Real.log_one,Real.exp_zero,Int.floor_zero,one_mul] using hh

/-- On the terminal output region the capped column is the adjoint of one
fixed bounded inverse-band operator applied to the centered unweighted column. -/
theorem cylinderCenteredCappedColumn_terminal
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    {ε : ℝ} (hε : 0<ε) (m : ℕ) (z : ℍ) (hz : ε≤z.im) :
    cylinderCenteredCappedColumn f hc he R hR hs ε m z=
      (terminalInverseWeightBand ε m ⌈(m:ℝ)*R+1⌉₊).adjoint
        (cylinderCenteredTimeColumn f hc he R hR hs z) := by
  simp only [cylinderCenteredCappedColumn,LogBands.conjugatedColumn,
    cappedHeightWeight_eq_one_above hε m z hz,Real.log_one,Real.exp_zero,
    Int.floor_zero,Complex.ofReal_one,one_smul]
  rfl

/-- Exact movement of the bounded inverse cap onto the excess operator.
The centered columns remain the actual ones from the original count. -/
theorem centeredCapped_column_trace_unweight
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    {ε : ℝ} (hε : 0<ε) (m : ℕ)
    (T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0)) :
    let K := terminalInverseWeightBand ε m ⌈(m:ℝ)*R+1⌉₊
    columnLinearTrace (volume.restrict (AsymptoticCertificateOperators.highStrip ε))
      (cylinderCenteredCappedColumn f hc he R hR hs ε m) T=
    columnLinearTrace (volume.restrict (AsymptoticCertificateOperators.highStrip ε))
      (cylinderCenteredTimeColumn f hc he R hR hs) (K.comp (T.comp K.adjoint)) := by
  intro K
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (AsymptoticCertificateOperators.highStrip_measurable ε)] with z hz
  rw [cylinderCenteredCappedColumn_terminal f hc he R hR hs hε m z hz.2]
  exact congrArg Complex.re (K.adjoint_inner_right _ _)

#print axioms cappedHeightWeight_eq_one_above
#print axioms terminalInverseWeightBand_norm
#print axioms cylinderCenteredCappedColumn_terminal
#print axioms centeredCapped_column_trace_unweight
end QuantitativeMaass
