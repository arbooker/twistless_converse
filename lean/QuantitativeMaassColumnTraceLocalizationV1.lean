module

public import QuantitativeMaassApproximateProjectionTraceV1
public import QuantitativeMaassCylinderSharpTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped SchwartzMap ENNReal
namespace QuantitativeMaass

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem columnLinearTrace_nonneg (μ : Measure α) (c : α→H)
    (T : H→L[ℂ]H) (hT : T.IsPositive) : 0≤columnLinearTrace μ c T :=
  integral_nonneg (fun x => hT.re_inner_nonneg_left (c x))

/-- Exact localization in the output variable, with integrability proved
from the actual column data. -/
theorem columnLinearTrace_split (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (T : H→L[ℂ]H) (s : Set α) (hs : MeasurableSet s) :
    columnLinearTrace μ c T=columnLinearTrace (μ.restrict s) c T+
      columnLinearTrace (μ.restrict sᶜ) c T :=
  (integral_add_compl hs (columnLinearTrace_integrable μ c hc T)).symm

/-- Nested cutoffs split into the retained cell and the upper tail. -/
theorem columnLinearTrace_nested_split (μ : Measure α) (c : α→H)
    (a b : Set α) (hb : MeasurableSet b) (hba : b⊆a)
    (hc : MemLp c 2 (μ.restrict a)) (T : H→L[ℂ]H) :
    columnLinearTrace (μ.restrict a) c T=
      columnLinearTrace (μ.restrict (a\b)) c T+columnLinearTrace (μ.restrict b) c T := by
  have hh := columnLinearTrace_split (μ.restrict a) c hc T b hb
  rw [Measure.restrict_restrict hb,Measure.restrict_restrict hb.compl,
    inter_eq_left.mpr hba] at hh
  simpa only [sdiff_eq,inter_comm,add_comm] using hh

/-- A real bound follows from the sharp nonzero-channel energy estimate;
no sign assumption on the written diagonal value is needed. -/
theorem cylinderCenteredCappedColumn_real_tail {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (ε : ℝ) (m : ℕ) (Y : ℝ) (hY : 0<Y) :
    let J := ⌈(m:ℝ)*R+1⌉₊
    (∫ z in AsymptoticCertificateOperators.highStrip Y,
      ‖cylinderCenteredCappedColumn f hc he R hR hs ε m z‖^2)≤
      ((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2)*
        (Y⁻¹*|(abelProfile (evenCoshLift (timeConvolution f f)) 1).re|) := by
  intro J
  have hi := (memLp_two_iff_integrable_sq_norm
    (cylinderCenteredCappedColumn_memLp f hc he hr R hR hs ε m Y hY).aestronglyMeasurable).mp
    (cylinderCenteredCappedColumn_memLp f hc he hr R hR hs ε m Y hY)
  have hh := cylinderCenteredCappedTerminalPacket_sharp_energy f hc he hr R hR hs basis ε m Y hY
  rw [cylinderCenteredCappedTerminalPacket_energy] at hh
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun z => sq_nonneg _))] at hh
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  apply hh.trans
  rw [ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_mul (inv_nonneg.mpr hY.le)]
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (le_abs_self _)))

/-- Upper-tail trace bound for the actual centered, capped columns used in
the original count. The only operator cost is its actual norm. -/
theorem cylinderCenteredCappedColumn_trace_tail {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (ε : ℝ) (m : ℕ) (Y : ℝ) (hY : 0<Y)
    (T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0)) :
    let J := ⌈(m:ℝ)*R+1⌉₊
    columnLinearTrace (volume.restrict (AsymptoticCertificateOperators.highStrip Y))
      (cylinderCenteredCappedColumn f hc he R hR hs ε m) T≤
      ‖T‖*(((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2)*
        (Y⁻¹*|(abelProfile (evenCoshLift (timeConvolution f f)) 1).re|)) := by
  intro J
  exact (le_abs_self _).trans ((columnLinearTrace_bound _ _
    (cylinderCenteredCappedColumn_memLp f hc he hr R hR hs ε m Y hY) T).trans
    (mul_le_mul_of_nonneg_left
      (cylinderCenteredCappedColumn_real_tail basis f hc he hr R hR hs ε m Y hY) (norm_nonneg T)))

#print axioms columnLinearTrace_nonneg
#print axioms columnLinearTrace_mono
#print axioms columnLinearTrace_split
#print axioms columnLinearTrace_nested_split
#print axioms cylinderCenteredCappedColumn_real_tail
#print axioms cylinderCenteredCappedColumn_trace_tail
end QuantitativeMaass
