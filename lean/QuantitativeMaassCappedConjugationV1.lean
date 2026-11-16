module

public import QuantitativeMaassMetricConjugationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane

namespace QuantitativeMaass

theorem cappedHeightWeight_log_measurable (ε : ℝ) (t : ℕ) :
    Measurable (fun z : ℍ => Real.log (cappedHeightWeight ε t z)) := by
  unfold cappedHeightWeight
  fun_prop

/-- Bounded conjugation by the literal capped reconstruction weight,
for an actual finite-propagation L2 operator on the hyperbolic plane. -/
def cappedWeightConjugation (μ : Measure ℍ) (ε : ℝ) (hε : 0<ε) (t : ℕ)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (R : ℝ) (hT : LogBands.HasMetricPropagation μ T R) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LogBands.metricConjugation μ (fun z => Real.log (cappedHeightWeight ε t z))
    (cappedHeightWeight_log_measurable ε t) T t R (Nat.cast_nonneg t)
    (cappedHeightWeight_log_dist hε t) hT

theorem cappedWeightConjugation_norm_bound (μ : Measure ℍ) (ε : ℝ) (hε : 0<ε) (t : ℕ)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (R : ℝ) (hR : 0≤R)
    (hT : LogBands.HasMetricPropagation μ T R) :
    ‖cappedWeightConjugation μ ε hε t T R hT‖≤
      5*(1+(t:ℝ)*R)*Real.exp ((t:ℝ)*R+3)*‖T‖ :=
  LogBands.metricConjugation_norm_bound μ (fun z => Real.log (cappedHeightWeight ε t z))
    (cappedHeightWeight_log_measurable ε t) T t R (Nat.cast_nonneg t) hR
    (cappedHeightWeight_log_dist hε t) hT

/-- The construction acts by the original capped weight, rather than an
unrelated equivalent weight, on its dense finite-band domain. -/
theorem cappedWeightConjugation_coeFn (μ : Measure ℍ) (ε : ℝ) (hε : 0<ε) (t : ℕ)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (R : ℝ)
    (hT : LogBands.HasMetricPropagation μ T R)
    (f : LogBands.finiteBandSpace μ (fun z => Real.log (cappedHeightWeight ε t z))
      (cappedHeightWeight_log_measurable ε t)) :
    cappedWeightConjugation μ ε hε t T R hT f.val=ᵐ[μ]
      (fun z => (cappedHeightWeight ε t z:ℂ)*
        (T (LogBands.exponentialEnd μ (fun z => Real.log (cappedHeightWeight ε t z))
          (cappedHeightWeight_log_measurable ε t) (-1) f).val) z) := by
  have hh := LogBands.boundedConjugation_coeFn μ (fun z => Real.log (cappedHeightWeight ε t z))
    (cappedHeightWeight_log_measurable ε t) T ⌈(t:ℝ)*R+1⌉₊
    (LogBands.band_propagation_of_metric μ (fun z => Real.log (cappedHeightWeight ε t z))
      (cappedHeightWeight_log_measurable ε t) T t R (Nat.cast_nonneg t)
      (cappedHeightWeight_log_dist hε t) hT) f
  simpa only [Real.exp_log (cappedHeightWeight_pos hε t _)] using! hh

#print axioms cappedHeightWeight_log_measurable
#print axioms cappedWeightConjugation_norm_bound
#print axioms cappedWeightConjugation_coeFn

end QuantitativeMaass
