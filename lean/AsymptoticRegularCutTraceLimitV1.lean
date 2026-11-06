module

public import AsymptoticRegularCutTerminalTraceV1
public import AsymptoticRegularCutLimitV1
public import AsymptoticSignedCornerContinuityV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace Filter
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open scoped ENNReal Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem cutTraceErrorBound_tendsto_zero (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℕ → ℝ) (hY : Tendsto Y atTop (𝓝 0)) :
    Tendsto (fun n => cutTraceErrorBound A hN P r s hs (Y n)) atTop (𝓝 0) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A P'
  change Tendsto (fun n => cutErrorBound A hN P r s hs (Y n)*BR^2+2*BR*(Y n/P'.ε*BR)) atTop (𝓝 0)
  simpa only [zero_mul,zero_div,mul_zero,zero_add] using
    ((cutErrorBound_tendsto_zero A hN P r s hs Y hY).mul_const (BR^2)).add
      (((hY.div_const P'.ε).mul_const BR).const_mul (2*BR))

/-- Quantitative trace error for the actual positive observation
operators. The estimate is taken in the finite terminal corner. -/
theorem cutPositive_trace_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY0 : 0≤Y) (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) :
    ‖(trace volume (cutPositive A hN P r s hs e Y)).toReal-(trace volume (positive A hN P r s hs e)).toReal‖≤
      cutTraceErrorBound A hN P r s hs Y/(AsymptoticReconstructedCount.parameters A P).ε := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have harea : (volume : Measure ℍ) (AsymptoticCertificateOperators.highStrip P'.ε)=ENNReal.ofReal P'.ε⁻¹ :=
    AsymptoticHyperbolicArea.closed_terminal_area P'.epsilon_pos
  have hf : (volume : Measure ℍ) (AsymptoticCertificateOperators.highStrip P'.ε)<∞ :=
    harea.trans_lt ENNReal.ofReal_lt_top
  have hb := norm_signedTrace_sub_le_corner volume
    (AsymptoticCertificateOperators.highStrip_measurable P'.ε) hf
    (cutTerminalTraceOperator A hN P r s hs e Y) (terminalTraceOperator A hN P r s hs e)
    (cutTerminalTraceOperator_matrix_measurable A hN P r s hs e Y hY 1 1)
    (terminalTraceOperator_matrix_measurable A hN P r s hs e 1 1)
    (cutTerminalTraceOperator_norm_le A hN P r s hs e Y hY) (terminalTraceOperator_norm_le A hN P r s hs e)
    (cutTerminalTraceOperator_right_terminal A hN P r s hs e Y) (terminalTraceOperator_right_terminal A hN P r s hs e)
    (fun z => (norm_sub_rev _ _).le.trans (cutTerminalTraceOperator_error A hN P r s hs e Y hY0 hY z))
  rw [harea,ENNReal.toReal_ofReal (inv_nonneg.mpr P'.epsilon_pos.le)] at hb
  rw [cutPositive_trace_toReal_eq_terminal A hN P r s hs e Y hY,positive_trace_toReal_eq_terminal]
  simpa only [div_eq_mul_inv] using hb

/-- Removal of the low-height cutoff is valid at the level of actual
positive traces, uniformly across all sectors. -/
theorem cutPositive_trace_tendstoUniformly (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℕ → ℝ)
    (hY0 : ∀ n,0≤Y n) (hYε : ∀ n,Y n≤(AsymptoticReconstructedCount.parameters A P).ε)
    (hY : Tendsto Y atTop (𝓝 0)) :
    TendstoUniformly (fun n (e : Sector N) => (trace volume (cutPositive A hN P r s hs e (Y n))).toReal)
      (fun e : Sector N => (trace volume (positive A hN P r s hs e)).toReal) atTop := by
  have hd : Tendsto (fun n => cutTraceErrorBound A hN P r s hs (Y n)/
      (AsymptoticReconstructedCount.parameters A P).ε) atTop (𝓝 0) := by
    simpa only [zero_div] using (cutTraceErrorBound_tendsto_zero A hN P r s hs Y hY).div_const
      (AsymptoticReconstructedCount.parameters A P).ε
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  apply ((tendsto_order.mp hd).2 δ hδ).mono
  intro n hn e
  rw [dist_eq_norm]
  exact ((norm_sub_rev _ _).le.trans (cutPositive_trace_error A hN P r s hs e (Y n) (hY0 n) (hYε n))).trans_lt hn

/-- The same limit for the nonnegative extended-real rooted trace; both
the cutoff and uncut traces have independently proved finiteness. -/
theorem cutPositive_trace_tendsto (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℕ → ℝ)
    (hY0 : ∀ n,0≤Y n) (hYε : ∀ n,Y n≤(AsymptoticReconstructedCount.parameters A P).ε)
    (hY : Tendsto Y atTop (𝓝 0)) :
    Tendsto (fun n => trace volume (cutPositive A hN P r s hs e (Y n))) atTop
      (𝓝 (trace volume (positive A hN P r s hs e))) := by
  have ht := (cutPositive_trace_tendstoUniformly A hN P r s hs Y hY0 hYε hY).tendsto_at e
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  have hcut (n : ℕ) : ENNReal.ofReal (trace volume (cutPositive A hN P r s hs e (Y n))).toReal=
      trace volume (cutPositive A hN P r s hs e (Y n)) :=
    ENNReal.ofReal_toReal (cutPositive_trace_finite A hN P r s hs e (Y n) (hYε n)).ne
  simpa only [Function.comp_def,hcut,
    ENNReal.ofReal_toReal (positive_trace_finite A hN P r s hs e).ne] using he

#print axioms cutTraceErrorBound_tendsto_zero
#print axioms cutPositive_trace_error
#print axioms cutPositive_trace_tendstoUniformly
#print axioms cutPositive_trace_tendsto

end AsymptoticRegularObservation
