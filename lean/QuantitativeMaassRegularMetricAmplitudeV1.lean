module

public import QuantitativeMaassRegularMetricCoefficientV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticMassTransport AsymptoticClassicalPetersson AsymptoticCompactBranch
open scoped ENNReal
namespace QuantitativeMaass.CountingMetric

/-- The normalized counting amplitude and metric diagonal combine to
exactly the scalar-corrected original cap. -/
theorem metric_amplitude {ι : Type*} [Fintype ι]
    (N : ℕ) (g : ι→quotientNormalizerGroup N) {δ : ℝ} (hδ : 0<δ)
    {ν : ℕ} (hν : 1≤ν) (z : ℍ) :
    amplitude N δ ν z*((Real.sqrt (weight N δ ν z)*normalizerCoverMetric N g δ ν z:ℝ):ℂ)=
      strip.indicator (fun w => ((normalizerCoverMetric N g δ ν w*cap δ ν w:ℝ):ℂ)) z := by
  classical
  by_cases hz : z∈strip
  · rw [amplitude,Set.indicator_of_mem hz,Set.indicator_of_mem hz,←Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    have hs : Real.sqrt (weight N δ ν z)≠0 := (Real.sqrt_pos.mpr (weight_pos N hδ hν z)).ne'
    field_simp [hs]
  · simp only [amplitude,Set.indicator_of_notMem hz,zero_mul]

/-- The regular metric cap has precisely the quotient covolume as mass. -/
theorem metric_amplitude_mass {ι : Type*} [Fintype ι]
    (N : ℕ) (g : ι→quotientNormalizerGroup N) {δ : ℝ} (hδ : 0<δ)
    {ν : ℕ} (hν : 1≤ν) (hpos : ∀ z,0<normalizerCoverWeight N g δ ν z) :
    (∫⁻ z,ENNReal.ofReal (‖amplitude N δ ν z*
      ((Real.sqrt (weight N δ ν z)*normalizerCoverMetric N g δ ν z:ℝ):ℂ)‖^2))=
      quotientMeasure N Set.univ := by
  have hh := normalizerCoverMetric_representative_energy N g hδ hν hpos
    (fun _ => (1:ℂ)) measurable_const (fun _ _ => rfl) (fun _ _ => rfl)
  simp only [mul_one,norm_one,one_pow,ENNReal.ofReal_one,lintegral_one] at hh
  rw [translation_quotient_measure] at hh
  rw [←lintegral_indicator strip_measurable] at hh
  apply Eq.trans _ hh
  apply lintegral_congr
  intro z
  rw [metric_amplitude N g hδ hν z]
  by_cases hz : z∈strip
  · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz]
  · simp only [Set.indicator_of_notMem hz,norm_zero,zero_pow (by decide : 2≠0),ENNReal.ofReal_zero]

#print axioms metric_amplitude
#print axioms metric_amplitude_mass
end QuantitativeMaass.CountingMetric
