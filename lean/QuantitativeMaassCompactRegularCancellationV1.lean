module

public import QuantitativeMaassCanonicalRegularityV1
public import QuantitativeMaassCompactCapCancellationV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane MeasureTheory AsymptoticMassTransport
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticCompactBranch
open AsymptoticNestedQuotients AsymptoticRegularTrace
open scoped lp ComplexConjugate

namespace QuantitativeMaass.CountingMetric

/-- The finite inverse-cap coefficient and the inverse scalar metric
cancel the actual regular counting amplitude on the input strip. -/
theorem compact_inverse_metric_amplitude {ι : Type*} [Fintype ι]
    (N : ℕ) (g : ι → quotientNormalizerGroup N)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) {ν : ℕ} (hν : 1 ≤ ν)
    (z : ℍ) (hz : z ∈ strip) (hheight : δ * Real.exp (-R) ≤ z.im)
    (hm : normalizerCoverMetric N g δ ν z ≠ 0) :
    ((∑ n ∈ Finset.Icc (-(⌈(ν : ℝ) * R + 1⌉₊ : ℤ)) (⌈(ν : ℝ) * R + 1⌉₊ : ℤ),
        LogBands.inverseCoefficient (fun w => Real.log (cappedHeightWeight δ ν w)) n z) *
      ((normalizerCoverMetric N g δ ν z : ℂ)⁻¹)) *
      (amplitude N δ ν z *
        ((Real.sqrt (weight N δ ν z) * normalizerCoverMetric N g δ ν z : ℝ) : ℂ)) = 1 := by
  rw [metric_amplitude N g hδ hν z, Set.indicator_of_mem hz, Complex.ofReal_mul]
  have hm' : (normalizerCoverMetric N g δ ν z : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [mul_assoc, ← mul_assoc ((normalizerCoverMetric N g δ ν z : ℂ)⁻¹),
    inv_mul_cancel₀ hm', one_mul]
  exact compact_inverse_cap_coefficient hδ hR ν z hheight

/-- Exact cancellation of both regular matrix amplitudes on the compact
input region. The remaining coefficient is the original counting-space
matrix coefficient, with coefficient one. -/
theorem compact_metricCompression_matrix {ι : Type*} [Fintype ι] [Nonempty ι]
    (N : ℕ) (g : ι → quotientNormalizerGroup N)
    {δ Y R : ℝ} (hδ : 0 < δ) (hY : 0 < Y) (hR : 0 ≤ R)
    {ν : ℕ} (hν : 1 ≤ ν)
    (hcover : ∀ z : ℍ, ∃ i, ∃ a : gamma N, Y ≤ (a.val • ((g i).val • z)).im)
    (P : ℓ²(Classes (gamma N), ℂ) →L[ℂ] ℓ²(Classes (gamma N), ℂ))
    (z : ℍ) (a b : AsymptoticRationalGroup.Group)
    (ha : a • z ∈ strip) (hb : b • z ∈ strip)
    (hheighta : δ * Real.exp (-R) ≤ (a • z).im)
    (hheightb : δ * Real.exp (-R) ≤ (b • z).im) :
    let k := fun w : ℍ =>
      (∑ n ∈ Finset.Icc (-(⌈(ν : ℝ) * R + 1⌉₊ : ℤ)) (⌈(ν : ℝ) * R + 1⌉₊ : ℤ),
        LogBands.inverseCoefficient (fun u => Real.log (cappedHeightWeight δ ν u)) n w) *
        ((normalizerCoverMetric N g δ ν w : ℂ)⁻¹)
    k (a • z) * conj (k (b • z)) *
      matrix (metricCompression N g hδ hY hν hcover P z) a b =
      matrix P (classOf (gamma N) a) (classOf (gamma N) b) := by
  intro k
  have hm (w : ℍ) : normalizerCoverMetric N g δ ν w ≠ 0 := by
    have hlo := (normalizerCoverMetric_bounds N g hδ hY hν hcover w).1
    have hp : 0 < Real.sqrt (((Fintype.card ι : ℝ) * quotientWeightBound δ + 1)⁻¹) := by
      have hB := quotientWeightBound_nonneg δ
      have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
      positivity
    exact (hp.trans_le hlo).ne'
  have hka := compact_inverse_metric_amplitude N g hδ hR hν (a • z) ha hheighta (hm _)
  have hkb := compact_inverse_metric_amplitude N g hδ hR hν (b • z) hb hheightb (hm _)
  rw [metricCompression_matrix]
  calc
    _ = (k (a • z) * (amplitude N δ ν (a • z) *
        ((Real.sqrt (weight N δ ν (a • z)) * normalizerCoverMetric N g δ ν (a • z) : ℝ) : ℂ))) *
      conj (k (b • z) * (amplitude N δ ν (b • z) *
        ((Real.sqrt (weight N δ ν (b • z)) * normalizerCoverMetric N g δ ν (b • z) : ℝ) : ℂ))) *
      matrix P (classOf (gamma N) a) (classOf (gamma N) b) := by
        dsimp only [k]
        simp only [map_mul]
        ring
    _ = _ := by rw [hka, hkb, map_one, one_mul, one_mul]

#print axioms compact_inverse_metric_amplitude
#print axioms compact_metricCompression_matrix

end QuantitativeMaass.CountingMetric
