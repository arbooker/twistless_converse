module

public import QuantitativeSpectralDistributionV1
public import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
@[expose] public section

namespace QuantitativeSpectralFilter

open MeasureTheory Set

/-- Scalar exponential decay of the positive polynomial filter. -/
theorem filter_le_exp {x K : ℝ} (hK : 0 < K) (hx : x ≤ K) (n : ℕ) :
    (1-x/K)^n ≤ Real.exp (-(n : ℝ)*x/K) := by
  have hnonneg : 0 ≤ 1-x/K := sub_nonneg.mpr ((div_le_one hK).mpr hx)
  have hbase : 1-x/K ≤ Real.exp (-x/K) := by
    simpa only [neg_div, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(x/K))
  have h := pow_le_pow_left₀ hnonneg hbase n
  rw [← Real.exp_nat_mul] at h
  have he : (n : ℝ) * (-x/K) = -(n : ℝ)*x/K := by ring
  rwa [he] at h

/-- A single polynomial filter has trace at most the low spectral mass
plus its exponentially damped high-spectrum tail. This is proved for any
finite measure and requires no discrete eigenvalue enumeration. -/
theorem filter_integral_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {K lam : ℝ} (hK : 0 < K) (n : ℕ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ f x) (hupper : ∀ᵐ x ∂μ, f x ≤ K) :
    (∫ x, (1-f x/K)^n ∂μ) ≤ μ.real {x | f x ≤ lam} +
      μ.real univ * Real.exp (-(n : ℝ)*lam/K) := by
  have hmeas : Measurable (fun x => (1-f x/K)^n) :=
    (measurable_const.sub (hf.div_const K)).pow_const n
  have hbounded : ∀ᵐ x ∂μ, ‖(1-f x/K)^n‖ ≤ 1 := by
    filter_upwards [hpos, hupper] with x hx hxK
    have h0 : 0 ≤ 1-f x/K := sub_nonneg.mpr ((div_le_one hK).mpr hxK)
    have h1 : 1-f x/K ≤ 1 := by linarith [div_nonneg hx hK.le]
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 n)]
    simpa only [one_pow] using pow_le_pow_left₀ h0 h1 n
  have hfi : Integrable (fun x => (1-f x/K)^n) μ :=
    (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable hbounded
  have hs : MeasurableSet {x | f x ≤ lam} := measurableSet_le hf measurable_const
  have hI := (integrable_const (1 : ℝ) : Integrable (fun _ : α => (1 : ℝ)) μ).indicator hs
  let tail := Real.exp (-(n : ℝ)*lam/K)
  have hb := integral_mono_ae hfi (hI.add (integrable_const tail)) ?_
  · simp only [Pi.add_apply] at hb
    simpa only [integral_add hI (integrable_const tail), integral_indicator_const (1 : ℝ) hs,
      integral_const, smul_eq_mul, mul_one, tail] using hb
  · filter_upwards [hupper, hbounded] with x hxK hxb
    change (1-f x/K)^n ≤ {x | f x ≤ lam}.indicator (fun _ => 1) x + tail
    by_cases h : f x ≤ lam
    · rw [Set.indicator_of_mem (show x ∈ {x | f x ≤ lam} from h)]
      have hb' : (1-f x/K)^n ≤ 1 := (le_abs_self _).trans (by simpa using hxb)
      have ht : 0 ≤ tail := Real.exp_nonneg _
      linarith
    · rw [Set.indicator_of_notMem (show x ∉ {x | f x ≤ lam} from h), zero_add]
      apply (filter_le_exp hK hxK n).trans
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff_of_pos_right hK).mpr
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [lt_of_not_ge h]

/-- An explicit degree criterion suffices to suppress the entire tail.
It avoids any appeal to an unspecified rate of strong convergence. -/
theorem tail_le_error {T K lam eta : ℝ} {n : ℕ}
    (hT : 0 < T) (hK : 0 < K) (hlam : 0 < lam) (heta : 0 < eta)
    (hdegree : K/lam * Real.log (T/eta) ≤ (n : ℝ)) :
    T * Real.exp (-(n : ℝ)*lam/K) ≤ eta := by
  have hscale : 0 < lam/K := div_pos hlam hK
  have hd := mul_le_mul_of_nonneg_right hdegree hscale.le
  have he : K/lam * Real.log (T/eta) * (lam/K) = Real.log (T/eta) := by
    field_simp
  rw [he] at hd
  have hx : -(n : ℝ)*lam/K ≤ -Real.log (T/eta) := by
    calc
      -(n : ℝ)*lam/K = -((n : ℝ)*(lam/K)) := by ring
      _ ≤ -Real.log (T/eta) := neg_le_neg hd
  have heq : Real.exp (-Real.log (T/eta)) = eta/T := by
    rw [Real.exp_neg, Real.exp_log (div_pos hT heta)]
    field_simp
  have hb := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) hT.le
  rw [heq] at hb
  have hcancel : T * (eta/T) = eta := by field_simp
  rwa [hcancel] at hb

#print axioms filter_le_exp
#print axioms filter_integral_bound
#print axioms tail_le_error

end QuantitativeSpectralFilter
