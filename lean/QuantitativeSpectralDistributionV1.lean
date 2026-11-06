module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

/-!
Scalar spectral-distribution estimates for arbitrary finite measures, not only
finite lists of eigenvalues. These are the measure-theoretic parts of the
fresh-prime and collective-logarithm arguments. Constructing the tracial
spectral distribution of the regular orbit operators is a separate obligation;
this file does not identify its measures with those operators.
-/

namespace QuantitativeSpectralDistribution

open MeasureTheory Set

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

/-- An upper bound on a bounded observable gives a lower bound for its
high-value mass. No positivity of the observable is needed. -/
theorem high_mass_bound (f : α → ℝ) (hf : Measurable f)
    (hfi : Integrable f μ) {a M : ℝ} (ha : 0 ≤ a)
    (hM : ∀ᵐ x ∂μ, f x ≤ M) :
    (∫ x, f x ∂μ) ≤ a * μ.real univ + M * μ.real {x | a ≤ f x} := by
  have hs : MeasurableSet {x | a ≤ f x} := measurableSet_le measurable_const hf
  have hI := (integrable_const M : Integrable (fun _ : α => M) μ).indicator hs
  have hi := integral_mono_ae hfi ((integrable_const a).add hI) ?_
  · simp only [Pi.add_apply] at hi
    simpa only [integral_add (integrable_const a) hI, integral_const,
      integral_indicator_const M hs, smul_eq_mul, mul_comm] using hi
  · filter_upwards [hM] with x hx
    change f x ≤ a + _
    by_cases h : a ≤ f x
    · simp only [Set.indicator_of_mem (show x ∈ {x | a ≤ f x} from h)]
      linarith
    · simp only [Set.indicator_of_notMem (show x ∉ {x | a ≤ f x} from h), add_zero]
      exact (lt_of_not_ge h).le

/-- The fresh-prime trace identity gives genuine high spectral mass:
a positive contraction of mean `1/n` has at least `T/(2*n)` mass above
`1/(2*n)`. The finite measure can have continuous spectrum. -/
theorem fresh_high_mass (f : α → ℝ) (hf : Measurable f)
    (hfi : Integrable f μ) {n : ℝ} (hn : 0 < n)
    (hupper : ∀ᵐ x ∂μ, f x ≤ 1)
    (htrace : (∫ x, f x ∂μ) = μ.real univ / n) :
    μ.real univ / (2*n) ≤ μ.real {x | 1/(2*n) ≤ f x} := by
  have h := high_mass_bound μ f hf hfi (a := 1/(2*n)) (by positivity) hupper
  rw [htrace, one_mul] at h
  have he : μ.real univ / n = 2 * (μ.real univ / (2*n)) := by field_simp
  have he' : 1/(2*n) * μ.real univ = μ.real univ / (2*n) := by ring
  rw [he, he'] at h
  linarith

/-- Adjustable fresh-prime extraction. Letting `theta` be small retains
an arbitrarily large fixed fraction of the original trace coefficient. -/
theorem fresh_high_mass_theta (f : α → ℝ) (hf : Measurable f)
    (hfi : Integrable f μ) {n theta : ℝ} (hn : 0 < n) (htheta : 0 ≤ theta)
    (hupper : ∀ᵐ x ∂μ, f x ≤ 1)
    (htrace : (∫ x, f x ∂μ) = μ.real univ / n) :
    (1-theta) * μ.real univ / n ≤ μ.real {x | theta/n ≤ f x} := by
  have h := high_mass_bound μ f hf hfi (a := theta/n) (div_nonneg htheta hn.le) hupper
  rw [htrace, one_mul] at h
  have he : (1-theta) * μ.real univ / n =
      μ.real univ / n - theta/n * μ.real univ := by ring
  rw [he]
  linarith

/-- The logarithmic determinant deficit controls the small spectrum.
The input is a log integral, rather than the desired spectral-mass bound.
It applies to arbitrary finite spectral distributions, including diffuse ones. -/
theorem small_mass_of_log_integral (f : α → ℝ) (hf : Measurable f)
    (hlog : Integrable (fun x => Real.log (f x)) μ)
    {s K lam : ℝ} (hs : 0 < s) (hK : 0 < K) (hlam : 0 < lam)
    (hlamK : lam < K) (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hupper : ∀ᵐ x ∂μ, f x ≤ K)
    (hlower : μ.real univ * Real.log s ≤ ∫ x, Real.log (f x) ∂μ) :
    μ.real {x | f x ≤ lam} ≤
      μ.real univ * Real.log (K/s) / Real.log (K/lam) := by
  have hset : MeasurableSet {x | f x ≤ lam} := measurableSet_le hf measurable_const
  let c := Real.log lam - Real.log K
  have hI := (integrable_const c : Integrable (fun _ : α => c) μ).indicator hset
  have hb := integral_mono_ae hlog ((integrable_const (Real.log K)).add hI) ?_
  · simp only [Pi.add_apply] at hb
    simp only [integral_add (integrable_const (Real.log K)) hI, integral_const,
      integral_indicator_const c hset, smul_eq_mul] at hb
    have hd : 0 < Real.log K - Real.log lam :=
      sub_pos.mpr (Real.log_lt_log hlam hlamK)
    rw [Real.log_div hK.ne' hs.ne', Real.log_div hK.ne' hlam.ne']
    apply (le_div_iff₀ hd).mpr
    dsimp [c] at hb
    nlinarith
  · filter_upwards [hpos, hupper] with x hx hxK
    change Real.log (f x) ≤ Real.log K + _
    by_cases h : f x ≤ lam
    · simp only [Set.indicator_of_mem (show x ∈ {x | f x ≤ lam} from h)]
      dsimp [c]
      have := Real.log_le_log hx h
      linarith
    · simp only [Set.indicator_of_notMem (show x ∉ {x | f x ≤ lam} from h), add_zero]
      exact Real.log_le_log hx hxK

/-- A numeric trace-log lower bound retains the separate contribution of
a small diagonal block. -/
theorem small_mass_of_log_integral_lower (f : α → ℝ) (hf : Measurable f)
    (hlog : Integrable (fun x => Real.log (f x)) μ)
    {L K lam : ℝ} (hK : 0 < K) (hlam : 0 < lam)
    (hlamK : lam < K) (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hupper : ∀ᵐ x ∂μ, f x ≤ K)
    (hlower : L ≤ ∫ x, Real.log (f x) ∂μ) :
    μ.real {x | f x ≤ lam} ≤
      (μ.real univ * Real.log K - L) / Real.log (K/lam) := by
  have hset : MeasurableSet {x | f x ≤ lam} := measurableSet_le hf measurable_const
  let c := Real.log lam - Real.log K
  have hI := (integrable_const c : Integrable (fun _ : α => c) μ).indicator hset
  have hb := integral_mono_ae hlog ((integrable_const (Real.log K)).add hI) ?_
  · simp only [Pi.add_apply] at hb
    simp only [integral_add (integrable_const (Real.log K)) hI, integral_const,
      integral_indicator_const c hset, smul_eq_mul] at hb
    have hd : 0 < Real.log K - Real.log lam :=
      sub_pos.mpr (Real.log_lt_log hlam hlamK)
    rw [Real.log_div hK.ne' hlam.ne']
    apply (le_div_iff₀ hd).mpr
    dsimp [c] at hb
    nlinarith
  · filter_upwards [hpos, hupper] with x hx hxK
    change Real.log (f x) ≤ Real.log K + _
    by_cases h : f x ≤ lam
    · simp only [Set.indicator_of_mem (show x ∈ {x | f x ≤ lam} from h)]
      dsimp [c]
      have := Real.log_le_log hx h
      linarith
    · simp only [Set.indicator_of_notMem (show x ∉ {x | f x ≤ lam} from h), add_zero]
      exact Real.log_le_log hx hxK

#print axioms small_mass_of_log_integral_lower

#print axioms high_mass_bound
#print axioms fresh_high_mass
#print axioms fresh_high_mass_theta
#print axioms small_mass_of_log_integral

end QuantitativeSpectralDistribution
