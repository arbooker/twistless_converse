module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace BigOperators

namespace QuantitativeArithmeticPositiveCutoff

variable {X H ι : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Localizing the output column after applying a bounded operator costs
only its operator norm on the complementary region. No commutation with
the spatial cutoff or global trace-class assumption is needed. -/
theorem column_energy_cutoff (μ : Measure X) (c : X → H)
    (A : H →L[ℂ] H) (K : Set X) (hK : MeasurableSet K) :
    (∫⁻ x, ENNReal.ofReal (‖A (c x)‖^2) ∂μ) ≤
      (∫⁻ x in K, ENNReal.ofReal (‖A (c x)‖^2) ∂μ) +
        ENNReal.ofReal (‖A‖^2) *
          ∫⁻ x in Kᶜ, ENNReal.ofReal (‖c x‖^2) ∂μ := by
  rw [← lintegral_add_compl (fun x => ENNReal.ofReal (‖A (c x)‖^2)) hK]
  refine add_le_add le_rfl ?_
  calc
    _ ≤ ∫⁻ x in Kᶜ, ENNReal.ofReal (‖A‖^2) * ENNReal.ofReal (‖c x‖^2) ∂μ := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (‖A (c x)‖^2) ≤ ENNReal.ofReal (‖A‖^2) * ENNReal.ofReal (‖c x‖^2)
      rw [← ENNReal.ofReal_mul (sq_nonneg ‖A‖)]
      apply ENNReal.ofReal_le_ofReal
      have h := A.le_opNorm (c x)
      nlinarith [norm_nonneg (A (c x)), norm_nonneg (c x), norm_nonneg A]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- A finite orthonormal family sees at most the actual column energy.
Nonnegative integrals allow the assertion before integrability is proved. -/
theorem finite_column_bessel [Fintype ι] (μ : Measure X) (c : X → H)
    (hc : StronglyMeasurable c) (v : ι → H) (hv : Orthonormal ℂ v) :
    (∑ i, ∫⁻ x, ENNReal.ofReal (‖inner ℂ (v i) (c x)‖^2) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (‖c x‖^2) ∂μ := by
  classical
  have hmeas (i : ι) : Measurable (fun x => ENNReal.ofReal (‖inner ℂ (v i) (c x)‖^2)) :=
    ((stronglyMeasurable_const.inner hc).norm.pow 2).measurable.ennreal_ofReal
  rw [← lintegral_finsetSum Finset.univ (fun i _ => hmeas i)]
  apply lintegral_mono
  intro x
  change (∑ i, ENNReal.ofReal (‖inner ℂ (v i) (c x)‖^2)) ≤ ENNReal.ofReal (‖c x‖^2)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hv.sum_inner_products_le (c x))

/-- The genuine even moment splits into a compact column integral and a
tail with an explicit operator-norm cost, uniformly in the power. -/
theorem finite_column_power_cutoff [Fintype ι] (μ : Measure X) (c : X → H)
    (hc : StronglyMeasurable c) (T : H →L[ℂ] H) (d : ℕ)
    (v : ι → H) (hv : Orthonormal ℂ v) (K : Set X) (hK : MeasurableSet K) :
    (∑ i, ∫⁻ x, ENNReal.ofReal (‖inner ℂ (v i) ((T^d) (c x))‖^2) ∂μ) ≤
      (∫⁻ x in K, ENNReal.ofReal (‖(T^d) (c x)‖^2) ∂μ) +
        ENNReal.ofReal (‖T‖^(2*d)) *
          ∫⁻ x in Kᶜ, ENNReal.ofReal (‖c x‖^2) ∂μ := by
  refine (finite_column_bessel μ _ ((T^d).continuous.comp_stronglyMeasurable hc) v hv).trans ?_
  refine (column_energy_cutoff μ c (T^d) K hK).trans ?_
  refine add_le_add le_rfl ?_
  refine mul_le_mul' ?_ le_rfl
  apply ENNReal.ofReal_le_ofReal
  have hpow : ‖T^d‖ ≤ ‖T‖^d := by
    cases d with
    | zero =>
      simp only [pow_zero]
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simp
    | succ n => exact norm_pow_le' T (Nat.succ_pos n)
  calc
    ‖T^d‖^2 ≤ (‖T‖^d)^2 := pow_le_pow_left₀ (norm_nonneg _) hpow 2
    _ = ‖T‖^(2*d) := by rw [← pow_mul, Nat.mul_comm]

theorem real_eigen_inner_power (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (v x : H) (r : ℝ) (he : T v = (r : ℂ) • v) (d : ℕ) :
    inner ℂ v ((T^d) x) = (r : ℂ)^d * inner ℂ v x := by
  induction d with
  | zero => simp
  | succ d ih =>
    have ht : inner ℂ (T v) ((T^d) x) = inner ℂ v (T ((T^d) x)) := hT _ _
    rw [pow_succ', mul_apply_eq_comp, ← ht, he, inner_smul_left,
      Complex.conj_ofReal, ih, pow_succ']
    ring

/-- Packet coefficient energy gives a quantitative spectral moment bound.
The normalization `m` is supplied by the positive window majorant; the
remaining integrals are literal compact/tail column energies. -/
theorem finite_eigenmoment_cutoff [Fintype ι] (μ : Measure X) (c : X → H)
    (hc : StronglyMeasurable c) (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (v : ι → H) (hv : Orthonormal ℂ v) (r : ι → ℝ)
    (he : ∀ i, T (v i) = (r i : ℂ) • v i) (d : ℕ) (m : ℝ≥0∞)
    (hm : ∀ i, m ≤ ∫⁻ x, ENNReal.ofReal (‖inner ℂ (v i) (c x)‖^2) ∂μ)
    (K : Set X) (hK : MeasurableSet K) :
    m * ∑ i, ENNReal.ofReal ((r i)^(2*d)) ≤
      (∫⁻ x in K, ENNReal.ofReal (‖(T^d) (c x)‖^2) ∂μ) +
        ENNReal.ofReal (‖T‖^(2*d)) *
          ∫⁻ x in Kᶜ, ENNReal.ofReal (‖c x‖^2) ∂μ := by
  classical
  have heq (i : ι) (x : X) :
      ‖inner ℂ (v i) ((T^d) (c x))‖^2 =
        (r i)^(2*d) * ‖inner ℂ (v i) (c x)‖^2 := by
    rw [real_eigen_inner_power T hT (v i) (c x) (r i) (he i) d,
      norm_mul, mul_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [← pow_mul, Nat.mul_comm d 2, pow_mul, sq_abs, ← pow_mul]
  refine le_trans ?_ (finite_column_power_cutoff μ c hc T d v hv K hK)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hn : 0 ≤ (r i)^(2*d) := by rw [pow_mul]; positivity
  simp_rw [heq, ENNReal.ofReal_mul hn]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simpa only [mul_comm] using mul_le_mul' (le_rfl : ENNReal.ofReal ((r i)^(2*d)) ≤ _) (hm i)

#print axioms column_energy_cutoff
#print axioms finite_column_bessel
#print axioms finite_column_power_cutoff
#print axioms real_eigen_inner_power
#print axioms finite_eigenmoment_cutoff

end QuantitativeArithmeticPositiveCutoff
