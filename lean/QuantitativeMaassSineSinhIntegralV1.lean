module

public import QuantitativeMaassTanhExpansionV1
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

theorem laplace_sine_integrable (a r : ℝ) (ha : 0<a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a*t)*Real.sin (r*t)) (Ioi 0) := by
  have h := (integrableOn_exp_mul_complex_Ioi
    (a := -(a:ℂ)+(r:ℂ)*Complex.I) (by simpa using neg_neg_of_pos ha) 0).im
  simpa [Complex.exp_im, neg_div] using h

theorem laplace_sine_integral (a r : ℝ) (ha : 0<a) :
    (∫ t : ℝ in Ioi 0, Real.exp (-a*t)*Real.sin (r*t)) = r/(a^2+r^2) := by
  have hi := integrableOn_exp_mul_complex_Ioi
    (a := -(a:ℂ)+(r:ℂ)*Complex.I) (by simpa using neg_neg_of_pos ha) 0
  have h := congrArg Complex.im (integral_exp_mul_complex_Ioi
    (a := -(a:ℂ)+(r:ℂ)*Complex.I) (by simpa using neg_neg_of_pos ha) 0)
  have him := integral_im hi
  change (∫ t : ℝ in Ioi 0, (Complex.exp ((-(a:ℂ)+(r:ℂ)*Complex.I)*(t:ℂ))).im) =
    (∫ t : ℝ in Ioi 0, Complex.exp ((-(a:ℂ)+(r:ℂ)*Complex.I)*(t:ℂ))).im at him
  rw [← him] at h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div, Complex.neg_im] at h
  have hr := reciprocal_real_imaginary (-a) r
  simp only [Complex.ofReal_neg, neg_sq] at hr
  rw [hr] at h
  simpa [Complex.exp_im, neg_div] using h

theorem laplace_time_integrable (a : ℝ) (ha : 0<a) :
    IntegrableOn (fun t : ℝ => t*Real.exp (-a*t)) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => Real.exp (-t)*t) (Ioi 0) := by
    simpa only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one] using (Real.GammaIntegral_convergent (s := 2) (by norm_num))
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun t : ℝ => Real.exp (-t)*t) 0 ha).mpr (by simpa using h)
  have hm := hs.const_mul (1/a)
  apply hm.congr
  filter_upwards with t
  field_simp

theorem laplace_time_integral (a : ℝ) (ha : 0<a) :
    (∫ t : ℝ in Ioi 0, t*Real.exp (-a*t)) = 1/a^2 := by
  simpa only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two,
    Real.Gamma_ofNat_eq_factorial, Nat.factorial_one, Nat.cast_one, mul_one,
    div_pow, one_pow, neg_mul] using
    (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) ha)

/-- The geometric series for the reciprocal hyperbolic sine. -/
theorem inverse_sinh_half_hasSum (t : ℝ) (ht : 0<t) :
    HasSum (fun n : ℕ => 2*Real.exp (-((n:ℝ)+1/2)*t)) (1/Real.sinh (t/2)) := by
  have hq : ‖Real.exp (-t)‖<1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have h := (hasSum_geometric_of_norm_lt_one hq).mul_left (2*Real.exp (-t/2))
  have he (n : ℕ) : 2*Real.exp (-t/2)*Real.exp (-t)^n =
      2*Real.exp (-((n:ℝ)+1/2)*t) := by
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hs : 2*Real.exp (-t/2)*(1-Real.exp (-t))⁻¹ = 1/Real.sinh (t/2) := by
    have hne : Real.sinh (t/2)≠0 := (Real.sinh_pos_iff.mpr (by linarith)).ne'
    have hden : 1-Real.exp (-t)≠0 := by
      have hlt : Real.exp (-t)<1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have hexp : Real.exp (-t/2)*Real.exp (t/2)=1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have hsq : Real.exp (-t/2)*Real.exp (-t/2)=Real.exp (-t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    apply (eq_div_iff hne).mpr
    rw [Real.sinh_eq]
    have heq : Real.exp (-(t/2))=Real.exp (-t/2) := by congr 1; ring
    rw [heq]
    field_simp
    simp only [neg_div] at hexp hsq
    nlinarith [hexp,hsq]
  rw [hs] at h
  simpa only [he] using h

/-- An absolutely integrable majorant gains two powers of the Laplace parameter. -/
theorem laplace_sine_norm_integral_le (a r : ℝ) (ha : 0<a) :
    (∫ t : ℝ in Ioi 0, ‖Real.exp (-a*t)*Real.sin (r*t)‖) ≤ |r|/a^2 := by
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, |r| *(t*Real.exp (-a*t)) := by
      apply integral_mono_ae (laplace_sine_integrable a r ha).norm
        ((laplace_time_integrable a ha).const_mul |r|)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ Real.exp (-a*t)*|r*t| :=
          mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (Real.exp_pos _).le
        _ = _ := by rw [abs_mul, abs_of_pos ht]; ring
    _ = _ := by rw [integral_const_mul, laplace_time_integral a ha]; ring

/-- The exponential sine series converges in integral norm. -/
theorem sine_sinh_series_norm_summable (r : ℝ) :
    Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0,
      ‖2*(Real.exp (-((n:ℝ)+1/2)*t)*Real.sin (r*t))‖) := by
  have hp : Summable (fun n : ℕ => 1/(((n:ℝ)+1/2)^2)) := by
    simpa only [Real.rpow_two, sq_abs] using
      (Real.summable_one_div_nat_add_rpow (1/2) 2).mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _))
    _ (hp.mul_left (2*|r|))
  intro n
  simp only [norm_mul (2:ℝ), Real.norm_ofNat, integral_const_mul]
  calc
    _ ≤ 2*(|r|/(((n:ℝ)+1/2)^2)) :=
      mul_le_mul_of_nonneg_left (laplace_sine_norm_integral_le _ r (by positivity)) (by norm_num)
    _ = _ := by ring

/-- Exact sine transform of the reciprocal hyperbolic sine. -/
theorem sine_sinh_half_integral (r : ℝ) :
    (∫ t : ℝ in Ioi 0, Real.sin (r*t)/Real.sinh (t/2)) =
      Real.pi*Real.tanh (Real.pi*r) := by
  let F : ℕ → ℝ → ℝ := fun n t => 2*(Real.exp (-((n:ℝ)+1/2)*t)*Real.sin (r*t))
  have hF (n : ℕ) : IntegrableOn (F n) (Ioi 0) :=
    (laplace_sine_integrable _ r (by positivity)).const_mul 2
  have h := hasSum_integral_of_summable_integral_norm hF (sine_sinh_series_norm_summable r)
  have hi (n : ℕ) : (∫ t : ℝ in Ioi 0, F n t)=2*halfResolventTerm r n := by
    dsimp only [F]
    rw [integral_const_mul, laplace_sine_integral _ r (by positivity)]
    rfl
  have hp (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) :
      (∑' n : ℕ, F n t)=Real.sin (r*t)/Real.sinh (t/2) := by
    have hs := (inverse_sinh_half_hasSum t ht).mul_right (Real.sin (r*t))
    simpa only [F, mul_assoc, one_div_mul_eq_div] using hs.tsum_eq
  have he : (∫ t : ℝ in Ioi 0, ∑' n : ℕ, F n t) =
      ∫ t : ℝ in Ioi 0, Real.sin (r*t)/Real.sinh (t/2) :=
    setIntegral_congr_fun measurableSet_Ioi hp
  simp only [hi, he] at h
  exact h.unique (halfResolvent_hasSum r)

/-- Absolute integrability of the sine transform, for every real parameter. -/
theorem sine_sinh_half_integrable (r : ℝ) :
    IntegrableOn (fun t : ℝ => Real.sin (r*t)/Real.sinh (t/2)) (Ioi 0) := by
  by_cases hr : r=0
  · simp [hr]
  by_contra h
  have hz := integral_undef h
  rw [sine_sinh_half_integral, Real.tanh_eq_sinh_div_cosh] at hz
  have hs : Real.sinh (Real.pi*r)≠0 := by
    rw [ne_eq, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero hr
  exact (mul_ne_zero Real.pi_ne_zero (div_ne_zero hs (Real.cosh_pos _).ne')) hz

/-- A finite first moment for the reciprocal sinh kernel, with an explicit
convergent series value. This supplies a uniform Fubini majorant. -/
theorem time_sinh_half_integral_hasSum :
    HasSum (fun n : ℕ => 2*(1/(((n:ℝ)+1/2)^2)))
      (∫ t : ℝ in Ioi 0, t/Real.sinh (t/2)) := by
  let G : ℕ → ℝ → ℝ := fun n t => 2*(t*Real.exp (-((n:ℝ)+1/2)*t))
  have hG (n : ℕ) : IntegrableOn (G n) (Ioi 0) :=
    (laplace_time_integrable _ (by positivity)).const_mul 2
  have hp : Summable (fun n : ℕ => 1/(((n:ℝ)+1/2)^2)) := by
    simpa only [Real.rpow_two, sq_abs] using
      (Real.summable_one_div_nat_add_rpow (1/2) 2).mpr (by norm_num)
  have hi (n : ℕ) : (∫ t : ℝ in Ioi 0, G n t)=2*(1/(((n:ℝ)+1/2)^2)) := by
    dsimp only [G]
    rw [integral_const_mul, laplace_time_integral _ (by positivity)]
  have hn (n : ℕ) : (∫ t : ℝ in Ioi 0, ‖G n t‖)=∫ t : ℝ in Ioi 0, G n t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact Real.norm_of_nonneg (mul_nonneg (by norm_num) (mul_nonneg ht.le (Real.exp_pos _).le))
  have hns : Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0, ‖G n t‖) := by
    simp_rw [hn, hi]
    exact hp.mul_left 2
  have h := hasSum_integral_of_summable_integral_norm hG hns
  have he : (∫ t : ℝ in Ioi 0, ∑' n : ℕ, G n t) =
      ∫ t : ℝ in Ioi 0, t/Real.sinh (t/2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hs := (inverse_sinh_half_hasSum t ht).mul_right t
    have hg (n : ℕ) : G n t=(2*Real.exp (-((n:ℝ)+1/2)*t))*t := by
      dsimp only [G]
      ring
    simpa only [hg, one_div_mul_eq_div] using hs.tsum_eq
  simpa only [hi, he] using h

theorem time_sinh_half_integrable :
    IntegrableOn (fun t : ℝ => t/Real.sinh (t/2)) (Ioi 0) := by
  by_contra h
  have hz := integral_undef h
  have hs := time_sinh_half_integral_hasSum
  rw [hz] at hs
  have hb := hs.summable.le_tsum 0 (fun n _ => by positivity)
  rw [hs.tsum_eq] at hb
  norm_num at hb

theorem sine_sinh_half_norm_integral_le (r : ℝ) :
    (∫ t : ℝ in Ioi 0, ‖Real.sin (r*t)/Real.sinh (t/2)‖) ≤
      |r| * (∫ t : ℝ in Ioi 0, t/Real.sinh (t/2)) := by
  rw [← integral_const_mul]
  apply integral_mono_ae (sine_sinh_half_integrable r).norm
    (time_sinh_half_integrable.const_mul |r|)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have hp : 0<Real.sinh (t/2) := Real.sinh_pos_iff.mpr (div_pos ht (by norm_num))
  simp only [Real.norm_eq_abs, abs_div, abs_of_pos hp]
  calc
    _ ≤ |r*t|/Real.sinh (t/2) := div_le_div_of_nonneg_right Real.abs_sin_le_abs hp.le
    _ = _ := by rw [abs_mul, abs_of_pos ht]; ring

end QuantitativeMaass

#print axioms QuantitativeMaass.laplace_sine_integrable
#print axioms QuantitativeMaass.laplace_sine_integral
#print axioms QuantitativeMaass.laplace_time_integrable
#print axioms QuantitativeMaass.laplace_time_integral
#print axioms QuantitativeMaass.inverse_sinh_half_hasSum
#print axioms QuantitativeMaass.laplace_sine_norm_integral_le
#print axioms QuantitativeMaass.sine_sinh_series_norm_summable
#print axioms QuantitativeMaass.sine_sinh_half_integral
#print axioms QuantitativeMaass.sine_sinh_half_integrable
#print axioms QuantitativeMaass.time_sinh_half_integral_hasSum
#print axioms QuantitativeMaass.time_sinh_half_integrable
#print axioms QuantitativeMaass.sine_sinh_half_norm_integral_le
