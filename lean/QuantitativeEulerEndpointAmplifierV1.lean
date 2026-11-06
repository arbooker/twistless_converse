module

public import QuantitativeEulerEndpointTracialProductV1
public import QuantitativeSpectralFilterV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSoftUpdate
open Polynomial MeasureTheory

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- Polynomial spectral amplifier used in the actual monotone update. -/
def amplifierPolynomial (d : ℕ) : ℝ[X] := 1-(1-X)^d

def amplifier (C : 𝔄) (d : ℕ) : 𝔄 := aeval C (amplifierPolynomial d)

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
theorem amplifier_eq (C : 𝔄) (d : ℕ) : amplifier C d=1-(1-C)^d := by
  simp only [amplifier,amplifierPolynomial,map_sub,map_one,map_pow,aeval_X]

theorem amplifier_le_linear (C : 𝔄) (hC0 : 0≤C) (hC1 : C≤1) (d : ℕ) :
    amplifier C d≤(d:ℝ) • C := by
  have hC := IsSelfAdjoint.of_nonneg hC0
  have hn : ‖C‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg C hC0).mpr hC1
  have hh := cfc_mono (a := C) (f := (amplifierPolynomial d).eval)
    (g := ((Polynomial.C (d:ℝ))*X).eval) (fun x hx => by
      have hx1 : x≤1 := (le_abs_self x).trans ((quasispectrum.norm_le_norm_of_mem
        (spectrum_subset_quasispectrum ℝ C hx)).trans hn)
      have h := one_add_mul_le_pow (by linarith : (-2:ℝ)≤-x) d
      simp only [amplifierPolynomial,eval_sub,eval_one,eval_pow,eval_X,eval_mul,eval_C]
      simp only [sub_eq_add_neg,mul_neg] at *
      linarith)
  simpa only [cfc_polynomial _ C hC,map_mul,aeval_C,aeval_X,← Algebra.smul_def,amplifier] using hh

/-- Spectral mass above lambda produces an explicit trace contribution.
The measure is constructed from the actual operator and positive trace. -/
theorem amplifier_trace_lower (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (C : 𝔄) (hC0 : 0≤C) (hC1 : C≤1) (d : ℕ) (lam : ℝ) :
    (1-Real.exp (-(d:ℝ)*lam)) *
      (QuantitativeTracialSpectralMeasure.measure τ hτ C (IsSelfAdjoint.of_nonneg hC0)).real
        {x : spectrum ℝ C | lam≤(x:ℝ)} ≤ τ (amplifier C d) := by
  let μ := QuantitativeTracialSpectralMeasure.measure τ hτ C (IsSelfAdjoint.of_nonneg hC0)
  let E := {x : spectrum ℝ C | lam≤(x:ℝ)}
  let v := 1-Real.exp (-(d:ℝ)*lam)
  have hE : MeasurableSet E := measurableSet_le measurable_const measurable_subtype_coe
  have hi : Integrable (E.indicator (fun _ => v)) μ := (integrable_const v).indicator hE
  have hc : Continuous (fun x : spectrum ℝ C => 1-(1-(x:ℝ))^d) := by fun_prop
  have hg : Integrable (fun x : spectrum ℝ C => 1-(1-(x:ℝ))^d) μ := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn : ‖C‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg C hC0).mpr hC1
  have hm := integral_mono hi hg (fun x => by
    have hx0 : 0≤(x:ℝ) := spectrum_nonneg_of_nonneg hC0 x.property
    have hx1 : (x:ℝ)≤1 := (le_abs_self (x:ℝ)).trans ((quasispectrum.norm_le_norm_of_mem
      (spectrum_subset_quasispectrum ℝ C x.property)).trans hn)
    by_cases hx : x∈E
    · rw [Set.indicator_of_mem hx]
      have ht := QuantitativeSpectralFilter.filter_le_exp (by norm_num : (0:ℝ)<1) hx1 d
      simp only [div_one] at ht
      have he : Real.exp (-(d:ℝ)*(x:ℝ))≤Real.exp (-(d:ℝ)*lam) := by
        apply Real.exp_le_exp.mpr
        have hdx : 0≤(d:ℝ) := Nat.cast_nonneg d
        change lam≤(x:ℝ) at hx
        nlinarith
      dsimp only [v]
      linarith
    · rw [Set.indicator_of_notMem hx]
      have hp : (1-(x:ℝ))^d≤1 := by
        simpa only [one_pow] using pow_le_pow_left₀ (by linarith : 0≤1-(x:ℝ))
          (by linarith : 1-(x:ℝ)≤1) d
      linarith)
  have he := QuantitativeTracialSpectralMeasure.integral_cfc τ hτ C (IsSelfAdjoint.of_nonneg hC0)
    (amplifierPolynomial d).eval (amplifierPolynomial d).continuous.continuousOn
  rw [cfc_polynomial _ C (IsSelfAdjoint.of_nonneg hC0)] at he
  simp only [amplifierPolynomial,eval_sub,eval_one,eval_pow,eval_X] at he
  rw [integral_indicator_const v hE,smul_eq_mul,he] at hm
  simpa only [v,μ,E,amplifier,amplifierPolynomial,mul_comm] using hm

#print axioms amplifier_eq
#print axioms amplifier_le_linear
#print axioms amplifier_trace_lower
end QuantitativeEulerEndpointSoftUpdate
