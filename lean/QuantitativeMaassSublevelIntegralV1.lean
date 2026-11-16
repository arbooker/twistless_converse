module

public import QuantitativeMaassWindowAbelDecayV1
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- Tail sets for the reciprocal square root are controlled by small sublevels.
The convention at zero is harmless here; nullity of zero sets is separate. -/
theorem inverse_sqrt_tail_subset {X : Type*} (f : X → ℝ) (hf : ∀ x,0≤f x)
    (t : ℝ) (ht : 0<t) :
    {x | t<1/Real.sqrt (f x)}⊆{x | f x<1/t^2} := by
  intro x hx
  have hs : 0<Real.sqrt (f x) := one_div_pos.mp (ht.trans hx)
  have hh : t*Real.sqrt (f x)<1 := (lt_div_iff₀ hs).mp hx
  have hsq := mul_self_lt_mul_self (by positivity : 0≤t*Real.sqrt (f x)) hh
  have heq : (t*Real.sqrt (f x))*(t*Real.sqrt (f x))=t^2*f x := by
    nlinarith [Real.sq_sqrt (hf x)]
  rw [heq] at hsq
  exact (lt_div_iff₀ (sq_pos_of_pos ht)).mpr (by nlinarith)

/-- A linear small-sublevel estimate gives an explicit integrable majorant for
all reciprocal-square-root tail measures. -/
theorem inverse_sqrt_tail_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : ∀ x,0≤f x)
    (V C : ℝ) (hV : 0≤V) (hC : 0≤C) (hvol : μ univ≤ENNReal.ofReal V)
    (hsub : ∀ r : ℝ,0<r → μ {x | f x<r}≤ENNReal.ofReal (C*r))
    (t : ℝ) (ht : 0<t) :
    μ {x | t<1/Real.sqrt (f x)}≤ENNReal.ofReal (2*(V+C)*(1+t^2)⁻¹) := by
  have hden : 0<1+t^2 := by positivity
  by_cases ht1 : t≤1
  · apply ((measure_mono (subset_univ _)).trans hvol).trans
    apply ENNReal.ofReal_le_ofReal
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hden).mpr
    have hsq : t^2≤1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hV]
  · have ht1' : 1≤t := (lt_of_not_ge ht1).le
    apply ((measure_mono (inverse_sqrt_tail_subset f hf t ht)).trans
      (hsub (1/t^2) (by positivity))).trans
    apply ENNReal.ofReal_le_ofReal
    rw [← div_eq_mul_inv]
    have hsq : 1≤t^2 := by nlinarith
    have hh : C*(1+t^2)≤2*(V+C)*t^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq hC,mul_nonneg hV (sq_nonneg t)]
    simpa only [mul_one_div] using (div_le_div_iff₀ (sq_pos_of_pos ht) hden).mpr hh

/-- A finite measure and linear sublevel bound imply absolute integrability of
1/sqrt(f), with the explicit bound pi*(V+C). No integrability premise is used. -/
theorem inverse_sqrt_integrable_of_sublevel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hfm : Measurable f) (hf : ∀ x,0≤f x)
    (V C : ℝ) (hV : 0≤V) (hC : 0≤C) (hvol : μ univ≤ENNReal.ofReal V)
    (hsub : ∀ r : ℝ,0<r → μ {x | f x<r}≤ENNReal.ofReal (C*r)) :
    Integrable (fun x => 1/Real.sqrt (f x)) μ ∧
      (∫ x,1/Real.sqrt (f x) ∂μ)≤Real.pi*(V+C) := by
  have hm : Measurable (fun x => 1/Real.sqrt (f x)) := by fun_prop
  have hn : ∀ x,0≤1/Real.sqrt (f x) := fun x => by positivity
  have hi : IntegrableOn (fun t : ℝ => 2*(V+C)*(1+t^2)⁻¹) (Ioi (0:ℝ)) :=
    integrable_inv_one_add_sq.integrableOn.const_mul _
  have hb : (∫⁻ x,ENNReal.ofReal (1/Real.sqrt (f x)) ∂μ)≤ENNReal.ofReal (Real.pi*(V+C)) := by
    rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hn) hm.aemeasurable]
    calc
      _ ≤ ∫⁻ t in Ioi (0:ℝ),ENNReal.ofReal (2*(V+C)*(1+t^2)⁻¹) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact inverse_sqrt_tail_bound μ f hf V C hV hC hvol hsub t ht
      _ = ENNReal.ofReal (Real.pi*(V+C)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun t => by positivity)),
          integral_const_mul,integral_Ioi_inv_one_add_sq,Real.arctan_zero,sub_zero]
        congr 1
        ring
  have hint : Integrable (fun x => 1/Real.sqrt (f x)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Eventually.of_forall hn)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  refine ⟨hint,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hn)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

/-- Linear sublevel area also rules out a positive-measure zero set. -/
theorem measure_zero_of_linear_sublevels {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (C : ℝ)
    (hsub : ∀ r : ℝ,0<r → μ {x | f x<r}≤ENNReal.ofReal (C*r)) :
    μ {x | f x=0}=0 := by
  have hle : ∀ r : ℝ,0<r → μ {x | f x=0}≤ENNReal.ofReal (C*r) := by
    intro r hr
    exact (measure_mono (fun x hx => by simp only [mem_ofPred_eq] at *;rw [hx];exact hr)).trans (hsub r hr)
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C*r)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (C*r)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
    simpa only [mul_zero,ENNReal.ofReal_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_antisymm _ bot_le
  exact ge_of_tendsto hlim (by filter_upwards [self_mem_nhdsWithin] with r hr;exact hle r hr)

#print axioms inverse_sqrt_tail_subset
#print axioms inverse_sqrt_tail_bound
#print axioms inverse_sqrt_integrable_of_sublevel
#print axioms measure_zero_of_linear_sublevels

end QuantitativeMaass
