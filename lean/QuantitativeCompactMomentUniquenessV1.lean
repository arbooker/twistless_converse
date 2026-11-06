module

public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set
open scoped CompactlySupported

namespace QuantitativeCompactMomentUniqueness

variable {s : Set ℝ} [CompactSpace s]

theorem continuous_integrable (μ : Measure s) [IsFiniteMeasure μ] (f : C(s, ℝ)) :
    Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

def integralCLM (μ : Measure s) [IsFiniteMeasure μ] : C(s, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (continuous_integrable μ f) (continuous_integrable μ g)
      map_smul' := fun c f => integral_smul c f }
    (μ.real univ) (fun f => by
      change ‖∫ x, f x ∂μ‖ ≤ μ.real univ * ‖f‖
      simpa only [mul_comm] using norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall f.norm_coe_le_norm))

theorem polynomial_integrable (μ : Measure s) [IsFiniteMeasure μ] (p : Polynomial ℝ) :
    Integrable (fun x : s => p.eval (x : ℝ)) μ :=
  continuous_integrable μ (p.toContinuousMapOn s)

theorem polynomial_integrals_eq (μ ν : Measure s) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ n : ℕ, (∫ x : s, (x : ℝ)^n ∂μ) = ∫ x : s, (x : ℝ)^n ∂ν)
    (p : Polynomial ℝ) :
    (∫ x : s, p.eval (x : ℝ) ∂μ) = ∫ x : s, p.eval (x : ℝ) ∂ν := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp_rw [Polynomial.eval_add]
    rw [integral_add (polynomial_integrable μ p) (polynomial_integrable μ q),
      integral_add (polynomial_integrable ν p) (polynomial_integrable ν q), hp, hq]
  | monomial n c =>
    simp_rw [Polynomial.eval_monomial, integral_const_mul, hm n]

/-- On a compact real set, equality of all moments determines a finite
regular measure. Polynomial density and continuity of integration are
proved inputs, rather than a moment-determinacy assumption. -/
theorem eq_of_moments (μ ν : Measure s) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.Regular] [ν.Regular]
    (hm : ∀ n : ℕ, (∫ x : s, (x : ℝ)^n ∂μ) = ∫ x : s, (x : ℝ)^n ∂ν) : μ = ν := by
  have hc : IsClosed {f : C(s, ℝ) | integralCLM μ f = integralCLM ν f} :=
    isClosed_eq (integralCLM μ).continuous (integralCLM ν).continuous
  have hp : (polynomialFunctions s : Set C(s, ℝ)) ⊆
      {f : C(s, ℝ) | integralCLM μ f = integralCLM ν f} := by
    intro f hf
    rw [polynomialFunctions_coe] at hf
    obtain ⟨p, rfl⟩ := hf
    exact polynomial_integrals_eq μ ν hm p
  have hd : closure (polynomialFunctions s : Set C(s, ℝ)) = univ := by
    rw [← Subalgebra.topologicalClosure_coe, polynomialFunctions.topologicalClosure]
    rfl
  have he : ∀ f : C(s, ℝ), integralCLM μ f = integralCLM ν f := by
    intro f
    exact (closure_minimal hp hc) (hd.symm ▸ mem_univ f)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact he f.toContinuousMap

/-- Finite measures on the real line with a common compact support are
determined by their moments. The support condition is literal zero mass
outside the compact set. -/
theorem real_eq_of_moments (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {K : Set ℝ} (hK : IsCompact K) (hμ : μ Kᶜ = 0) (hν : ν Kᶜ = 0)
    (hm : ∀ n : ℕ, (∫ x : ℝ, x^n ∂μ) = ∫ x : ℝ, x^n ∂ν) : μ = ν := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μ' : Measure K := μ.comap Subtype.val
  let ν' : Measure K := ν.comap Subtype.val
  have hm' (n : ℕ) : (∫ x : K, (x : ℝ)^n ∂μ') = ∫ x : K, (x : ℝ)^n ∂ν' := by
    change (∫ x : K, (x : ℝ)^n ∂μ.comap Subtype.val) =
      ∫ x : K, (x : ℝ)^n ∂ν.comap Subtype.val
    rw [integral_subtype_comap (μ := μ) hK.measurableSet (fun x : ℝ => x^n),
      integral_subtype_comap (μ := ν) hK.measurableSet (fun x : ℝ => x^n),
      Measure.restrict_eq_self_of_ae_mem hμ, Measure.restrict_eq_self_of_ae_mem hν]
    exact hm n
  have he := congrArg (fun ρ : Measure K => ρ.map Subtype.val) (eq_of_moments μ' ν' hm')
  simpa only [μ', ν', map_comap_subtype_coe hK.measurableSet,
    Measure.restrict_eq_self_of_ae_mem hμ, Measure.restrict_eq_self_of_ae_mem hν] using he

#print axioms continuous_integrable
#print axioms polynomial_integrals_eq
#print axioms eq_of_moments
#print axioms real_eq_of_moments

end QuantitativeCompactMomentUniqueness
