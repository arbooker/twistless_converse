module

public import QuantitativeSpectralDistributionV1
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set
open scoped CompactlySupported

namespace QuantitativeTracialSpectralMeasure

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- The positive functional induced by an actual positive bounded functional
and continuous functional calculus. Cyclicity is unnecessary for this step. -/
def functional (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA : IsSelfAdjoint A) : C_c(spectrum ℝ A, ℝ) →ₚ[ℝ] ℝ where
  toFun f := τ (cfcHom hA f.toContinuousMap)
  map_add' f g := by
    change τ (cfcHom hA (f.toContinuousMap + g.toContinuousMap)) = _
    rw [map_add, map_add]
  map_smul' c f := by
    change τ (cfcHom hA (c • f.toContinuousMap)) = _
    rw [map_smul, map_smul]
    rfl
  monotone' f g hfg := hτ (cfcHom_mono hA hfg)

/-- The finite regular spectral distribution of the given functional. -/
def measure (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) (A : 𝔄) (hA : IsSelfAdjoint A) :
    Measure (spectrum ℝ A) := RealRMK.rieszMeasure (functional τ hτ A hA)

instance measure_finite (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) (A : 𝔄)
    (hA : IsSelfAdjoint A) : IsFiniteMeasure (measure τ hτ A hA) := by
  unfold measure
  infer_instance

instance measure_regular (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) (A : 𝔄)
    (hA : IsSelfAdjoint A) : (measure τ hτ A hA).Regular := by
  unfold measure
  infer_instance

theorem integral_continuous (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA : IsSelfAdjoint A) (f : C(spectrum ℝ A, ℝ)) :
    (∫ x, f x ∂measure τ hτ A hA) = τ (cfcHom hA f) := by
  let g : C_c(spectrum ℝ A, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure (functional τ hτ A hA) g

theorem measure_real_univ (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA : IsSelfAdjoint A) : (measure τ hτ A hA).real univ = τ 1 := by
  simpa using integral_continuous τ hτ A hA (1 : C(spectrum ℝ A, ℝ))

theorem integral_cfc (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA : IsSelfAdjoint A) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    (∫ x : spectrum ℝ A, f x ∂measure τ hτ A hA) = τ (cfc f A) := by
  rw [cfc_apply f A hA hf]
  exact integral_continuous τ hτ A hA ⟨_, hf.domRestrict⟩

theorem integral_id (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA : IsSelfAdjoint A) :
    (∫ x : spectrum ℝ A, (x : ℝ) ∂measure τ hτ A hA) = τ A := by
  rw [integral_cfc τ hτ A hA (fun x : ℝ => x) continuous_id.continuousOn,
    cfc_id' ℝ A hA]

theorem integral_log (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA : IsSelfAdjoint A) (hpos : IsStrictlyPositive A) :
    (∫ x : spectrum ℝ A, Real.log x ∂measure τ hτ A hA) = τ (CFC.log A) := by
  have hf : ContinuousOn Real.log (spectrum ℝ A) :=
    Real.continuousOn_log.mono (fun x hx => (hpos.spectrum_pos hx).ne')
  exact integral_cfc τ hτ A hA Real.log hf

/-- Fresh spectral mass for the spectral distribution of the actual operator.
The mean hypothesis is the operator trace identity. -/
theorem fresh_high_mass (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA : IsSelfAdjoint A) (hnorm : ‖A‖ ≤ 1)
    {n theta : ℝ} (hn : 0 < n) (htheta : 0 ≤ theta)
    (htrace : τ A = τ 1 / n) :
    (1-theta) * τ 1 / n ≤
      (measure τ hτ A hA).real {x : spectrum ℝ A | theta/n ≤ (x : ℝ)} := by
  have hi : Integrable (fun x : spectrum ℝ A => (x : ℝ)) (measure τ hτ A hA) :=
    continuous_subtype_val.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hh := QuantitativeSpectralDistribution.fresh_high_mass_theta
    (measure τ hτ A hA) (fun x : spectrum ℝ A => (x : ℝ)) measurable_subtype_coe
    hi hn htheta
    (Filter.Eventually.of_forall (fun x =>
      (le_abs_self (x : ℝ)).trans
        ((quasispectrum.norm_le_norm_of_mem
          (spectrum_subset_quasispectrum ℝ A x.property)).trans hnorm)))
    (by rwa [integral_id, measure_real_univ])
  rwa [measure_real_univ] at hh

/-- The small-spectrum estimate for the constructed spectral distribution.
Its logarithmic input is an operator trace, rather than a postulated measure
integral. The determinant argument can therefore feed into this theorem. -/
theorem small_mass_of_trace_log (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA : IsSelfAdjoint A) (hpos : IsStrictlyPositive A)
    {s K lam : ℝ} (hs : 0 < s) (hK : 0 < K) (hlam : 0 < lam) (hlamK : lam < K)
    (hupper : ∀ x ∈ spectrum ℝ A, x ≤ K)
    (hlower : τ 1 * Real.log s ≤ τ (CFC.log A)) :
    (measure τ hτ A hA).real {x : spectrum ℝ A | (x : ℝ) ≤ lam} ≤
      τ 1 * Real.log (K / s) / Real.log (K / lam) := by
  have hf : ContinuousOn Real.log (spectrum ℝ A) :=
    Real.continuousOn_log.mono (fun x hx => (hpos.spectrum_pos hx).ne')
  have hi : Integrable (fun x : spectrum ℝ A => Real.log x) (measure τ hτ A hA) :=
    hf.domRestrict.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := QuantitativeSpectralDistribution.small_mass_of_log_integral
    (measure τ hτ A hA) (fun x : spectrum ℝ A => (x : ℝ))
    measurable_subtype_coe hi hs hK hlam hlamK
    (Filter.Eventually.of_forall (fun x => hpos.spectrum_pos x.property))
    (Filter.Eventually.of_forall (fun x => hupper x x.property))
    (by rwa [measure_real_univ, integral_log τ hτ A hA hpos])
  rwa [measure_real_univ] at hh

/-- The same determinant estimate with the upper support bound discharged
by an operator norm bound. -/
theorem small_mass_of_trace_log_norm (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA : IsSelfAdjoint A) (hpos : IsStrictlyPositive A)
    {s K lam : ℝ} (hs : 0 < s) (hK : 0 < K) (hlam : 0 < lam) (hlamK : lam < K)
    (hnorm : ‖A‖ ≤ K) (hlower : τ 1 * Real.log s ≤ τ (CFC.log A)) :
    (measure τ hτ A hA).real {x : spectrum ℝ A | (x : ℝ) ≤ lam} ≤
      τ 1 * Real.log (K / s) / Real.log (K / lam) := by
  apply small_mass_of_trace_log τ hτ A hA hpos hs hK hlam hlamK ?_ hlower
  intro x hx
  exact (le_abs_self x).trans ((quasispectrum.norm_le_norm_of_mem
    (spectrum_subset_quasispectrum ℝ A hx)).trans hnorm)

#print axioms integral_continuous
#print axioms measure_real_univ
#print axioms integral_id
#print axioms integral_log
#print axioms fresh_high_mass
#print axioms small_mass_of_trace_log
#print axioms small_mass_of_trace_log_norm

end QuantitativeTracialSpectralMeasure
