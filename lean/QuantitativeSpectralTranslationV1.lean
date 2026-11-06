module

public import QuantitativeTracialSpectralMeasureV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralTranslation

open MeasureTheory Set
open scoped CompactlySupported

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- The spectral distribution on the real line, rather than on a varying
spectrum subtype, permits literal comparison under scalar shifts. -/
def realMeasure (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) (A : 𝔄) (hA : IsSelfAdjoint A) :
    Measure ℝ := (QuantitativeTracialSpectralMeasure.measure τ hτ A hA).map Subtype.val

instance realMeasure_finite (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) (A : 𝔄)
    (hA : IsSelfAdjoint A) : IsFiniteMeasure (realMeasure τ hτ A hA) := by
  unfold realMeasure
  infer_instance

theorem integral_realMeasure (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) (A : 𝔄)
    (hA : IsSelfAdjoint A) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂realMeasure τ hτ A hA) = τ (cfc f A) := by
  rw [realMeasure, integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable]
  exact QuantitativeTracialSpectralMeasure.integral_cfc τ hτ A hA f hf.continuousOn

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
theorem shift_selfAdjoint (A : 𝔄) (hA : IsSelfAdjoint A) (r : ℝ) :
    IsSelfAdjoint (A + algebraMap ℝ 𝔄 r) :=
  hA.add (IsSelfAdjoint.algebraMap 𝔄 (.all r))

/-- Spectral distributions translate by exactly the scalar added to the
operator. This follows from actual CFC composition and uniqueness of RMK
measures, without a postulated spectral identification. -/
theorem realMeasure_shift (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) (A : 𝔄)
    (hA : IsSelfAdjoint A) (r : ℝ) :
    realMeasure τ hτ (A + algebraMap ℝ 𝔄 r) (shift_selfAdjoint A hA r) =
      (realMeasure τ hτ A hA).map (fun x => x+r) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_realMeasure τ hτ _ _ f f.continuous,
    integral_map (by fun_prop)
      (show AEStronglyMeasurable (fun x : ℝ => f x)
        ((realMeasure τ hτ A hA).map (fun x => x+r)) from
          (show Continuous (fun x : ℝ => f x) from f.continuous).aestronglyMeasurable),
    integral_realMeasure τ hτ A hA (fun x => f (x+r)) (by fun_prop)]
  congr 1
  have hc := cfc_comp (f : ℝ → ℝ) (fun x : ℝ => x+r) A hA
    f.continuous.continuousOn (by fun_prop)
  rw [cfc_add_const r (fun x : ℝ => x) A continuous_id.continuousOn hA,
    cfc_id' ℝ A hA] at hc
  exact hc.symm

/-- Exact low-spectrum equality, with no loss at boundary atoms. -/
theorem low_mass_shift (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) (A : 𝔄)
    (hA : IsSelfAdjoint A) (r lam : ℝ) :
    (QuantitativeTracialSpectralMeasure.measure τ hτ (A + algebraMap ℝ 𝔄 r)
      (shift_selfAdjoint A hA r)).real
        {x : spectrum ℝ (A + algebraMap ℝ 𝔄 r) | (x:ℝ) ≤ lam+r} =
    (QuantitativeTracialSpectralMeasure.measure τ hτ A hA).real
        {x : spectrum ℝ A | (x:ℝ) ≤ lam} := by
  have he := congrArg (fun μ : Measure ℝ => μ (Iic (lam+r)))
    (realMeasure_shift τ hτ A hA r)
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic] at he
  have hs : (fun x : ℝ => x+r) ⁻¹' Iic (lam+r) = Iic lam := by
    ext x
    simp
  rw [hs, realMeasure, realMeasure,
    Measure.map_apply measurable_subtype_coe measurableSet_Iic,
    Measure.map_apply measurable_subtype_coe measurableSet_Iic] at he
  exact congrArg ENNReal.toReal he

/-- The regularization by epsilon is removed using cutoff twice epsilon. -/
theorem low_mass_double_shift (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) (A : 𝔄)
    (hA : IsSelfAdjoint A) (ε : ℝ) :
    (QuantitativeTracialSpectralMeasure.measure τ hτ (A + algebraMap ℝ 𝔄 ε)
      (shift_selfAdjoint A hA ε)).real
        {x : spectrum ℝ (A + algebraMap ℝ 𝔄 ε) | (x:ℝ) ≤ 2*ε} =
    (QuantitativeTracialSpectralMeasure.measure τ hτ A hA).real
        {x : spectrum ℝ A | (x:ℝ) ≤ ε} := by
  simpa only [two_mul] using low_mass_shift τ hτ A hA ε ε

#print axioms realMeasure_shift
#print axioms low_mass_shift
#print axioms low_mass_double_shift

end QuantitativeSpectralTranslation
