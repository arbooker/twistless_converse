module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace CompactlySupported

namespace QuantitativeScalarSpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual positive vector functional on continuous functions of a
bounded self-adjoint operator, restricted to compactly supported functions
on its compact real spectrum. -/
def functional (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H) :
    C_c(spectrum ℝ A, ℝ) →ₚ[ℝ] ℝ where
  toFun f := (⟪v, (cfcHom hA f.toContinuousMap) v⟫_ℂ).re
  map_add' f g := by
    change (⟪v, (cfcHom hA (f.toContinuousMap + g.toContinuousMap)) v⟫_ℂ).re = _
    rw [map_add, add_apply, inner_add_right, Complex.add_re]
  map_smul' c f := by
    change (⟪v, (cfcHom hA (c • f.toContinuousMap)) v⟫_ℂ).re = _
    rw [map_smul, smul_apply, ← algebraMap_smul ℂ c, inner_smul_right]
    simp
  monotone' f g hfg := by
    have hh := cfcHom_mono hA (show f.toContinuousMap ≤ g.toContinuousMap from hfg)
    have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hh)).re_inner_nonneg_right v
    simp only [sub_apply, inner_sub_right, RCLike.re_to_complex,
      Complex.sub_re] at hp
    exact sub_nonneg.mp hp

/-- A finite regular scalar spectral measure on the actual real spectrum. -/
def measure (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H) :
    Measure (spectrum ℝ A) := RealRMK.rieszMeasure (functional A hA v)

instance measure_finite (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H) :
    IsFiniteMeasure (measure A hA v) := by unfold measure; infer_instance

instance measure_regular (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H) :
    (measure A hA v).Regular := by unfold measure; infer_instance

theorem integral_continuous (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H)
    (f : C(spectrum ℝ A, ℝ)) :
    (∫ s, f s ∂measure A hA v) = (⟪v, (cfcHom hA f) v⟫_ℂ).re := by
  let g : C_c(spectrum ℝ A, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure (functional A hA v) g

theorem measure_real_univ (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H) :
    (measure A hA v).real Set.univ = ‖v‖^2 := by
  simpa [inner_self_eq_norm_sq, ← Complex.ofReal_pow] using
    integral_continuous A hA v (1 : C(spectrum ℝ A, ℝ))

theorem measure_univ (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H) :
    measure A hA v Set.univ = ENNReal.ofReal (‖v‖^2) := by
  rw [← measure_real_univ A hA v, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

def realMeasure (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H) : Measure ℝ :=
  (measure A hA v).map Subtype.val

instance realMeasure_finite (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H) :
    IsFiniteMeasure (realMeasure A hA v) := by unfold realMeasure; infer_instance

theorem realMeasure_univ (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H) :
    realMeasure A hA v Set.univ = ENNReal.ofReal (‖v‖^2) := by
  rw [realMeasure, Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

theorem realMeasure_probability (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {v : H} (hv : ‖v‖ = 1) : IsProbabilityMeasure (realMeasure A hA v) := by
  constructor
  simp [realMeasure_univ, hv]

theorem realMeasure_compl_spectrum (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H) :
    realMeasure A hA v (spectrum ℝ A)ᶜ = 0 := by
  rw [realMeasure, Measure.map_apply measurable_subtype_coe
    (spectrum.isCompact A).measurableSet.compl]
  simp

theorem integral_realMeasure (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ s, f s ∂realMeasure A hA v) = (⟪v, (cfc f A) v⟫_ℂ).re := by
  rw [realMeasure, integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable,
    cfc_apply f A hA hf.continuousOn]
  exact integral_continuous A hA v ⟨_, hf.comp continuous_subtype_val⟩

theorem moment (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H) (n : ℕ) :
    (∫ s, s^n ∂realMeasure A hA v) = (⟪v, (A^n) v⟫_ℂ).re := by
  rw [integral_realMeasure A hA v _ (by fun_prop), cfc_pow_id A n hA]

#print axioms integral_continuous
#print axioms measure_real_univ
#print axioms measure_univ
#print axioms realMeasure_univ
#print axioms realMeasure_probability
#print axioms realMeasure_compl_spectrum
#print axioms integral_realMeasure
#print axioms moment

end QuantitativeScalarSpectralMeasure
