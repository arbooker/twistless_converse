module

public import AsymptoticOrbitDensityCoverV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticOrbitDensity

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]

/-- Unfolding a nonnegative orbit density over a genuine fundamental
domain computes its integral exactly, including arbitrary constant mass. -/
theorem integral_eq_mass_mul_volume (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (f : α → ℝ≥0∞) (hf : Measurable f) (c : ℝ≥0∞)
    (hn : ∀ x,∑' g : G,f (g • x)=c)
    (s : Set α) (hs : IsFundamentalDomain G s μ) :
    (∫⁻ x,f x ∂μ)=c*μ s := by
  let : MeasurableConstSMul G α := ⟨fun g => (hmp g).measurable⟩
  let : SMulInvariantMeasure G α μ := ⟨fun g _ ht => (hmp g).measure_preimage ht.nullMeasurableSet⟩
  rw [hs.lintegral_eq_tsum'']
  have hmeas (g : G) : Measurable (fun x => f (g • x)) := hf.comp (hmp g).measurable
  rw [← lintegral_tsum (μ:=μ.restrict s) (fun g => (hmeas g).aemeasurable)]
  simp only [hn,lintegral_const,Measure.restrict_apply_univ]

#print axioms integral_eq_mass_mul_volume

end AsymptoticOrbitDensity
