module

public import QuantitativeMaassAutomorphicL2V1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass.AutomorphicL2

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (H : Subgroup G) (g : G)
    (hc : ∀ a ∈ H, g * a * g⁻¹ ∈ H) (hci : ∀ a ∈ H, g⁻¹ * a * g ∈ H)
    (ρ : α → ℝ≥0∞) (hρ : Measurable ρ)
    (hn : ∀ x, ∑' a : H, ρ (a.val • x) = 1)

include hmp hc hci hρ hn in
theorem eLpNorm_normalizer (f : α → ℂ) (hf : Measurable f)
    (hinv : ∀ a : H, ∀ x, f (a.val • x) = f x) :
    eLpNorm (fun x => f (g • x)) 2 (μ.withDensity ρ) = eLpNorm f 2 (μ.withDensity ρ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (μ := μ.withDensity ρ)
      (f := fun x => f (g • x)) (by norm_num) (by norm_num)
      (hf.comp (hmp g).measurable).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (μ := μ.withDensity ρ)
      (f := f) (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  congr 1
  apply OrbitIntegral.lintegral_normalizer μ hmp H g hc hci ρ hρ hn
    (fun x => ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal)
  · fun_prop
  · intro a x
    rw [hinv]

/-- Literal pullback by the quotient normalizer on measurable representatives. -/
def normalizerRepresentative : representatives H (μ.withDensity ρ) →ₗ[ℂ]
    representatives H (μ.withDensity ρ) where
  toFun f := ⟨fun x => f.val (g • x),
    (f.property.1.comp (hmp g).measurable), (by
      intro a x
      have hi := f.property.2.1 ⟨g * a.val * g⁻¹, hc a.val a.property⟩ (g • x)
      simpa only [mul_smul, inv_smul_smul] using hi), (by
      change eLpNorm (fun x => f.val (g • x)) 2 (μ.withDensity ρ) < ∞
      rw [eLpNorm_normalizer μ hmp H g hc hci ρ hρ hn f.val f.property.1 f.property.2.1]
      exact f.property.2.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem normalizerRepresentative_norm (f : representatives H (μ.withDensity ρ)) :
    ‖denseEmbedding H (μ.withDensity ρ)
      (normalizerRepresentative μ hmp H g hc hci ρ hρ hn f)‖ =
      ‖denseEmbedding H (μ.withDensity ρ) f‖ := by
  rw [embedding_norm, embedding_norm]
  congr 1
  exact eLpNorm_normalizer μ hmp H g hc hci ρ hρ hn f.val f.property.1 f.property.2.1

/-- The actual normalizer extends isometrically to the automorphic Hilbert
completion. Its definition uses the proved quotient integral identity. -/
def normalizerIsometry : space H (μ.withDensity ρ) →ₗᵢ[ℂ] space H (μ.withDensity ρ) :=
  ((denseEmbedding H (μ.withDensity ρ)).comp
    (normalizerRepresentative μ hmp H g hc hci ρ hρ hn)).extendOfIsometry
    (denseEmbedding_dense H (μ.withDensity ρ))
    (normalizerRepresentative_norm μ hmp H g hc hci ρ hρ hn)

theorem normalizerIsometry_apply (f : representatives H (μ.withDensity ρ)) :
    normalizerIsometry μ hmp H g hc hci ρ hρ hn (denseEmbedding H (μ.withDensity ρ) f) =
      denseEmbedding H (μ.withDensity ρ)
        (normalizerRepresentative μ hmp H g hc hci ρ hρ hn f) := by
  exact LinearMap.extendOfIsometry_eq _ _ _ f

#print axioms eLpNorm_normalizer
#print axioms normalizerIsometry_apply

end QuantitativeMaass.AutomorphicL2
