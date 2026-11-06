module

public import QuantitativeMaassNormalizerL2V1
public import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace QuantitativeMaass.AutomorphicL2

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (H : Subgroup G) (g : G)
    (hc : ∀ a ∈ H, g * a * g⁻¹ ∈ H) (hci : ∀ a ∈ H, g⁻¹ * a * g ∈ H)
    (ρ : α → ℝ≥0∞) (hρ : Measurable ρ)
    (hn : ∀ x, ∑' a : H, ρ (a.val • x) = 1)

/-- Squaring into the automorphy group makes the actual normalizer an
involution on the completed quotient Hilbert space. -/
theorem normalizerIsometry_involutive (hgg : g*g ∈ H) :
    Function.Involutive (normalizerIsometry μ hmp H g hc hci ρ hρ hn) := by
  let U := normalizerIsometry μ hmp H g hc hci ρ hρ hn
  have he : (fun x => U (U x)) = id := by
    apply (denseEmbedding_dense H (μ.withDensity ρ)).equalizer
      (U.continuous.comp U.continuous) continuous_id
    funext f
    change U (U (denseEmbedding H (μ.withDensity ρ) f)) = denseEmbedding H (μ.withDensity ρ) f
    simp only [U, normalizerIsometry_apply]
    apply congrArg (denseEmbedding H (μ.withDensity ρ))
    apply Subtype.ext
    funext x
    change f.val (g • (g • x)) = f.val x
    rw [← mul_smul]
    exact f.property.2.1 ⟨g*g,hgg⟩ x
  intro x
  exact congrFun he x

/-- The same geometric square relation proves self-adjointness, using the
actual isometric action rather than assuming a Hecke spectral property. -/
theorem normalizerIsometry_selfAdjoint (hgg : g*g ∈ H) :
    IsSelfAdjoint (normalizerIsometry μ hmp H g hc hci ρ hρ hn).toContinuousLinearMap := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro x y
  have hi := (normalizerIsometry μ hmp H g hc hci ρ hρ hn).inner_map_map x
    (normalizerIsometry μ hmp H g hc hci ρ hρ hn y)
  rw [normalizerIsometry_involutive μ hmp H g hc hci ρ hρ hn hgg y] at hi
  exact hi

#print axioms normalizerIsometry_involutive
#print axioms normalizerIsometry_selfAdjoint

end QuantitativeMaass.AutomorphicL2
