module

public import QuantitativeMaassPoincareSmoothV1
public import QuantitativeMaassPoincareL2V1
public import QuantitativeMaassGreenEnergyV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Matrix Set UpperHalfPlane
open scoped ENNReal Topology ContDiff MatrixGroups

namespace QuantitativeMaass
open MaassDifferential

/-- The restriction of a smooth Cartesian function is genuinely continuous
on the upper half-plane, with no condition at its boundary. -/
theorem upperFunction_continuous {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) : Continuous (upperFunction u) :=
  hu.continuousOn.comp_continuous (continuous_re.prodMk continuous_im) (fun z => z.im_pos)

/-- A constructed smooth Poincaré series belongs to the actual invariant
representatives defining the quotient Hilbert completion. The measure and
normalized orbit density are the existing quotient-model inputs. No density
of these constructed representatives is asserted here. -/
theorem poincare_core_representative (H : Subgroup SL(2,ℤ))
    (μ : Measure ℍ) [IsFiniteMeasureOnCompacts μ]
    (hmp : ∀ g : H, MeasurePreserving (fun z : ℍ => g • z) μ μ)
    (ρ : ℍ → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ z, ∑' g : H, ρ (g • z)=1)
    {u : Point → ℂ} (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hc : HasCompactSupport (upperFunction u)) :
    upperFunction (poincareCartesian H u) ∈ AutomorphicL2.representatives H (μ.withDensity ρ) := by
  let : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  let : Countable SL(2,ℤ) :=
    Function.Injective.countable (f := fun s : SL(2,ℤ) => s.val) Subtype.val_injective
  let : ContinuousConstSMul H ℍ := ⟨fun g =>
    continuous_const_smul (SpecialLinearGroup.mapGL ℝ g.val)⟩
  have he : upperFunction (poincareCartesian H u)=poincareSum (G := H) (upperFunction u) :=
    funext (poincareCartesian_represents H u)
  have hcont := upperFunction_continuous hu
  refine ⟨?_,?_,?_⟩
  · rw [he]
    exact (poincareSum_continuous (G := H) (upperFunction u) hc hcont).measurable
  · intro g z
    exact poincareCartesian_automorphic H u g z
  · rw [he]
    exact poincareSum_memLp μ hmp ρ hρ hn (upperFunction u) hcont hc

#print axioms poincareCartesian_smooth
#print axioms poincare_core_representative
#print axioms cylinderLaplacianPairing_symmetric
#print axioms cylinderLaplacianPairing_nonneg

end QuantitativeMaass
