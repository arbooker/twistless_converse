module

public import QuantitativeMaassGreenCompactSymmetryV1
public import QuantitativeMaassHyperbolicIntegralV1
public import QuantitativeMaassPoincareSmoothExtensionV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem upper_green_symmetric_of_cartesian_compact {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hc : HasCompactSupport u) (hp : ∀ Z∈tsupport u, 0<Z.2) :
    (∫ z : ℍ, star (upperFunction u z)*upperLaplacian v z)=
      ∫ z : ℍ, star (upperLaplacian u z)*upperFunction v z := by
  have hl : Function.support (fun Z => star (u Z)*hyperbolic v Z)⊆
      {Z : Point | 0<Z.2} := by
    intro Z hZ
    apply hp Z
    apply subset_tsupport u
    intro hz
    exact hZ (by simp [hz])
  have hr : Function.support (fun Z => star (hyperbolic u Z)*v Z)⊆
      {Z : Point | 0<Z.2} := by
    intro Z hZ
    apply hp Z
    by_contra hn
    exact hZ (by simp [hyperbolic_zero_of_notMem_tsupport hn])
  change (∫ z : ℍ, upperFunction (fun Z => star (u Z)*hyperbolic v Z) z)=
    ∫ z : ℍ, upperFunction (fun Z => star (hyperbolic u Z)*v Z) z
  rw [integral_upper_cartesian_of_support _ hl,integral_upper_cartesian_of_support _ hr]
  exact green_compact_symmetric hu hv hc hp

/-- The actual ambient hyperbolic Green symmetry. Only the first function
must have compact support on the upper half-plane; neither function needs
an imposed boundary condition at height zero or infinity. -/
theorem upper_green_symmetric {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hc : HasCompactSupport (upperFunction u)) :
    (∫ z : ℍ, star (upperFunction u z)*upperLaplacian v z)=
      ∫ z : ℍ, star (upperLaplacian u z)*upperFunction v z := by
  have h := upper_green_symmetric_of_cartesian_compact
    (upperSeedExtension_contDiff hu hc).contDiffOn hv
    (upperSeedExtension_compact (upperFunction u) hc)
    (fun Z hZ => upperSeedExtension_support_positive (upperFunction u) hc hZ)
  simpa only [upperSeedExtension_represents,upperLaplacian_upperSeedExtension] using h

#print axioms upper_green_symmetric

end QuantitativeMaass
