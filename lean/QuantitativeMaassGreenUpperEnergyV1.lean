module

public import QuantitativeMaassEnergySupportV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem upper_green_energy_right_of_cartesian_compact {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hc : HasCompactSupport v) (hp : ∀ Z∈tsupport v, 0<Z.2) :
    (∫ z : ℍ, star (upperFunction u z)*upperLaplacian v z)=
      ∫ z : ℍ, upperEnergy u v z := by
  have hn (Z : Point) (hZ : ¬0<Z.2) : Z∉tsupport v := fun h => hZ (hp Z h)
  have hz (Z : Point) (hZ : ¬0<Z.2) : X v Z=0 ∧ Y v Z=0 := by
    have hd := fderiv_of_notMem_tsupport ℝ (hn Z hZ)
    simp [X,Y,dir,D,hd]
  have hl : Function.support (fun Z => star (u Z)*hyperbolic v Z)⊆
      {Z : Point | 0<Z.2} := by
    intro Z hZ
    by_contra hpos
    exact hZ (by simp [hyperbolic_zero_of_notMem_tsupport (hn Z hpos)])
  have he : Function.support (hyperbolicEnergy u v)⊆{Z : Point | 0<Z.2} := by
    intro Z hZ
    by_contra hpos
    exact hZ (by simp [hyperbolicEnergy,(hz Z hpos).1,(hz Z hpos).2])
  change (∫ z : ℍ, upperFunction (fun Z => star (u Z)*hyperbolic v Z) z)=
    ∫ z : ℍ, upperFunction (hyperbolicEnergy u v) z
  rw [integral_upper_cartesian_of_support _ hl,integral_upper_cartesian_of_support _ he,
    green_compact_right hu hv hc hp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun Z => by
    by_cases hZ : 0<Z.2
    · unfold hyperbolicEnergy
      have hnZ : (Z.2:ℂ)≠0 := by exact_mod_cast hZ.ne'
      field_simp
    · simp [hyperbolicEnergy,(hz Z hZ).1,(hz Z hZ).2]

/-- Ambient Green energy with a compact second test. This is the form
needed for quotient unfolding, with no derivative of the quotient density. -/
theorem upper_green_energy_right {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hc : HasCompactSupport (upperFunction v)) :
    (∫ z : ℍ, star (upperFunction u z)*upperLaplacian v z)=
      ∫ z : ℍ, upperEnergy u v z := by
  have h := upper_green_energy_right_of_cartesian_compact hu
    (upperSeedExtension_contDiff hv hc).contDiffOn
    (upperSeedExtension_compact (upperFunction v) hc)
    (fun Z hZ => upperSeedExtension_support_positive (upperFunction v) hc hZ)
  rw [upperLaplacian_upperSeedExtension,
    upperEnergy_eqOn_right (upperSeedExtension_eqOn v)] at h
  exact h

#print axioms upper_green_energy_right

end QuantitativeMaass
