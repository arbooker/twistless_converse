module

public import QuantitativeMaassPoincareEnergyIdentityV1
public import QuantitativeMaassPoincareLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Unfold only the compact test in the energy pairing. The test need
not be invariant under the congruence group. -/
theorem poincareSeedVector_laplacian_unfold_energy (N : ℕ) (u v : SmoothUpperSeed) :
    inner ℂ (poincareSeedVector N u.laplacian) (poincareSeedVector N v) =
      ∫ z, upperEnergy (congruencePoincareCartesian N u.toFun) v.toFun z := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun g => AsymptoticRationalBranches.action_continuous g.val⟩
  rw [poincareSeedVector_laplacian_symmetric, poincareSeedVector_inner]
  have hrep := poincareSeed_representative N u
  have hp := (integral_poincare_pairing volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (poincareSum (G := gamma N) (upperFunction u.toFun)) hrep.1 hrep.2.1 hrep.2.2
    (upperLaplacian v.toFun) (upperLaplacian_continuous v.smooth)
    (upperLaplacian_compact v.toFun v.compact)).2.2
  have hg := upper_green_energy_right
    (congruencePoincareCartesian_smooth N u.smooth u.compact) v.smooth v.compact
  simp only [congruencePoincareCartesian_represents] at hg
  exact hp.trans hg

/-- The corresponding identity with a compact first test. -/
theorem poincareSeedVector_unfold_laplacian_energy (N : ℕ) (u v : SmoothUpperSeed) :
    inner ℂ (poincareSeedVector N u) (poincareSeedVector N v.laplacian) =
      ∫ z, upperEnergy u.toFun (congruencePoincareCartesian N v.toFun) z := by
  rw [← inner_conj_symm (𝕜 := ℂ) (poincareSeedVector N u)
    (poincareSeedVector N v.laplacian), poincareSeedVector_laplacian_unfold_energy]
  rw [← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  simp [upperEnergy, upperFunction, hyperbolicEnergy, mul_comm]

/-- Cross-quotient Green identity on compact smooth tests. In particular
one of the levels can be the translation cylinder (level zero). The
compact cutoff is not required to be invariant under either group. -/
theorem cross_poincare_localization_energy (N M : ℕ) (u v b : SmoothUpperSeed) :
    let F := congruencePoincareCartesian N u.toFun
    let G := congruencePoincareCartesian M v.toFun
    let bG := b.localized G (congruencePoincareCartesian_smooth M v.smooth v.compact)
    let bF := b.localized F (congruencePoincareCartesian_smooth N u.smooth u.compact)
    inner ℂ (poincareSeedVector N u.laplacian) (poincareSeedVector N bG) -
      inner ℂ (poincareSeedVector M bF) (poincareSeedVector M v.laplacian) =
        (∫ z, upperEnergy F bG.toFun z) - ∫ z, upperEnergy bF.toFun G z := by
  intro F G bG bF
  rw [poincareSeedVector_laplacian_unfold_energy,
    poincareSeedVector_unfold_laplacian_energy]

#print axioms poincareSeedVector_laplacian_unfold_energy
#print axioms poincareSeedVector_unfold_laplacian_energy
#print axioms cross_poincare_localization_energy

end QuantitativeMaass
