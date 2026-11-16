module

public import QuantitativeMaassEnergyPoincareV1
public import QuantitativeMaassGreenUpperEnergyV1
public import QuantitativeMaassPoincareGraphV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Exact global quotient Green energy, including proof of energy
integrability. The normalized measurable orbit density is only used for
unfolding; no derivative of it is taken. -/
theorem poincare_green_energy (N : ℕ) {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hcu : HasCompactSupport (upperFunction u))
    (hcv : HasCompactSupport (upperFunction v)) :
    Integrable (upperEnergy (congruencePoincareCartesian N u)
      (congruencePoincareCartesian N v)) (quotientMeasure N) ∧
    (∫ z, star (poincareSum (G := gamma N) (upperFunction u) z)*
      upperLaplacian (congruencePoincareCartesian N v) z ∂quotientMeasure N)=
      ∫ z, upperEnergy (congruencePoincareCartesian N u)
        (congruencePoincareCartesian N v) z ∂quotientMeasure N := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun g => AsymptoticRationalBranches.action_continuous g.val⟩
  have huP := congruencePoincareCartesian_smooth N hu hcu
  have hinv : ∀ g : gamma N, ∀ z,
      upperFunction (congruencePoincareCartesian N u) (g•z)=
        upperFunction (congruencePoincareCartesian N u) z := by
    intro g z
    simp only [congruencePoincareCartesian_represents,poincareSum_invariant]
  have he := upperEnergy_poincare_right N huP hv hcv hinv
  have hE := integral_poincare_unfold volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (upperEnergy (congruencePoincareCartesian N u) v)
    (upperEnergy_continuous huP hv).measurable (upperEnergy_integrable huP hv hcv)
  change Integrable (poincareSum (G := gamma N)
      (upperEnergy (congruencePoincareCartesian N u) v)) (quotientMeasure N) ∧
    (∫ z, poincareSum (G := gamma N) (upperEnergy (congruencePoincareCartesian N u) v) z
      ∂quotientMeasure N)=∫ z : ℍ, upperEnergy (congruencePoincareCartesian N u) v z at hE
  rw [← he] at hE
  refine ⟨hE.1,?_⟩
  rw [upperLaplacian_congruencePoincareCartesian N hv hcv]
  have hrep := poincareSeed_representative N ⟨u,hu,hcu⟩
  have hp := (integral_poincare_pairing volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (poincareSum (G := gamma N) (upperFunction u)) hrep.1 hrep.2.1 hrep.2.2
    (upperLaplacian v) (upperLaplacian_continuous hv) (upperLaplacian_compact v hcv)).2.2
  have hg := upper_green_energy_right huP hv hcv
  simp only [congruencePoincareCartesian_represents] at hg
  exact hp.trans (hg.trans hE.2.symm)

/-- Nonnegative energy for the literal quotient Laplacian on every smooth
compact Poincaré vector, with all quotient energy integrability proved. -/
theorem poincareSeedVector_laplacian_nonneg (N : ℕ) (u : SmoothUpperSeed) :
    0≤(inner ℂ (poincareSeedVector N u) (poincareSeedVector N u.laplacian)).re := by
  rw [poincareSeedVector_inner]
  have h := poincare_green_energy N u.smooth u.smooth u.compact u.compact
  rw [upperLaplacian_congruencePoincareCartesian N u.smooth u.compact] at h
  change 0≤(∫ z, star (poincareSum (G := gamma N) (upperFunction u.toFun) z)*
    poincareSum (G := gamma N) (upperLaplacian u.toFun) z ∂quotientMeasure N).re
  rw [h.2]
  change 0≤RCLike.re (∫ z, upperEnergy (congruencePoincareCartesian N u.toFun)
    (congruencePoincareCartesian N u.toFun) z ∂quotientMeasure N)
  rw [← integral_re h.1]
  apply integral_nonneg
  intro z
  exact hyperbolicEnergy_self_nonneg _ (z.re,z.im)

#print axioms poincare_green_energy
#print axioms poincareSeedVector_laplacian_nonneg

end QuantitativeMaass
