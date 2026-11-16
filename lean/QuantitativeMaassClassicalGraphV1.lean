module

public import QuantitativeMaassWeakGraphV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Exact unfolding against an arbitrary actual invariant L2 representative. -/
theorem poincareSeed_pairing_representative (N : ℕ) (u : SmoothUpperSeed)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    inner ℂ (poincareSeedVector N u) (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)=
      ∫ z : ℍ,star (upperFunction u.toFun z)*f.val z := by
  have he : inner ℂ (poincareSeedVector N u)
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)=
      ∫ z,star (poincareSum (G:=gamma N) (upperFunction u.toFun) z)*f.val z ∂quotientMeasure N := by
    change inner ℂ (poincareSeedVector N u).val (f.property.2.2.toLp f.val)=_
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [poincareSeedVector_coeFn N u,f.property.2.2.coeFn_toLp] with z hu hf
    rw [hu,hf]
    simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]
  rw [he]
  exact congruence_poincare_pairing_left N f.val f.property.1 f.property.2.1 f.property.2.2
    (upperFunction u.toFun) (upperFunction_continuous u.smooth) u.compact

/-- A smooth classical eigenfunction that is actually invariant and square
integrable lies in the full self-adjoint Laplace graph. Smooth compact tests,
Green's formula and the proved radial approximate identity establish the
operator-domain assertion; it is not an extra assumption on the input. -/
theorem classical_eigenfunction_friedrichsGraph (N : ℕ) [NeZero N]
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (u : ℝ×ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hrep : ∀ z : ℍ,upperFunction u z=f.val z) (e : ℂ)
    (heigen : ∀ z : ℍ,upperLaplacian u z=e*upperFunction u z) :
    FriedrichsGraph N (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)
      (e • AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) := by
  apply friedrichsGraph_of_seed_pairings
  intro v
  rw [inner_smul_right (𝕜:=ℂ) (poincareSeedVector N v)
    (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) e,
    poincareSeed_pairing_representative,poincareSeed_pairing_representative]
  simp_rw [←hrep]
  change (∫ z : ℍ,star (upperLaplacian v.toFun z)*upperFunction u z)=_
  rw [←upper_green_symmetric v.smooth hu v.compact]
  simp_rw [heigen,mul_left_comm (star (upperFunction v.toFun _)) e]
  exact integral_const_mul e _

#print axioms poincareSeed_pairing_representative
#print axioms classical_eigenfunction_friedrichsGraph

end QuantitativeMaass
