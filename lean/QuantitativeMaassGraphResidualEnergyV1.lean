module

public import QuantitativeMaassCrossGraphFluxV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeArithmeticMaassWave
open scoped InnerProductSpace

namespace QuantitativeMaass

/-- Exact form norm of a graph vector with a real spectral centre and
an actual residual. -/
theorem graphEnergyLift_residual_norm_sq (N : ℕ) (μ : ℝ)
    (g d : AutomorphicSpace N) (hg : FriedrichsGraph N g ((μ : ℂ) • g + d)) :
    ‖graphEnergyLift N g ((μ : ℂ) • g + d)‖^2 =
      (1+μ)*‖g‖^2 + (inner ℂ g d).re := by
  let v := graphEnergyLift N g ((μ : ℂ) • g + d)
  have h := quotientClosedEnergy_norm N v
  rw [graphEnergyLift_value N hg, graphEnergyLift_form N hg,
    graphEnergyLift_value N hg] at h
  rw [inner_add_right, _root_.inner_smul_right (𝕜 := ℂ) g g (μ : ℂ),
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at h
  have hself : (inner ℂ g g).re = ‖g‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) g
  rw [hself] at h
  change ‖g‖^2 + (μ*‖g‖^2 + (inner ℂ g d).re) = ‖v‖^2 at h
  change ‖v‖^2 = _
  nlinarith only [h]

/-- A first-order source energy bound uses only the source and its residual
in L2, with an explicit spectral factor. -/
theorem graphEnergyLift_residual_norm_sq_le (N : ℕ) (μ : ℝ) (hμ : 0 ≤ μ)
    (g d : AutomorphicSpace N) (hg : FriedrichsGraph N g ((μ : ℂ) • g + d)) :
    ‖graphEnergyLift N g ((μ : ℂ) • g + d)‖^2 ≤
      2*(1+μ)*‖g‖^2 + ‖d‖^2 := by
  rw [graphEnergyLift_residual_norm_sq N μ g d hg]
  have hinner : (inner ℂ g d).re ≤ ‖g‖*‖d‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm g d)
  nlinarith [sq_nonneg (‖g‖-‖d‖), mul_nonneg hμ (sq_nonneg ‖g‖)]

#print axioms graphEnergyLift_residual_norm_sq
#print axioms graphEnergyLift_residual_norm_sq_le

end QuantitativeMaass
