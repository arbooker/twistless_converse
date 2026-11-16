module

public import QuantitativeMaassClassicalGraphV1
public import QuantitativeMaassEulerLevelOneCuspidalV1
public import QuantitativeMaassEulerWaveEquationV1
public import QuantitativeMaassEulerSmoothV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- The literal original level-one solution is an eigenvector of the actual
Friedrichs Laplacian at energy 1/4+r^2. All modularity, integrability and
operator-domain hypotheses have been discharged from original Euler data. -/
theorem principalEulerLevelOneClass_graph {b : ℕ → ℂ} (r : ℝ) (σ : ℕ)
    (hb : MaassOriginal.IsEulerSolution 1 (.principal r) σ b) :
    FriedrichsGraph 1 (principalEulerLevelOneClass r σ hb)
      (((1/4+r^2:ℝ):ℂ) • principalEulerLevelOneClass r σ hb) := by
  apply classical_eigenfunction_friedrichsGraph 1 (principalEulerLevelOneRepresentative r σ hb)
    (principalEulerWave b r σ) (principalEulerWave_contDiffOn hb.polynomialGrowth r σ) (fun _ => rfl)
  intro z
  exact principalEulerWave_hyperbolic hb.polynomialGrowth r σ z.re z.im z.im_pos

#print axioms principalEulerLevelOneClass_graph

end QuantitativeMaass
