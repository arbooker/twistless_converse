module

public import QuantitativeArithmeticMaassResidualColumnEnergyV1
public import QuantitativeMaassCylinderColumnLaplacianV1
public import QuantitativeMaassCylinderColumnLinearV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- The residual whose integrated energy was estimated is literally the
Friedrichs residual of the original wave column. -/
theorem cylinderTimeColumn_spectralResidual_graph (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R)
    (z : ℍ) (t : ℝ) :
    FriedrichsGraph 0 (cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z))
      ((((t^2+1/4 : ℝ) : ℂ)) •
        cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z) +
        cylinderAutomorphic (cylinderTimeColumn (spectralResidualSchwartz t f)
          (spectralResidualSchwartz_compact t f hc) (spectralResidualSchwartz_even t f he)
          R hR (spectralTimeResidual_support t f R hs) z)) := by
  have hlin := cylinderTimeColumn_linear (timeSecondDerivative f) f
    (spectralResidualSchwartz t f) (timeSecondDerivative_compact f hc) hc
    (spectralResidualSchwartz_compact t f hc) (timeSecondDerivative_even f he) he
    (spectralResidualSchwartz_even t f he) R hR (timeSecondDerivative_support f R hs) hs
    (spectralTimeResidual_support t f R hs) (-1) (-(t : ℂ)^2)
    (by simp [spectralResidualSchwartz, timeSecondDerivative, sub_eq_add_neg]) z
  rw [hlin]
  have hcast : ((t^2+1/4 : ℝ) : ℂ) = (t : ℂ)^2+1/4 := by push_cast; rfl
  rw [hcast]
  convert cylinderTimeColumn_residual_friedrichsGraph f hc he R hR hs z t using 1
  module

#print axioms cylinderTimeColumn_spectralResidual_graph

end QuantitativeMaass
