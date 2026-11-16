module

public import QuantitativeMaassPhysicalTimeLaplacianV1
public import QuantitativeMaassCylinderColumnDomainV1
public import QuantitativeMaassPoincareGraphLinearV1
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- The second time derivative as an actual Schwartz function. -/
def timeSecondDerivative (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)

theorem timeSecondDerivative_coe (f : SchwartzMap ℝ ℂ) :
    (timeSecondDerivative f : ℝ → ℂ) = deriv (deriv (f : ℝ → ℂ)) := rfl

theorem timeSecondDerivative_compact (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) :
    HasCompactSupport (timeSecondDerivative f : ℝ → ℂ) := by
  rw [timeSecondDerivative_coe]
  exact hc.deriv.deriv

theorem timeSecondDerivative_even (f : SchwartzMap ℝ ℂ) (he : Function.Even f) :
    Function.Even (timeSecondDerivative f) := by
  rw [timeSecondDerivative_coe]
  exact even_time_second_deriv_even f he

/-- Differentiation preserves the original closed time-support interval. -/
theorem timeSecondDerivative_support (f : SchwartzMap ℝ ℂ) (R : ℝ)
    (hs : Function.support f ⊆ Icc (-R) R) :
    Function.support (timeSecondDerivative f) ⊆ Icc (-R) R := by
  rw [timeSecondDerivative_coe]
  exact support_deriv_subset.trans
    (tsupport_deriv_subset.trans (closure_minimal hs isClosed_Icc))

/-- The literal cylinder time column has the exact Friedrichs-Laplacian
image given by the original second time derivative, with no larger support. -/
theorem cylinderTimeColumn_friedrichsGraph (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) (z : ℍ) :
    FriedrichsGraph 0 (cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z))
      ((1/4 : ℂ) • cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z) -
        cylinderAutomorphic (cylinderTimeColumn (timeSecondDerivative f)
          (timeSecondDerivative_compact f hc) (timeSecondDerivative_even f he)
          R hR (timeSecondDerivative_support f R hs) z)) := by
  let F := evenCoshLift f
  let G := evenCoshLift (timeSecondDerivative f)
  have hF : ContDiffOn ℝ ∞ F (Ici 1) := evenCoshLift_smoothOn f (f.smooth ⊤) he hc
  have hG : ContDiffOn ℝ ∞ G (Ici 1) :=
    evenCoshLift_smoothOn (timeSecondDerivative f) ((timeSecondDerivative f).smooth ⊤)
      (timeSecondDerivative_even f he) (timeSecondDerivative_compact f hc)
  have hsF : Function.support F ⊆ Iic (Real.cosh R) :=
    evenCoshLift_support_of_time_support f R hR hs
  have hsG : Function.support G ⊆ Iic (Real.cosh R) :=
    evenCoshLift_support_of_time_support (timeSecondDerivative f) R hR
      (timeSecondDerivative_support f R hs)
  let u := physicalRadialSeed (abelProfile F)
    (abelProfile_smoothOn_physical F hF (Real.cosh R) (Real.one_le_cosh R) hsF)
    z R hR (abelProfile_support F _ hsF)
  let v := physicalRadialSeed (abelProfile G)
    (abelProfile_smoothOn_physical G hG (Real.cosh R) (Real.one_le_cosh R) hsG)
    z R hR (abelProfile_support G _ hsG)
  have hu : cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z) =
      poincareSeedVector 0 u :=
    cylinderAbelColumn_eq_physicalRadialSeed F hF R hR hsF z
  have hv : cylinderAutomorphic (cylinderTimeColumn (timeSecondDerivative f)
      (timeSecondDerivative_compact f hc) (timeSecondDerivative_even f he)
      R hR (timeSecondDerivative_support f R hs) z) = poincareSeedVector 0 v :=
    cylinderAbelColumn_eq_physicalRadialSeed G hG R hR hsG z
  have hlap : poincareSeedVector 0 u.laplacian =
      (1/4 : ℂ) • poincareSeedVector 0 u - poincareSeedVector 0 v := by
    calc
      poincareSeedVector 0 u.laplacian =
          poincareSeedVector 0 ((u.smul (1/4)).add (v.smul (-1))) := by
        apply poincareSeedVector_congr
        funext w
        change upperLaplacian (radialFunction (abelProfile F) z) w =
          (1/4 : ℂ) * upperFunction (radialFunction (abelProfile F) z) w +
            (-1 : ℂ) * upperFunction (radialFunction (abelProfile G) z) w
        rw [radialFunction_upper, radialFunction_upper]
        simpa only [F, G, timeSecondDerivative_coe, neg_one_mul, sub_eq_add_neg] using
          physicalTimeRadial_laplacian f (f.smooth ⊤) he hc R hR hs z w
      _ = (1/4 : ℂ) • poincareSeedVector 0 u - poincareSeedVector 0 v := by
        rw [poincareSeedVector_add, poincareSeedVector_smul, poincareSeedVector_smul]
        module
  rw [hu, hv, ← hlap]
  exact friedrichsGraph_poincareSeed 0 u

/-- The same graph identity centered at the spectral value t²+1/4.
The bracket is an actual difference of cylinder columns. -/
theorem cylinderTimeColumn_residual_friedrichsGraph (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R)
    (z : ℍ) (t : ℝ) :
    FriedrichsGraph 0 (cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z))
      ((((t : ℂ)^2 + 1/4) : ℂ) •
          cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z) +
        (-cylinderAutomorphic (cylinderTimeColumn (timeSecondDerivative f)
          (timeSecondDerivative_compact f hc) (timeSecondDerivative_even f he)
          R hR (timeSecondDerivative_support f R hs) z) -
          (t : ℂ)^2 • cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z))) := by
  convert cylinderTimeColumn_friedrichsGraph f hc he R hR hs z using 1
  module

#print axioms timeSecondDerivative_support
#print axioms cylinderTimeColumn_friedrichsGraph
#print axioms cylinderTimeColumn_residual_friedrichsGraph

end QuantitativeMaass
