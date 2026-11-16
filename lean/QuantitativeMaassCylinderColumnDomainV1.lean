module

public import QuantitativeMaassPhysicalRadialSeedV1
public import QuantitativeMaassPhysicalAbelSmoothV1
public import QuantitativeMaassCylinderSquareKernelV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- The actual Abel column is the periodization of a smooth compact
radial seed, even when the Abel profile is only smooth on the physical half-line. -/
theorem cylinderAbelColumn_eq_physicalRadialSeed (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support F ⊆ Iic (Real.cosh R)) (z : ℍ) :
    cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z) =
      poincareSeedVector 0 (physicalRadialSeed (abelProfile F)
        (abelProfile_smoothOn_physical F hF (Real.cosh R) (Real.one_le_cosh R) hs)
        z R hR (abelProfile_support F _ hs)) := by
  apply Subtype.ext
  apply Lp.ext
  exact (cylinderAbelColumn_coeFn F hF R hR hs z).trans
    (physicalRadialSeed_coeFn 0 (abelProfile F) _ z R hR _).symm

/-- Direct domain membership of the literal column. This uses a compact
smooth seed, not an application of a wave packet to a point mass. -/
theorem cylinderAbelColumn_friedrichsGraph (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support F ⊆ Iic (Real.cosh R)) (z : ℍ) :
    FriedrichsGraph 0 (cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z))
      (poincareSeedVector 0 (physicalRadialSeed (abelProfile F)
        (abelProfile_smoothOn_physical F hF (Real.cosh R) (Real.one_le_cosh R) hs)
        z R hR (abelProfile_support F _ hs)).laplacian) := by
  rw [cylinderAbelColumn_eq_physicalRadialSeed]
  exact physicalRadialSeed_friedrichsGraph 0 _ _ z R hR _

/-- Every actual compact time-packet column lies in the quotient
Laplacian domain on the cylinder. The residual formula is a separate assertion. -/
theorem cylinderTimeColumn_mem_friedrichsDomain (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) (z : ℍ) :
    ∃ d : AutomorphicSpace 0,
      FriedrichsGraph 0 (cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z)) d :=
  ⟨_, cylinderAbelColumn_friedrichsGraph (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) he hc) R hR
    (evenCoshLift_support_of_time_support f R hR hs) z⟩

#print axioms cylinderAbelColumn_eq_physicalRadialSeed
#print axioms cylinderAbelColumn_friedrichsGraph
#print axioms cylinderTimeColumn_mem_friedrichsDomain

end QuantitativeMaass
