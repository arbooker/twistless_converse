module

public import QuantitativeMaassRadialSeedV1
public import QuantitativeMaassFriedrichsGraphV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Only the physical half-line is sampled by the radial coordinate,
including at the centre of the kernel. -/
theorem radialCoordinate_mem_physical (w : ℍ) {Z : Point} (hZ : 0 < Z.2) :
    radialCoordinate w.re w.im Z ∈ Ici (1 : ℝ) := by
  change 1 ≤ ((Z.1-w.re)^2+Z.2^2+w.im^2)/(2*w.im*Z.2)
  apply (le_div_iff₀ (by positivity : 0 < 2*w.im*Z.2)).mpr
  nlinarith [sq_nonneg (Z.1-w.re), sq_nonneg (Z.2-w.im)]

/-- One-sided smoothness at the physical endpoint suffices for a smooth
function on the entire upper half-plane. -/
theorem radialFunction_smoothOn_physical (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (w : ℍ) :
    ContDiffOn ℝ ∞ (radialFunction g w) {Z | 0 < Z.2} :=
  hg.comp (radialCoordinate_smooth w.re w.im (ne_of_gt w.im_pos))
    (fun _ hZ => radialCoordinate_mem_physical w hZ)

/-- A compact radial seed built directly from its one-sided profile.
No extension of that profile below one is required. -/
def physicalRadialSeed (g : ℝ → ℂ) (hg : ContDiffOn ℝ ∞ g (Ici 1))
    (w : ℍ) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support g ⊆ Iic (Real.cosh R)) : SmoothUpperSeed where
  toFun := radialFunction g w
  smooth := radialFunction_smoothOn_physical g hg w
  compact := (isCompact_closedBall w R).of_isClosed_subset isClosed_closure
    (radialFunction_support g w R hR hs)

theorem physicalRadialSeed_coeFn (N : ℕ) (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (w : ℍ) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support g ⊆ Iic (Real.cosh R)) :
    (poincareSeedVector N (physicalRadialSeed g hg w R hR hs)).val
      =ᵐ[quotientMeasure N] radialPoincareKernel N g w :=
  poincareSeedVector_coeFn N (physicalRadialSeed g hg w R hR hs)

/-- The literal periodized physical radial seed lies in the graph of
the actual quotient Friedrichs Laplacian, also for the translation cylinder. -/
theorem physicalRadialSeed_friedrichsGraph (N : ℕ) (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (w : ℍ) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support g ⊆ Iic (Real.cosh R)) :
    FriedrichsGraph N (poincareSeedVector N (physicalRadialSeed g hg w R hR hs))
      (poincareSeedVector N (physicalRadialSeed g hg w R hR hs).laplacian) :=
  friedrichsGraph_poincareSeed N _

#print axioms radialCoordinate_mem_physical
#print axioms radialFunction_smoothOn_physical
#print axioms physicalRadialSeed_coeFn
#print axioms physicalRadialSeed_friedrichsGraph

end QuantitativeMaass
