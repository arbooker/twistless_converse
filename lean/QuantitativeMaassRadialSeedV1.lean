module

public import QuantitativeMaassRadialLaplacianV1
public import QuantitativeMaassPoincareGraphV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass
open MaassDifferential

/-- The radial profile as an actual Cartesian function. -/
def radialFunction (g : ℝ → ℂ) (w : ℍ) (Z : Point) : ℂ :=
  g (radialCoordinate w.re w.im Z)

theorem radialFunction_upper (g : ℝ → ℂ) (w z : ℍ) :
    upperFunction (radialFunction g w) z=g (Real.cosh (dist z w)) := by
  unfold upperFunction radialFunction
  rw [radialCoordinate_eq_cosh_dist]

theorem radialFunction_smooth (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (w : ℍ) :
    ContDiffOn ℝ ∞ (radialFunction g w) {Z | 0<Z.2} :=
  hg.comp_contDiffOn (radialCoordinate_smooth w.re w.im (ne_of_gt w.im_pos))

/-- Compact radial support gives the exact geometric propagation ball. -/
theorem radialFunction_support (g : ℝ → ℂ) (w : ℍ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) :
    tsupport (upperFunction (radialFunction g w))⊆Metric.closedBall w R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  have hn : g (Real.cosh (dist z w))≠0 := by
    change upperFunction (radialFunction g w) z≠0 at hz
    rwa [radialFunction_upper] at hz
  have hh := Real.cosh_le_cosh.mp (hs hn)
  rw [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] at hh
  exact hh

/-- A genuine smooth compact seed for the quotient Friedrichs construction. -/
def radialSeed (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (w : ℍ)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) : SmoothUpperSeed where
  toFun := radialFunction g w
  smooth := radialFunction_smooth g hg w
  compact := (isCompact_closedBall w R).of_isClosed_subset isClosed_closure
    (radialFunction_support g w R hR hs)

/-- Exact radial differential expression for the positive Laplacian. -/
def radialLaplacianProfile (g : ℝ → ℂ) (q : ℝ) : ℂ :=
  -((q:ℂ)^2-1)*deriv (deriv g) q-2*(q:ℂ)*deriv g q

theorem radialFunction_laplacian (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (w z : ℍ) :
    upperLaplacian (radialFunction g w) z=
      radialLaplacianProfile g (Real.cosh (dist z w)) := by
  change hyperbolic (fun Z => g (radialCoordinate w.re w.im Z)) (z.re,z.im)=_
  rw [hyperbolic_radialCoordinate g hg w.re w.im z.re z.im w.im_pos z.im_pos,
    radialCoordinate_eq_cosh_dist]
  rfl

/-- The kernel column obtained by periodizing a genuine radial seed.
No identification with the spectral wave packet is presumed here. -/
def radialPoincareKernel (N : ℕ) (g : ℝ → ℂ) (w z : ℍ) : ℂ :=
  poincareSum (G := gamma N) (upperFunction (radialFunction g w)) z

theorem radialPoincareKernel_invariant (N : ℕ) (g : ℝ → ℂ) (w z : ℍ) (γ : gamma N) :
    radialPoincareKernel N g w (γ•z)=radialPoincareKernel N g w z :=
  poincareSum_invariant _ γ z

/-- The literal kernel column represents an element of the actual quotient L2. -/
theorem radialPoincareKernel_representative (N : ℕ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (w : ℍ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) :
    radialPoincareKernel N g w∈AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
  poincareSeed_representative N (radialSeed g hg w R hR hs)

/-- The actual hyperbolic Laplacian of the periodized radial column is
its periodized radial differential expression, by local finiteness. -/
theorem radialPoincareKernel_laplacian (N : ℕ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (w : ℍ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) :
    upperLaplacian (congruencePoincareCartesian N (radialFunction g w))=
      radialPoincareKernel N (radialLaplacianProfile g) w := by
  rw [upperLaplacian_congruencePoincareCartesian N
    (radialFunction_smooth g hg w) (radialSeed g hg w R hR hs).compact]
  have he : upperLaplacian (radialFunction g w)=
      upperFunction (radialFunction (radialLaplacianProfile g) w) := by
    funext z
    rw [radialFunction_laplacian g hg,radialFunction_upper]
  rw [he]
  rfl

#print axioms radialFunction_support
#print axioms radialFunction_laplacian
#print axioms radialPoincareKernel_representative
#print axioms radialPoincareKernel_laplacian

end QuantitativeMaass
