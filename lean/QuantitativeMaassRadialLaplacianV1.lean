module

public import QuantitativeMaassRadialCoordinateV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- A real inner coordinate and complex outer profile, differentiated twice.
Only local derivative data for the coordinate are required. -/
theorem radial_second_comp (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (r r₁ : ℝ → ℝ) (r₂ x : ℝ)
    (hr : ∀ᶠ u in 𝓝 x, HasDerivAt r (r₁ u) u) (hr₁ : HasDerivAt r₁ r₂ x) :
    deriv (deriv (fun u => g (r u))) x=
      (r₁ x:ℂ)^2*deriv (deriv g) (r x)+(r₂:ℂ)*deriv g (r x) := by
  have hg₁ : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have he : deriv (fun u => g (r u))=ᶠ[𝓝 x]
      fun u => (r₁ u:ℂ)*deriv g (r u) := by
    filter_upwards [hr] with u hu
    simpa only [Function.comp_def,Complex.real_smul] using
      (((hg.differentiable (by simp)) (r u)).hasDerivAt.scomp u hu).deriv
  have hd := hr₁.ofReal_comp.mul
    (((hg₁.differentiable (by simp)) (r x)).hasDerivAt.scomp x hr.self_of_nhds)
  simp only [Function.comp_def,Pi.mul_def,Complex.real_smul] at hd
  rw [he.deriv_eq,hd.deriv]
  ring

/-- Exact radial form of the ACTUAL Cartesian hyperbolic Laplacian.
The coordinate is cosh distance, including the centre where distance itself
is not a smooth coordinate. The sign agrees with the positive Laplacian used
by the quotient Friedrichs operator. -/
theorem hyperbolic_radialCoordinate (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (a b x y : ℝ) (hb : 0<b) (hy : 0<y) :
    hyperbolic (fun Z => g (radialCoordinate a b Z)) (x,y)=
      -((radialCoordinate a b (x,y):ℂ)^2-1)*deriv (deriv g) (radialCoordinate a b (x,y))
      -2*(radialCoordinate a b (x,y):ℂ)*deriv g (radialCoordinate a b (x,y)) := by
  have hx := radial_second_comp g hg (fun u => radialCoordinate a b (u,y))
    (fun u => radialCoordinateX a b u y) (1/(b*y)) x
    (Eventually.of_forall (fun u => radialCoordinate_hasDerivAt_x a b u y (ne_of_gt hb) (ne_of_gt hy)))
    (radialCoordinateX_hasDerivAt_x a b x y)
  have hyr : ∀ᶠ u in 𝓝 y, HasDerivAt (fun v => radialCoordinate a b (x,v))
      (radialCoordinateY a b x u) u := by
    filter_upwards [Ioi_mem_nhds hy] with u hu
    exact radialCoordinate_hasDerivAt_y a b x u (ne_of_gt hb) (ne_of_gt hu)
  have hy' := radial_second_comp g hg (fun u => radialCoordinate a b (x,u))
    (fun u => radialCoordinateY a b x u) (((x-a)^2+b^2)/(b*y^3)) y hyr
    (radialCoordinateY_hasDerivAt_y a b x y (ne_of_gt hb) (ne_of_gt hy))
  have hgrad := congrArg (fun v : ℝ => (v:ℂ))
    (radialCoordinate_gradient a b x y (ne_of_gt hb) (ne_of_gt hy))
  have htrace := congrArg (fun v : ℝ => (v:ℂ))
    (radialCoordinate_trace a b x y (ne_of_gt hb) (ne_of_gt hy))
  push_cast at hgrad htrace
  simp only [hyperbolic,euclidean,hx,hy',Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_pow]
  push_cast
  linear_combination
    -(deriv (deriv g) (radialCoordinate a b (x,y))) * hgrad -
      (deriv g (radialCoordinate a b (x,y))) * htrace

#print axioms radial_second_comp
#print axioms hyperbolic_radialCoordinate

end QuantitativeMaass
