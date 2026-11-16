module

public import MaassFrickeCovarianceV1
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Smooth Cartesian coordinate equal to cosh of hyperbolic distance.
Unlike distance itself, this is smooth also at the centre. -/
def radialCoordinate (a b : ℝ) (Z : Point) : ℝ :=
  ((Z.1-a)^2+Z.2^2+b^2)/(2*b*Z.2)

def radialCoordinateX (a b x y : ℝ) : ℝ := (x-a)/(b*y)
def radialCoordinateY (a b x y : ℝ) : ℝ :=
  1/(2*b)-((x-a)^2+b^2)/(2*b*y^2)

theorem radialCoordinate_eq_cosh_dist (z w : ℍ) :
    radialCoordinate w.re w.im (z.re,z.im)=Real.cosh (dist z w) := by
  rw [UpperHalfPlane.cosh_dist']
  unfold radialCoordinate
  congr 1
  ring

theorem radialCoordinate_smooth (a b : ℝ) (hb : b≠0) :
    ContDiffOn ℝ ∞ (radialCoordinate a b) {Z | 0<Z.2} := by
  apply ContDiffOn.div
  · fun_prop
  · fun_prop
  · intro Z hZ
    exact mul_ne_zero (mul_ne_zero (by norm_num) hb) (ne_of_gt hZ)

theorem radialCoordinate_hasDerivAt_x (a b x y : ℝ) (hb : b≠0) (hy : y≠0) :
    HasDerivAt (fun u => radialCoordinate a b (u,y)) (radialCoordinateX a b x y) x := by
  have h := (((((hasDerivAt_id x).sub_const a).pow 2).add_const (y^2)).add_const (b^2)).div_const (2*b*y)
  convert h using 1
  · rfl
  · simp only [radialCoordinateX,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    field_simp

theorem radialCoordinate_hasDerivAt_y (a b x y : ℝ) (hb : b≠0) (hy : y≠0) :
    HasDerivAt (fun u => radialCoordinate a b (x,u)) (radialCoordinateY a b x y) y := by
  have h := ((((hasDerivAt_id y).pow 2).const_add ((x-a)^2)).add_const (b^2)).div
    ((hasDerivAt_id y).const_mul (2*b)) (mul_ne_zero (mul_ne_zero (by norm_num) hb) hy)
  convert h using 1
  · rfl
  · simp only [radialCoordinateY,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,Pi.pow_apply]
    field_simp
    ring

theorem radialCoordinateX_hasDerivAt_x (a b x y : ℝ) :
    HasDerivAt (fun u => radialCoordinateX a b u y) (1/(b*y)) x := by
  convert ((hasDerivAt_id x).sub_const a).div_const (b*y) using 1
  rfl

theorem radialCoordinateY_hasDerivAt_y (a b x y : ℝ) (hb : b≠0) (hy : y≠0) :
    HasDerivAt (fun u => radialCoordinateY a b x u)
      (((x-a)^2+b^2)/(b*y^3)) y := by
  have h := (hasDerivAt_const y (1/(2*b))).sub
    ((hasDerivAt_const y ((x-a)^2+b^2)).div
      (((hasDerivAt_id y).pow 2).const_mul (2*b))
      (mul_ne_zero (mul_ne_zero (by norm_num) hb) (pow_ne_zero 2 hy)))
  convert h using 1
  · rfl
  · simp only [id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,Pi.pow_apply]
    field_simp
    ring

/-- Squared hyperbolic gradient of the actual radial coordinate. -/
theorem radialCoordinate_gradient (a b x y : ℝ) (hb : b≠0) (hy : y≠0) :
    y^2*(radialCoordinateX a b x y^2+radialCoordinateY a b x y^2)=
      radialCoordinate a b (x,y)^2-1 := by
  unfold radialCoordinate radialCoordinateX radialCoordinateY
  field_simp
  ring

/-- The positive-sign radial Laplacian coefficient in dimension two. -/
theorem radialCoordinate_trace (a b x y : ℝ) (hb : b≠0) (hy : y≠0) :
    y^2*(1/(b*y)+((x-a)^2+b^2)/(b*y^3))=2*radialCoordinate a b (x,y) := by
  unfold radialCoordinate
  field_simp
  ring

#print axioms radialCoordinate_eq_cosh_dist
#print axioms radialCoordinate_smooth
#print axioms radialCoordinate_hasDerivAt_x
#print axioms radialCoordinate_hasDerivAt_y
#print axioms radialCoordinateY_hasDerivAt_y
#print axioms radialCoordinate_gradient
#print axioms radialCoordinate_trace

end QuantitativeMaass
