module

public import QuantitativeMaassRealLinearLowerV1
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- Numerator of z minus its fractional-linear image. -/
def realMatrixDisplacementNumerator (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) : ℂ :=
  (M 1 0:ℂ)*z^2+((M 1 1:ℂ)-M 0 0)*z-M 0 1

/-- Inserting one real translation makes the displacement numerator affine
in its averaging parameter, with an explicit rank-one factorization. -/
theorem averaging_displacement_numerator (G H : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) (z : ℂ) :
    realMatrixDisplacementNumerator (G*!![1,u;0,1]*H) z=
      realMatrixDisplacementNumerator (G*H) z+
        (u:ℂ)*(((H 1 0:ℂ)*z+H 1 1)*((G 1 0:ℂ)*z-G 0 0)) := by
  simp only [realMatrixDisplacementNumerator,Matrix.mul_apply,Fin.sum_univ_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    mul_one,mul_zero,add_zero]
  push_cast
  ring

/-- Bounded determinant-one partial products give the required uniform
polynomial lower bound for the averaging slope on a retained rectangle. -/
theorem averaging_displacement_slope_lower (G H : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G.det=1) (hH : H.det=1) (B : ℝ) (hB : 0<B)
    (hGb : ∀ i j,|G i j|≤B) (hHb : ∀ i j,|H i j|≤B)
    (z : ℂ) (X Y : ℝ) (hX : 0≤X) (hY : 0<Y) (hx : |z.re|≤X) (hy : Y≤z.im) :
    (1/(B*(1+(X+1)/Y)))^2≤
      ‖((H 1 0:ℂ)*z+H 1 1)*((G 1 0:ℂ)*z-G 0 0)‖ := by
  have hgd : G 1 0*(-G 0 1)-(-G 0 0)*G 1 1=1 := by
    rw [Matrix.det_fin_two] at hG
    nlinarith
  have hhd : H 1 0*(-H 0 1)-H 1 1*(-H 0 0)=1 := by
    rw [Matrix.det_fin_two] at hH
    nlinarith
  have hg := real_linear_form_lower_of_det (G 1 0) (-G 0 0) (G 1 1) (-G 0 1) hgd
    B hB (hGb 1 1) (by simpa only [abs_neg] using hGb 0 1) z X Y hX hY hx hy
  have hh := real_linear_form_lower_of_det (H 1 0) (H 1 1) (-H 0 0) (-H 0 1) hhd
    B hB (by simpa only [abs_neg] using hHb 0 0) (by simpa only [abs_neg] using hHb 0 1)
    z X Y hX hY hx hy
  have hg' : 1/(B*(1+(X+1)/Y))≤‖(G 1 0:ℂ)*z-G 0 0‖ := by
    simpa only [Complex.ofReal_neg,sub_eq_add_neg] using hg
  rw [norm_mul,pow_two]
  exact mul_le_mul hh hg' (by positivity) (norm_nonneg _)

/-- A word containing a horizontal average has a linear parameter
sublevel bound, including when all other parameters have been fixed. -/
theorem averaging_numerator_parameter_sublevel (G H : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G.det=1) (hH : H.det=1) (B : ℝ) (hB : 0<B)
    (hGb : ∀ i j,|G i j|≤B) (hHb : ∀ i j,|H i j|≤B)
    (z : ℂ) (X Y : ℝ) (hX : 0≤X) (hY : 0<Y) (hx : |z.re|≤X) (hy : Y≤z.im)
    (r : ℝ) (hr : 0<r) :
    volume {u : ℝ | ‖realMatrixDisplacementNumerator (G*!![1,u;0,1]*H) z‖<r}≤
      ENNReal.ofReal (4*r/((1/(B*(1+(X+1)/Y)))^2)) := by
  simp_rw [averaging_displacement_numerator]
  have hh := complex_affine_parameter_sublevel
    (((H 1 0:ℂ)*z+H 1 1)*((G 1 0:ℂ)*z-G 0 0))
    (realMatrixDisplacementNumerator (G*H) z) ((1/(B*(1+(X+1)/Y)))^2) r (by positivity)
    (averaging_displacement_slope_lower G H hG hH B hB hGb hHb z X Y hX hY hx hy) hr
  simpa only [add_comm] using hh

#print axioms averaging_displacement_numerator
#print axioms averaging_displacement_slope_lower
#print axioms averaging_numerator_parameter_sublevel

end QuantitativeMaass
