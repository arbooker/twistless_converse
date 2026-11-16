module

public import QuantitativeMaassAveragingDisplacementV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticMobiusFold
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- One averaging translation increases a two-by-two entry bound by an
explicit quadratic factor, uniformly over the entire averaging period. -/
theorem averaging_product_entry_bound (G H : Matrix (Fin 2) (Fin 2) ℝ)
    (B : ℝ) (hB : 0≤B) (hG : ∀ i j,|G i j|≤B) (hH : ∀ i j,|H i j|≤B)
    (u : ℝ) (hu : |u|≤1) (i j : Fin 2) : |(G*!![1,u;0,1]*H) i j|≤3*B^2 := by
  have hp : |G i 0*u+G i 1|≤2*B := by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    have hh := mul_le_mul (hG i 0) hu (abs_nonneg u) hB
    nlinarith [hG i 1]
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,mul_one,mul_zero,add_zero]
  calc
    _≤|G i 0*H 0 j|+|(G i 0*u+G i 1)*H 1 j| := abs_add_le _ _
    _=|G i 0| *|H 0 j|+|G i 0*u+G i 1| *|H 1 j| := by rw [abs_mul,abs_mul]
    _≤B*B+(2*B)*B := add_le_add
      (mul_le_mul (hG i 0) (hH 0 j) (abs_nonneg _) hB)
      (mul_le_mul hp (hH 1 j) (abs_nonneg _) (by positivity))
    _=_ := by ring

/-- The denominator in the actual averaging action has a fully explicit
bound in terms of the partial matrices and the retained point. -/
theorem averaging_denominator_bound (G H : GL (Fin 2) ℝ)
    (B : ℝ) (hB : 0≤B) (hG : ∀ i j,|G.val i j|≤B) (hH : ∀ i j,|H.val i j|≤B)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) (z : ℍ) :
    ‖denom (G*translation u*H) z‖≤3*B^2*(‖(z:ℂ)‖+1) := by
  have hab : |u|≤1 := by rw [abs_of_nonneg hu.1];exact hu.2
  have he (i j : Fin 2) : |(G.val*!![1,u;0,1]*H.val) i j|≤3*B^2 :=
    averaging_product_entry_bound G.val H.val B hB hG hH u hab i j
  change ‖(((G.val*!![1,u;0,1]*H.val) 1 0:ℝ):ℂ)*(z:ℂ)+
    ((G.val*!![1,u;0,1]*H.val) 1 1:ℂ)‖≤_
  calc
    _≤‖(((G.val*!![1,u;0,1]*H.val) 1 0:ℝ):ℂ)*(z:ℂ)‖+
      ‖((G.val*!![1,u;0,1]*H.val) 1 1:ℂ)‖ := norm_add_le _ _
    _=|(G.val*!![1,u;0,1]*H.val) 1 0| *‖(z:ℂ)‖+
      |(G.val*!![1,u;0,1]*H.val) 1 1| := by
      rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    _≤(3*B^2)*‖(z:ℂ)‖+3*B^2 :=
      add_le_add (mul_le_mul_of_nonneg_right (he 1 0) (norm_nonneg _)) (he 1 1)
    _=_ := by ring

/-- Actual averaging near returns, with the denominator premise discharged. -/
theorem averaging_hyperbolic_parameter_sublevel_explicit (G H : GL (Fin 2) ℝ)
    (hG : G.val.det=1) (hH : H.val.det=1) (B : ℝ) (hB : 0<B)
    (hGb : ∀ i j,|G.val i j|≤B) (hHb : ∀ i j,|H.val i j|≤B)
    (z : ℍ) (X Y : ℝ) (hX : 0≤X) (hY : 0<Y) (hx : |z.re|≤X) (hy : Y≤z.im)
    (r : ℝ) (hr : 0<r) :
    volume {u∈Icc (0:ℝ) 1 | dist (G • (u+ᵥ(H•z))) z<r}≤
      ENNReal.ofReal ((1+4*(3*B^2*(‖(z:ℂ)‖+1))*localDisplacementScale z 0/
        ((1/(B*(1+(X+1)/Y)))^2))*r) :=
  averaging_hyperbolic_parameter_sublevel G H hG hH B hB hGb hHb z X Y
    (3*B^2*(‖(z:ℂ)‖+1)) hX hY (by positivity) hx hy
    (fun u hu => averaging_denominator_bound G H B hB.le hGb hHb u hu z) r hr

#print axioms averaging_product_entry_bound
#print axioms averaging_denominator_bound
#print axioms averaging_hyperbolic_parameter_sublevel_explicit

end QuantitativeMaass
