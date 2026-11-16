module

public import QuantitativeMaassMatrixMotionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane Matrix
open scoped Topology

namespace QuantitativeMaass

/-- Explicit entry growth for a product of two real partial words. -/
theorem realMatrix_product_entry_bound (M K : Matrix (Fin 2) (Fin 2) ℝ)
    (A B : ℝ) (hA : 0≤A) (hm : ∀ i j,|M i j|≤A) (hk : ∀ i j,|K i j|≤B) (i j : Fin 2) :
    |(M*K) i j|≤2*A*B := by
  simp only [Matrix.mul_apply,Fin.sum_univ_two]
  calc
    _≤|M i 0*K 0 j|+|M i 1*K 1 j| := abs_add_le _ _
    _=|M i 0| *|K 0 j|+|M i 1| *|K 1 j| := by rw [abs_mul,abs_mul]
    _≤A*B+A*B := add_le_add
      (mul_le_mul (hm i 0) (hk 0 j) (abs_nonneg _) hA)
      (mul_le_mul (hm i 1) (hk 1 j) (abs_nonneg _) hA)
    _=_ := by ring

/-- Entry height is at most exponential in the length of a real matrix
word, uniformly in bounded real averaging parameters. -/
theorem realMatrix_word_entry_bound (l : List (Matrix (Fin 2) (Fin 2) ℝ))
    (B : ℝ) (hB : 0≤B) (hl : ∀ M∈l,∀ i j,|M i j|≤B) (i j : Fin 2) :
    |l.prod i j|≤(2*B)^l.length := by
  have hall : ∀ i j,|l.prod i j|≤(2*B)^l.length := by
    induction l with
    | nil =>
      intro i j
      simp only [List.prod_nil,List.length_nil,pow_zero,Matrix.one_apply]
      split_ifs <;> norm_num
    | cons M l ih =>
      have ht := ih (fun A hA => hl A (List.mem_cons_of_mem M hA))
      have hh := realMatrix_product_entry_bound M l.prod B ((2*B)^l.length) hB
        (hl M List.mem_cons_self) ht
      simpa only [List.prod_cons,List.length_cons,pow_succ',mul_assoc] using hh
  exact hall i j

/-- The actual Möbius denominator has a linear entry-height bound. -/
theorem realMatrix_denominator_bound (M : GL (Fin 2) ℝ) (B : ℝ)
    (hm : ∀ i j,|M.val i j|≤B) (z : ℍ) :
    ‖denom M z‖≤B*(‖(z:ℂ)‖+1) := by
  change ‖(M.val 1 0:ℂ)*(z:ℂ)+(M.val 1 1:ℂ)‖≤_
  calc
    _≤‖(M.val 1 0:ℂ)*(z:ℂ)‖+‖(M.val 1 1:ℂ)‖ := norm_add_le _ _
    _=|M.val 1 0| *‖(z:ℂ)‖+|M.val 1 1| := by
      rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    _≤B*‖(z:ℂ)‖+B := add_le_add
      (mul_le_mul_of_nonneg_right (hm 1 0) (norm_nonneg _)) (hm 1 1)
    _=_ := by ring

/-- Reciprocal height under a determinant-one word grows polynomially in
its entry height, with an explicit retained-point factor. -/
theorem realMatrix_inverse_im_bound (M : GL (Fin 2) ℝ) (hM : M.val.det=1)
    (B : ℝ) (hm : ∀ i j,|M.val i j|≤B) (z : ℍ) :
    1/(M•z).im≤B^2*(‖(z:ℂ)‖+1)^2/z.im := by
  have him : (M•z).im=z.im/‖denom M z‖^2 := by
    rw [im_smul_eq_div_normSq]
    have hh : M.det.val=1 := hM
    rw [hh,abs_one,one_mul,Complex.normSq_eq_norm_sq]
  have heq : 1/(M•z).im=‖denom M z‖^2/z.im := by
    rw [him]
    field_simp
  rw [heq]
  apply div_le_div_of_nonneg_right _ z.im_pos.le
  have hh := pow_le_pow_left₀ (norm_nonneg (denom M z)) (realMatrix_denominator_bound M B hm z) 2
  simpa only [mul_pow] using hh

#print axioms realMatrix_product_entry_bound
#print axioms realMatrix_word_entry_bound
#print axioms realMatrix_denominator_bound
#print axioms realMatrix_inverse_im_bound

end QuantitativeMaass
