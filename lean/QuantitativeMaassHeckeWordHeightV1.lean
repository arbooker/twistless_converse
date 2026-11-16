module

public import QuantitativeMaassCorrespondenceHeightV1
public import QuantitativeMaassHeckeWordTraceV1
public import QuantitativeMaassRealMatrixWordsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane Matrix

namespace QuantitativeMaass

/-- Every standard integral Hecke representative has entries bounded by p. -/
theorem heckeBranchMatrix_entry_bound (p : ℕ) [Fact p.Prime] (j : Option (ZMod p)) :
    ∀ i k,|((HeckeUpper.branchMatrix p j) i k:ℝ)|≤p := by
  have hp : (1:ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  cases j with
  | none =>
    intro i k
    fin_cases i <;> fin_cases k
    · change |((p:ℤ):ℝ)|≤(p:ℝ);norm_num
    · change |((0:ℤ):ℝ)|≤(p:ℝ);norm_num
    · change |((0:ℤ):ℝ)|≤(p:ℝ);norm_num
    · change |((1:ℤ):ℝ)|≤(p:ℝ);simpa only [Int.cast_one,abs_one] using hp
  | some u =>
    have hu : (u.val:ℝ)≤p := by exact_mod_cast (ZMod.val_lt u).le
    intro i k
    fin_cases i <;> fin_cases k
    · change |((1:ℤ):ℝ)|≤(p:ℝ);simpa only [Int.cast_one,abs_one] using hp
    · change |((u.val:ℤ):ℝ)|≤(p:ℝ)
      simpa only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ)≤u.val)] using hu
    · change |((0:ℤ):ℝ)|≤(p:ℝ);norm_num
    · change |((p:ℤ):ℝ)|≤(p:ℝ);norm_num

/-- One actual Hecke branch increases the integral entry height by at most
9p, independently of the current word and of the level. -/
theorem heckeUpper_left_height (p : ℕ) [Fact p.Prime] (j : Option (ZMod p)) (M : HeckeUpper) :
    integralMatrixHeight (HeckeUpper.left p j M).matrix≤(9*(p:ℝ))*integralMatrixHeight M.matrix := by
  have hM := integralMatrixHeight_bounds M.matrix
  have hp : (1:ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have he (i k : Fin 2) : |((HeckeUpper.left p j M).matrix i k:ℝ)|≤2*(p:ℝ)*integralMatrixHeight M.matrix := by
    have hh := realMatrix_product_entry_bound
      ((HeckeUpper.branchMatrix p j).map (Int.castRingHom ℝ)) (M.matrix.map (Int.castRingHom ℝ))
      p (integralMatrixHeight M.matrix) (Nat.cast_nonneg p) (heckeBranchMatrix_entry_bound p j) hM.2 i k
    rw [HeckeUpper.left_matrix]
    simpa only [Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul,Matrix.map_apply,Int.coe_castRingHom] using hh
  have h1 : 1≤(p:ℝ)*integralMatrixHeight M.matrix := by nlinarith only [hp,hM.1]
  change 1+|((HeckeUpper.left p j M).matrix 0 0:ℝ)|+|((HeckeUpper.left p j M).matrix 0 1:ℝ)|+
    |((HeckeUpper.left p j M).matrix 1 0:ℝ)|+|((HeckeUpper.left p j M).matrix 1 1:ℝ)|≤_
  linarith only [he 0 0,he 0 1,he 1 0,he 1 1,h1]

#print axioms heckeBranchMatrix_entry_bound
#print axioms heckeUpper_left_height

end QuantitativeMaass
