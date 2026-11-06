module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

abbrev IntegerMatrix2 := Matrix (Fin 2) (Fin 2) ℤ

def MatrixEntryBound (M : IntegerMatrix2) (B : ℝ) : Prop :=
  ∀ i j, |(M i j : ℝ)| ≤ B

theorem matrix_entry_bound_mul {A B : IntegerMatrix2} {a b : ℝ} (ha : 0 ≤ a)
    (hA : MatrixEntryBound A a) (hB : MatrixEntryBound B b) :
    MatrixEntryBound (A * B) (2 * a * b) := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul]
  calc
    _ ≤ |(A i 0 : ℝ) * (B 0 j : ℝ)| + |(A i 1 : ℝ) * (B 1 j : ℝ)| := abs_add_le _ _
    _ ≤ a * b + a * b := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul (hA i 0) (hB 0 j) (abs_nonneg _) ha)
        (mul_le_mul (hA i 1) (hB 1 j) (abs_nonneg _) ha)
    _ = _ := by ring

/-- Integral representatives of a word have exponential entry height
in its length, with an explicit base.  No uncontrolled choice of a
projective representative occurs in this estimate. -/
theorem matrix_entry_bound_word (l : List IntegerMatrix2) {B : ℝ} (hB : 0 ≤ B)
    (hl : ∀ M ∈ l, MatrixEntryBound M B) :
    MatrixEntryBound l.prod ((2 * B) ^ l.length) := by
  induction l with
  | nil =>
    intro i j
    simp only [List.prod_nil, List.length_nil, pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | cons M l ih =>
    have ht := ih (fun A hA => hl A (List.mem_cons_of_mem M hA))
    have hh := matrix_entry_bound_mul hB
      (hl M List.mem_cons_self) ht
    simpa only [List.prod_cons, List.length_cons, pow_succ', mul_assoc] using hh

theorem matrix_denominator_bound {M : IntegerMatrix2} {B Z : ℝ} (hB : 0 ≤ B)
    (hM : MatrixEntryBound M B) (z : ℂ) (hz : ‖z‖ ≤ Z) :
    ‖(M 1 0 : ℂ) * z + (M 1 1 : ℂ)‖ ≤ B * (Z + 1) := by
  calc
    _ ≤ ‖(M 1 0 : ℂ) * z‖ + ‖(M 1 1 : ℂ)‖ := norm_add_le _ _
    _ = |(M 1 0 : ℝ)| * ‖z‖ + |(M 1 1 : ℝ)| := by rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast]
    _ ≤ B * Z + B := add_le_add (mul_le_mul (hM 1 0) hz (norm_nonneg _) hB) (hM 1 1)
    _ = _ := by ring

theorem strip_matrix_denominator_bound {M : IntegerMatrix2} {B H : ℝ} (hB : 0 ≤ B)
    (hM : MatrixEntryBound M B) (z : UpperHalfPlane)
    (hre : |z.re| ≤ 1) (him : z.im ≤ H) :
    ‖(M 1 0 : ℂ) * (z : ℂ) + (M 1 1 : ℂ)‖ ≤ B * (H + 2) := by
  have hz : ‖(z : ℂ)‖ ≤ H + 1 := by
    have hh := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
    change ‖(z : ℂ)‖ ≤ |z.re| + |z.im| at hh
    rw [abs_of_pos z.im_pos] at hh
    linarith
  have hb := matrix_denominator_bound hB hM (z : ℂ) hz
  simpa only [add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using hb

#print axioms matrix_entry_bound_word
#print axioms strip_matrix_denominator_bound

end QuantitativeHolomorphic
