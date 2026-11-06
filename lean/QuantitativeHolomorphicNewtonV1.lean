module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open Polynomial

/-- Explicit Newton–Schulz inverse-square-root polynomial. -/
def inverseSqrtPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C (1 / 2) * inverseSqrtPolynomial n *
      (C 3 - X * inverseSqrtPolynomial n ^ 2)

def inverseSqrtValue (n : ℕ) (x : ℝ) : ℝ := (inverseSqrtPolynomial n).eval x

@[simp] theorem inverseSqrtValue_zero (x : ℝ) : inverseSqrtValue 0 x = 1 := by
  simp [inverseSqrtValue, inverseSqrtPolynomial]

theorem inverseSqrtValue_succ (n : ℕ) (x : ℝ) :
    inverseSqrtValue (n + 1) x =
      inverseSqrtValue n x * (3 - x * inverseSqrtValue n x ^ 2) / 2 := by
  simp only [inverseSqrtValue, inverseSqrtPolynomial, eval_mul, eval_C, eval_sub, eval_X, eval_pow]
  ring

theorem inverseSqrt_defect_succ (n : ℕ) (x : ℝ) :
    1 - x * inverseSqrtValue (n + 1) x ^ 2 =
      (1 - x * inverseSqrtValue n x ^ 2) ^ 2 *
        (3 + (1 - x * inverseSqrtValue n x ^ 2)) / 4 := by
  rw [inverseSqrtValue_succ]
  ring

theorem inverseSqrt_invariant {x : ℝ} (_hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    0 ≤ inverseSqrtValue n x ∧ 0 ≤ 1 - x * inverseSqrtValue n x ^ 2 := by
  induction n with
  | zero => simp only [inverseSqrtValue_zero, one_pow, mul_one]; constructor <;> linarith
  | succ n ih =>
      constructor
      · rw [inverseSqrtValue_succ]
        exact div_nonneg (mul_nonneg ih.1 (by linarith [ih.2])) (by norm_num)
      · rw [inverseSqrt_defect_succ]
        exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith [ih.2])) (by norm_num)

theorem inverseSqrt_defect_le_one {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    1 - x * inverseSqrtValue n x ^ 2 ≤ 1 := by
  nlinarith [mul_nonneg hx (sq_nonneg (inverseSqrtValue n x))]

theorem inverseSqrt_defect_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1 - x * inverseSqrtValue n x ^ 2 ≤ (1 - x) ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hi := inverseSqrt_invariant hx hx1 n
      have h1 := inverseSqrt_defect_le_one hx n
      have hstep : 1 - x * inverseSqrtValue (n + 1) x ^ 2 ≤
          (1 - x * inverseSqrtValue n x ^ 2) ^ 2 := by
        rw [inverseSqrt_defect_succ]
        nlinarith [mul_nonneg (sq_nonneg (1 - x * inverseSqrtValue n x ^ 2))
          (sub_nonneg.mpr h1)]
      apply hstep.trans
      have hp := pow_le_pow_left₀ hi.2 ih 2
      rw [← pow_mul] at hp
      simpa only [pow_succ (2 : ℕ) n] using hp

theorem inverseSqrt_scalar_error {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (n : ℕ) :
    |inverseSqrtValue n x - (Real.sqrt x)⁻¹| ≤
      (1 - x) ^ (2 ^ n) / Real.sqrt x := by
  have hi := inverseSqrt_invariant hx.le hx1 n
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hu0 : 0 ≤ Real.sqrt x * inverseSqrtValue n x := mul_nonneg hs.le hi.1
  have hu2 : (Real.sqrt x * inverseSqrtValue n x) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt hx.le]
    linarith [hi.2]
  have hu : Real.sqrt x * inverseSqrtValue n x ≤ 1 := by nlinarith
  have hq : inverseSqrtValue n x ≤ (Real.sqrt x)⁻¹ := by
    rw [← one_div, le_div_iff₀ hs]
    nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr hq)]
  calc
    _ = (1 - Real.sqrt x * inverseSqrtValue n x) / Real.sqrt x := by field_simp; ring
    _ ≤ (1 - x * inverseSqrtValue n x ^ 2) / Real.sqrt x := by
      apply div_le_div_of_nonneg_right _ hs.le
      have hmul := mul_nonneg hu0 (sub_nonneg.mpr hu)
      nlinarith [Real.sq_sqrt hx.le]
    _ ≤ _ := div_le_div_of_nonneg_right (inverseSqrt_defect_le hx.le hx1 n) hs.le

theorem inverseSqrt_uniform_scalar_error {κ x : ℝ} (hκ : 0 < κ)
    (hκx : κ ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    |inverseSqrtValue n x - (Real.sqrt x)⁻¹| ≤
      (1 - κ) ^ (2 ^ n) / Real.sqrt κ := by
  apply (inverseSqrt_scalar_error (hκ.trans_le hκx) hx1 n).trans
  calc
    _ ≤ (1 - κ) ^ (2 ^ n) / Real.sqrt x :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (sub_nonneg.mpr hx1) (sub_le_sub_left hκx 1) _)
        (Real.sqrt_nonneg x)
    _ ≤ _ := div_le_div_of_nonneg_left
      (pow_nonneg (sub_nonneg.mpr (hκx.trans hx1)) _)
      (Real.sqrt_pos.2 hκ) (Real.sqrt_le_sqrt hκx)

theorem inverseSqrtPolynomial_degree_step (n : ℕ) :
    (inverseSqrtPolynomial (n + 1)).natDegree ≤
      3 * (inverseSqrtPolynomial n).natDegree + 1 := by
  rw [inverseSqrtPolynomial]
  apply natDegree_mul_le.trans
  have hleft : (C (1 / 2 : ℝ) * inverseSqrtPolynomial n).natDegree ≤
      (inverseSqrtPolynomial n).natDegree := by
    simpa only [natDegree_C, zero_add] using
      (natDegree_mul_le (p := C (1 / 2 : ℝ)) (q := inverseSqrtPolynomial n))
  have hright : (C (3 : ℝ) - X * inverseSqrtPolynomial n ^ 2).natDegree ≤
      1 + 2 * (inverseSqrtPolynomial n).natDegree := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · have hh := (natDegree_mul_le (p := X) (q := inverseSqrtPolynomial n ^ 2)).trans (add_le_add le_rfl
        (natDegree_pow_le (p := inverseSqrtPolynomial n) (n := 2)))
      simpa only [natDegree_X] using hh
  omega

/-- Degree grows at most geometrically with iteration count, while the
error exponent grows as `2^n`. -/
theorem inverseSqrtPolynomial_degree_bound (n : ℕ) :
    (inverseSqrtPolynomial n).natDegree + 1 ≤ 3 ^ n := by
  induction n with
  | zero => simp [inverseSqrtPolynomial]
  | succ n ih =>
      have hs := inverseSqrtPolynomial_degree_step n
      rw [pow_succ]
      omega

theorem inverseSqrtValue_continuous (n : ℕ) : Continuous (inverseSqrtValue n) :=
  (inverseSqrtPolynomial n).continuous

#print axioms inverseSqrtPolynomial_degree_bound

#print axioms inverseSqrt_invariant
#print axioms inverseSqrt_defect_le
#print axioms inverseSqrt_uniform_scalar_error

end QuantitativeHolomorphic
