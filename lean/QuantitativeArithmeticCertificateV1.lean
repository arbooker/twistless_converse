module

public import QuantitativeHolomorphicWordGeometryV1

set_option autoImplicit false
@[expose] public noncomputable section

/-!
Concrete integer-matrix part of the density-one certificate construction.
The existence/density of suitable divisors is deliberately not asserted here.
In particular the exponent of V is (d-c)/Q, not (d-c)/(N*Q).
-/

namespace QuantitativeArithmetic

open QuantitativeHolomorphic

def upperUnipotent (s : ℤ) : IntegerMatrix2 := !![1, s; 0, 1]

def lowerUnipotent (N r : ℤ) : IntegerMatrix2 := !![1, 0; N*r, 1]

def certificateMatrix (Q B N c D : ℤ) : IntegerMatrix2 := !![Q, B; N*c, D]

theorem upperUnipotent_add (s t : ℤ) :
    upperUnipotent (s+t) = upperUnipotent s * upperUnipotent t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem lowerUnipotent_add (N r s : ℤ) :
    lowerUnipotent N (r+s) = lowerUnipotent N r * lowerUnipotent N s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem lowerUnipotent_nat_pow (N : ℤ) (m : ℕ) :
    (lowerUnipotent N 1)^m = lowerUnipotent N (m : ℤ) := by
  induction m with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]
  | succ m ih =>
    rw [pow_succ, ih, ← lowerUnipotent_add]
    simp

theorem lowerUnipotent_inverse (N r : ℤ) :
    lowerUnipotent N r * lowerUnipotent N (-r) = 1 := by
  rw [← lowerUnipotent_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]

/-- The precise multiplication producing the prime upper-left entry. -/
theorem certificate_shear (Q B N c D r s : ℤ) :
    upperUnipotent s * lowerUnipotent N r * certificateMatrix Q B N c D =
      certificateMatrix (Q + N*s*(c+r*Q)) (B+s*(N*r*B+D))
        N (c+r*Q) (N*r*B+D) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent, lowerUnipotent, certificateMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Divisor witnesses are arithmetic hypotheses, not density assumptions. -/
theorem certificate_shear_of_witnesses (Q B N c D r s d q : ℤ)
    (hd : d = c+r*Q) (hq : q = Q+N*s*d) :
    upperUnipotent s * lowerUnipotent N r * certificateMatrix Q B N c D =
      certificateMatrix q (B+s*(N*r*B+D)) N d (N*r*B+D) := by
  rw [certificate_shear, ← hd, ← hq]

theorem certificate_det (Q B N c D : ℤ) :
    (certificateMatrix Q B N c D).det = Q*D-N*c*B := by
  simp [certificateMatrix, Matrix.det_fin_two]
  ring

theorem certificate_shear_det (Q B N c D r s : ℤ) :
    (certificateMatrix (Q+N*s*(c+r*Q)) (B+s*(N*r*B+D))
      N (c+r*Q) (N*r*B+D)).det = (certificateMatrix Q B N c D).det := by
  simp only [certificate_det]
  ring

/-- Converting the first column (q,N*d) to the canonical prime-q matrix. -/
theorem canonical_conversion (q B N d D l β : ℤ) (hβ : B+q*l = -β) :
    lowerUnipotent N (-1) * certificateMatrix q B N d D * upperUnipotent l =
      !![q, -β; -N*(q-d), D+N*d*l+N*β] := by
  have hB : B = -β-q*l := by linarith
  subst B
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotent, certificateMatrix, upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- This proves the displayed canonical bottom-right entry and congruence
without dividing by q.  Division is legal as soon as q is nonzero. -/
theorem canonical_bottom_right (q B N d D l β : ℤ)
    (hdet : q*D-N*d*B = 1) (hβ : B+q*l = -β) :
    q*(D+N*d*l+N*β) = 1+N*(q-d)*β := by
  calc
    q*(D+N*d*l+N*β) = (q*D-N*d*B)+N*(q-d)*β+N*d*(B+q*l+β) := by ring
    _ = 1+N*(q-d)*β := by rw [hdet, hβ]; ring

theorem canonical_congruence (q B N d D l β : ℤ)
    (hdet : q*D-N*d*B = 1) (hβ : B+q*l = -β) :
    q ∣ 1+N*(q-d)*β := by
  exact ⟨D+N*d*l+N*β, (canonical_bottom_right q B N d D l β hdet hβ).symm⟩

/-- An explicit Bezout proof of the integrality of (q-Q)/(N*d). -/
theorem product_divides_of_bezout (N d n x y : ℤ)
    (hbezout : x*N+y*d = 1) (hN : N ∣ n) (hd : d ∣ n) : N*d ∣ n := by
  obtain ⟨u, hu⟩ := hN
  obtain ⟨v, hv⟩ := hd
  refine ⟨x*v+y*u, ?_⟩
  calc
    n = (x*N+y*d)*n := by rw [hbezout]; ring
    _ = x*N*(d*v)+y*d*(N*u) := by rw [← hv, ← hu]; ring
    _ = N*d*(x*v+y*u) := by ring

/-- The divisor congruence modulo N*Q implies the required shear witness.
No primality or analytic number theory is used. -/
theorem shear_witness_of_congruence (N Q c d : ℤ) (h : N*Q ∣ d-c) :
    ∃ r : ℤ, d = c+r*Q := by
  obtain ⟨t, ht⟩ := h
  refine ⟨N*t, ?_⟩
  calc
    d = c+(d-c) := by ring
    _ = c+(N*Q)*t := by rw [ht]
    _ = c+(N*t)*Q := by ring

theorem lowerUnipotent_entry_bound (N r : ℤ) :
    MatrixEntryBound (lowerUnipotent N r) (1+|(N : ℝ)| * |(r : ℝ)|) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotent, abs_mul]
  all_goals nlinarith [mul_nonneg (abs_nonneg (N : ℝ)) (abs_nonneg (r : ℝ))]

theorem upperUnipotent_entry_bound (s : ℤ) :
    MatrixEntryBound (upperUnipotent s) (1+|(s : ℝ)|) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent]
  all_goals nlinarith [abs_nonneg (s : ℝ)]

/-- Contiguous repeated lower unipotents have linear, rather than
exponential, entry height. -/
theorem lowerUnipotent_pow_entry_bound (N : ℤ) (m : ℕ) :
    MatrixEntryBound ((lowerUnipotent N 1)^m) (1+|(N : ℝ)| * (m : ℝ)) := by
  rw [lowerUnipotent_nat_pow]
  simpa using lowerUnipotent_entry_bound N (m : ℤ)

/-- The two variable shears cost a quadratic polynomial in their sizes. -/
theorem certificate_shear_entry_bound (M : IntegerMatrix2) (N r s : ℤ)
    {H : ℝ} (hM : MatrixEntryBound M H) :
    MatrixEntryBound (upperUnipotent s * lowerUnipotent N r * M)
      (4*(1+|(s : ℝ)|)*(1+|(N : ℝ)| * |(r : ℝ)|)*H) := by
  have hUV := matrix_entry_bound_mul (by positivity)
    (upperUnipotent_entry_bound s) (lowerUnipotent_entry_bound N r)
  have h := matrix_entry_bound_mul (by positivity) hUV hM
  convert h using 1
  ring

/-- Uniform quadratic entry height when both shear exponents are O(q).
This is a concrete polynomial estimate, independent of word length. -/
theorem certificate_shear_polynomial_entry_bound (M : IntegerMatrix2) (N r s : ℤ)
    {H C q : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C) (hq : 1 ≤ q)
    (hM : MatrixEntryBound M H) (hr : |(r : ℝ)| ≤ C*q)
    (hs : |(s : ℝ)| ≤ C*q) :
    MatrixEntryBound (upperUnipotent s * lowerUnipotent N r * M)
      (4*(1+C)*(1+|(N : ℝ)| * C)*H*q^2) := by
  have h₁ : 1+|(s : ℝ)| ≤ (1+C)*q := by nlinarith
  have h₂ : 1+|(N : ℝ)| * |(r : ℝ)| ≤ (1+|(N : ℝ)| * C)*q := by
    nlinarith [mul_le_mul_of_nonneg_left hr (abs_nonneg (N : ℝ))]
  intro i j
  calc
    _ ≤ 4*(1+|(s : ℝ)|)*(1+|(N : ℝ)| * |(r : ℝ)|)*H :=
      certificate_shear_entry_bound M N r s hM i j
    _ ≤ 4*((1+C)*q)*((1+|(N : ℝ)| * C)*q)*H := by gcongr
    _ = _ := by ring

/-- Every nonsingular integral matrix has a nonvanishing denominator on
the upper half-plane.  No translated-nonidentity condition is asserted. -/
theorem integer_matrix_denominator_ne_zero (M : IntegerMatrix2) (hdet : M.det ≠ 0)
    (z : UpperHalfPlane) : (M 1 0 : ℂ)*(z : ℂ)+(M 1 1 : ℂ) ≠ 0 := by
  intro h
  have him : (M 1 0 : ℝ)*z.im = 0 := by
    simpa [Complex.mul_im] using congrArg Complex.im h
  have hc : (M 1 0 : ℝ) = 0 := (mul_eq_zero.mp him).resolve_right z.im_ne_zero
  have hcZ : M 1 0 = 0 := by exact_mod_cast hc
  have hd : (M 1 1 : ℝ) = 0 := by
    simpa [hcZ] using congrArg Complex.re h
  have hdZ : M 1 1 = 0 := by exact_mod_cast hd
  apply hdet
  simp [Matrix.det_fin_two, hcZ, hdZ]

/-- The already proved strip estimate applied to the actual shear matrix. -/
theorem certificate_shear_strip_denominator_bound (M : IntegerMatrix2) (N r s : ℤ)
    {B H : ℝ} (hB : 0 ≤ B) (hM : MatrixEntryBound M B)
    (z : UpperHalfPlane) (hre : |z.re| ≤ 1) (him : z.im ≤ H) :
    ‖((upperUnipotent s * lowerUnipotent N r * M) 1 0 : ℂ)*(z : ℂ) +
      ((upperUnipotent s * lowerUnipotent N r * M) 1 1 : ℂ)‖ ≤
      (4*(1+|(s : ℝ)|)*(1+|(N : ℝ)| * |(r : ℝ)|)*B)*(H+2) := by
  exact strip_matrix_denominator_bound (by positivity)
    (certificate_shear_entry_bound M N r s hM) z hre him

#print axioms certificate_shear_of_witnesses
#print axioms canonical_conversion
#print axioms canonical_congruence
#print axioms product_divides_of_bezout
#print axioms lowerUnipotent_pow_entry_bound
#print axioms certificate_shear_entry_bound
#print axioms certificate_shear_polynomial_entry_bound
#print axioms integer_matrix_denominator_ne_zero
#print axioms certificate_shear_strip_denominator_bound

end QuantitativeArithmetic
