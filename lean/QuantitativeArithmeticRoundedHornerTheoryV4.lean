module

public import Mathlib.Data.Rat.Floor
public import QuantitativeArithmeticComplexHornerBoundsTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticRoundedHorner. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticRoundedHornerV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

/-! Certified fixed-precision Horner evaluation. Intermediate rounded states
and their error bounds are computed, rather than supplied as a long witness. -/
namespace QuantitativeArithmeticRoundedHorner
open QuantitativeArithmeticComplexHornerBounds

def roundDown (D u : ℚ) : ℚ := (⌊D*u⌋ : ℚ)/D

theorem roundDown_error (D u : ℚ) (hD : 0<D) :
    0 ≤ u-roundDown D u ∧ u-roundDown D u ≤ 1/D := by
  have hf := Int.floor_le (D*u)
  have hg := Int.lt_floor_add_one (D*u)
  have hlo : roundDown D u ≤ u := by
    apply (div_le_iff₀ hD).2
    nlinarith
  refine ⟨sub_nonneg.mpr hlo, ?_⟩
  apply (le_div_iff₀ hD).2
  have hc : roundDown D u*D=(⌊D*u⌋ : ℚ) := div_mul_cancel₀ _ (ne_of_gt hD)
  nlinarith

theorem abs_roundDown_error (D u : ℚ) (hD : 0<D) :
    |u-roundDown D u| ≤ 1/D := by
  rw [abs_of_nonneg (roundDown_error D u hD).1]
  exact (roundDown_error D u hD).2

def step (D a : ℚ) (z u : ℚ × ℚ) : ℚ × ℚ :=
  (roundDown D (a+z.1*u.1-z.2*u.2), roundDown D (z.1*u.2+z.2*u.1))

theorem step_error (D a : ℚ) (z u : ℚ × ℚ) (hD : 0<D) :
    |(ratResidual a z u (step D a z u)).1|+
      |(ratResidual a z u (step D a z u)).2| ≤ 2/D := by
  have h := add_le_add (abs_roundDown_error D (a+z.1*u.1-z.2*u.2) hD)
    (abs_roundDown_error D (z.1*u.2+z.2*u.1) hD)
  simpa only [ratResidual, step, div_eq_mul_inv, one_mul, ← two_mul] using h

def value (D : ℚ) (a : ℕ → ℚ) (z : ℚ × ℚ) : ℕ → ℕ → ℚ × ℚ
  | 0, _ => (0,0)
  | n+1, j => step D (a j) z (value D a z n (j+1))

def error (D R : ℚ) : ℕ → ℚ
  | 0 => 0
  | n+1 => 2/D+R*error D R n

theorem error_nonneg (D R : ℚ) (hD : 0<D) (hR : 0≤R) (n : ℕ) :
    0≤error D R n := by
  induction n with
  | zero => simp [error]
  | succ n ih =>
    exact add_nonneg (div_nonneg (by norm_num) hD.le) (mul_nonneg hR ih)

theorem steps (D R : ℚ) (a : ℕ → ℚ) (z : ℚ × ℚ) (hD : 0<D)
    (n j : ℕ) (hj : j<n) :
    |(ratResidual (a j) z (value D a z (n-(j+1)) (j+1))
        (value D a z (n-j) j)).1|+
      |(ratResidual (a j) z (value D a z (n-(j+1)) (j+1))
        (value D a z (n-j) j)).2|+
      R*error D R (n-(j+1)) ≤ error D R (n-j) := by
  have hn : n-j=(n-(j+1))+1 := by omega
  rw [hn, value, error]
  exact add_le_add (step_error D (a j) z _ hD) (le_refl _)

/-- The whole polynomial has a certified error bound with no per-step
arithmetic assumptions or externally supplied intermediate values. -/
theorem polynomial_error (D R : ℚ) (a : ℕ → ℚ) (z : ℚ × ℚ)
    (hD : 0<D) (hz : |z.1|+|z.2|≤R) (n : ℕ) :
    ‖(hornerPolynomial (fun j => (a j : ℂ)) n 0).eval (ratComplex z)-
      ratComplex (value D a z n 0)‖ ≤ (error D R n : ℝ) := by
  have hR : 0≤R := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hz
  have h := polynomial_error_of_rational_certificate a z
    (fun j => value D a z (n-j) j) (fun j => error D R (n-j)) R n hz
    (fun j _ => error_nonneg D R hD hR (n-j))
    (by simp [value, error])
    (fun j hj => steps D R a z hD n j hj)
  simpa only [Nat.sub_zero] using h

#print axioms roundDown_error
#print axioms step_error
#print axioms error_nonneg
#print axioms steps
#print axioms polynomial_error
end QuantitativeArithmeticRoundedHorner
end
end

/-! ## QuantitativeArithmeticRoundedHornerBoundsV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticRoundedHorner
open QuantitativeArithmeticComplexHornerBounds

/-- A rounded Horner certificate needs only its final rational inequality.
All intermediate error inequalities follow from the rounding construction. -/
theorem polynomial_bound (D R B : ℚ) (a : ℕ → ℚ) (z : ℚ × ℚ)
    (hD : 0<D) (hz : |z.1|+|z.2|≤R) (n : ℕ)
    (hfinal : |(value D a z n 0).1|+|(value D a z n 0).2|+error D R n≤B) :
    ‖(hornerPolynomial (fun j => (a j : ℂ)) n 0).eval (ratComplex z)‖ ≤ (B : ℝ) := by
  have hR : 0≤R := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hz
  have h := polynomial_bound_of_rational_certificate a z
    (fun j => value D a z (n-j) j) (fun j => error D R (n-j)) R B n hz
    (fun j _ => error_nonneg D R hD hR (n-j))
    (by simp [value, error])
    (fun j hj => steps D R a z hD n j hj)
    (by simpa only [Nat.sub_zero] using hfinal)
  exact h

#print axioms polynomial_bound
end QuantitativeArithmeticRoundedHorner
end
end
