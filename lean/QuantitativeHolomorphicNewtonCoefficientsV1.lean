module

public import QuantitativeHolomorphicNewtonPerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open Polynomial

/-- Changing X to -X makes every Newton coefficient nonnegative. -/
def positiveNewtonPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C (1 / 2) * positiveNewtonPolynomial n *
      (C 3 + X * positiveNewtonPolynomial n ^ 2)

theorem positiveNewtonPolynomial_eq (n : ℕ) :
    positiveNewtonPolynomial n = (inverseSqrtPolynomial n).comp (-X) := by
  induction n with
  | zero => simp [positiveNewtonPolynomial, inverseSqrtPolynomial]
  | succ n ih =>
    simp only [positiveNewtonPolynomial, inverseSqrtPolynomial, mul_comp, sub_comp,
      C_comp, X_comp, pow_comp, ← ih]
    ring

private theorem coeff_mul_nonneg (p q : ℝ[X]) (hp : ∀ j, 0 ≤ p.coeff j)
    (hq : ∀ j, 0 ≤ q.coeff j) (j : ℕ) : 0 ≤ (p * q).coeff j := by
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp i.1) (hq i.2))

theorem positiveNewtonPolynomial_coeff_nonneg (n j : ℕ) :
    0 ≤ (positiveNewtonPolynomial n).coeff j := by
  induction n generalizing j with
  | zero => simp only [positiveNewtonPolynomial, coeff_one]; positivity
  | succ n ih =>
    rw [positiveNewtonPolynomial]
    apply coeff_mul_nonneg
    · exact fun j => coeff_mul_nonneg _ _ (fun j => by simp [coeff_C]; positivity) ih j
    · intro j
      rw [coeff_add]
      apply add_nonneg (by simp [coeff_C]; positivity)
      apply coeff_mul_nonneg _ _ (fun j => by simp [coeff_X]; positivity)
      simpa only [pow_two] using coeff_mul_nonneg _ _ ih ih

theorem positiveNewtonPolynomial_coeff (n j : ℕ) :
    (positiveNewtonPolynomial n).coeff j = |(inverseSqrtPolynomial n).coeff j| := by
  have he : (positiveNewtonPolynomial n).coeff j =
      (inverseSqrtPolynomial n).coeff j * (-1 : ℝ) ^ j := by
    rw [positiveNewtonPolynomial_eq, show (-X : ℝ[X]) = C (-1) * X by simp]
    exact comp_C_mul_X_coeff
  have ha := congrArg abs he
  rw [abs_of_nonneg (positiveNewtonPolynomial_coeff_nonneg n j), abs_mul, abs_pow] at ha
  simpa using ha

theorem polynomialMass_inverseSqrt_eq (n : ℕ) (D : ℝ) :
    polynomialMass (inverseSqrtPolynomial n) D = (positiveNewtonPolynomial n).eval D := by
  have hs : (inverseSqrtPolynomial n).support = (positiveNewtonPolynomial n).support := by
    ext j
    simp only [mem_support_iff, positiveNewtonPolynomial_coeff]
    exact (not_congr abs_eq_zero).symm
  rw [polynomialMass, hs, eval_eq_sum, sum_def]
  exact Finset.sum_congr rfl (fun j _ => by rw [positiveNewtonPolynomial_coeff])

theorem positiveNewtonPolynomial_eval_nonneg {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    0 ≤ (positiveNewtonPolynomial n).eval D := by
  rw [eval_eq_sum, sum_def]
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg (positiveNewtonPolynomial_coeff_nonneg n j) (pow_nonneg hD j))

theorem polynomialMass_inverseSqrt_le {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    polynomialMass (inverseSqrtPolynomial n) D ≤ (3 + D) ^ (4 ^ n) := by
  rw [polynomialMass_inverseSqrt_eq]
  have hbase : 1 ≤ 3 + D := by linarith
  induction n with
  | zero => simpa [positiveNewtonPolynomial] using hbase
  | succ n ih =>
    let L := (3 + D) ^ (4 ^ n)
    have hL : 1 ≤ L := one_le_pow₀ hbase
    have hQ := positiveNewtonPolynomial_eval_nonneg hD n
    have hp : (positiveNewtonPolynomial n).eval D ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ hQ ih 2
    have hpart : 3 + D * (positiveNewtonPolynomial n).eval D ^ 2 ≤ (3 + D) * L ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hp hD, one_le_pow₀ hL (n := 2)]
    simp only [positiveNewtonPolynomial, eval_mul, eval_C, eval_add, eval_X, eval_pow]
    calc
      _ ≤ L * ((3 + D) * L ^ 2) := by
        apply mul_le_mul _ hpart (by positivity) (by positivity)
        nlinarith
      _ = (3 + D) * L ^ 3 := by ring
      _ = (3 + D) ^ (1 + 3 * 4 ^ n) := by
        dsimp [L]
        rw [pow_add, pow_one, ← pow_mul, Nat.mul_comm (4 ^ n) 3]
      _ ≤ (3 + D) ^ (4 ^ (n + 1)) := by
        apply pow_le_pow_right₀ hbase
        have hp : 1 ≤ 4 ^ n := Nat.one_le_pow n 4 (by omega)
        rw [pow_succ]
        omega

theorem polynomialSensitivity_le_degree_mass (p : ℝ[X]) {D : ℝ} (hD : 0 ≤ D) :
    polynomialSensitivity p D ≤ (p.natDegree : ℝ) * polynomialMass p D := by
  unfold polynomialSensitivity polynomialMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjd : (j : ℝ) ≤ p.natDegree := by exact_mod_cast le_natDegree_of_ne_zero (mem_support_iff.1 hj)
  have hh := mul_le_mul_of_nonneg_left hjd (mul_nonneg (abs_nonneg (p.coeff j)) (pow_nonneg hD j))
  nlinarith only [hh]

theorem polynomialSensitivity_inverseSqrt_le {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    polynomialSensitivity (inverseSqrtPolynomial n) D ≤
      (3 ^ n : ℕ) * (3 + D) ^ (4 ^ n) := by
  apply (polynomialSensitivity_le_degree_mass _ hD).trans
  have hd : ((inverseSqrtPolynomial n).natDegree : ℝ) ≤ (3 ^ n : ℕ) := by
    exact_mod_cast (Nat.le_add_right _ 1).trans (inverseSqrtPolynomial_degree_bound n)
  have hm : 0 ≤ polynomialMass (inverseSqrtPolynomial n) D := by
    unfold polynomialMass; positivity
  exact mul_le_mul hd (polynomialMass_inverseSqrt_le hD n) hm (by positivity)

/-- Closed perturbation bound with no implicit polynomial coefficient sum. -/
theorem finite_polynomial_normalization_closed_error {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R V : G →L[ℂ] H) {κ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hR : ∀ v, κ * ‖v‖ ^ 2 ≤ ‖R v‖ ^ 2)
    (hRn : ‖R‖ ≤ 1) (hVn : ‖V‖ ≤ 2) (hδ : ‖V - R‖ ≤ δ) (n : ℕ) :
    ‖polynomialNormalizedReconstruction V n - normalizedReconstruction R‖ ≤
      δ * (1 + 3 * (3 ^ n : ℕ)) * (7 : ℝ) ^ (4 ^ n) +
        (1 - κ) ^ (2 ^ n) / Real.sqrt κ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg (V - R)).trans hδ
  apply (finite_polynomial_normalization_error R V hκ hκ1 hR hRn hVn hδ n).trans
  apply add_le_add _ le_rfl
  have hm := polynomialMass_inverseSqrt_le (by norm_num : (0 : ℝ) ≤ 4) n
  have hs := polynomialSensitivity_inverseSqrt_le (by norm_num : (0 : ℝ) ≤ 4) n
  norm_num only [show (3 + 4 : ℝ) = 7 by norm_num] at hm hs
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add hm (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 3))) hδ0
  convert hh using 1
  ring

#print axioms positiveNewtonPolynomial_coeff
#print axioms polynomialMass_inverseSqrt_le
#print axioms polynomialSensitivity_inverseSqrt_le

end QuantitativeHolomorphic
