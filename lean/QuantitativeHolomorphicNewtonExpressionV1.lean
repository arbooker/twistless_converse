module

public import QuantitativeHolomorphicNewtonV1
public import QuantitativeHolomorphicExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open AsymptoticFiniteBranch ContinuousLinearMap

/-- The Newton polynomial expanded into the actual common branch language. -/
def inverseSqrtExpression (e : Expression) : ℕ → Expression
  | 0 => [identity]
  | n + 1 => scaleExpression (1 / 2) (composeExpression (inverseSqrtExpression e n)
      (scaleExpression 3 [identity] ++ scaleExpression (-1)
        (composeExpression e (composeExpression (inverseSqrtExpression e n)
          (inverseSqrtExpression e n)))))

theorem inverseSqrt_aeval_succ {𝔄 : Type*} [Ring 𝔄] [Algebra ℝ 𝔄]
    (A : 𝔄) (n : ℕ) :
    Polynomial.aeval A (inverseSqrtPolynomial (n + 1)) =
      (1 / 2 : ℝ) • (Polynomial.aeval A (inverseSqrtPolynomial n) *
        (3 - A * Polynomial.aeval A (inverseSqrtPolynomial n) ^ 2)) := by
  simp only [inverseSqrtPolynomial, map_mul, map_sub, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X, map_ofNat]
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc]

private theorem complex_newton_step {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A T : E →L[ℂ] E) :
    (1 / 2 : ℂ) • T.comp ((3 : ℂ) • 1 + (-1 : ℂ) • A.comp (T.comp T)) =
      (1 / 2 : ℝ) • (T * (3 - A * T ^ 2)) := by
  have h3 : (3 : ℂ) • (1 : E →L[ℂ] E) = 3 := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact map_ofNat _ _
  rw [h3, neg_one_smul]
  simp only [← mul_def, ← pow_two, ← sub_eq_add_neg]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (1 / 2 : ℝ)]
  norm_num

theorem holomorphicSum_inverseSqrt (e : Expression) (n m : ℕ) :
    holomorphicSum (inverseSqrtExpression e n) m =
      Polynomial.aeval (holomorphicSum e m) (inverseSqrtPolynomial n) := by
  induction n with
  | zero => simp [inverseSqrtExpression, inverseSqrtPolynomial, holomorphicSum, holomorphic_identity]
  | succ n ih =>
    have hid : holomorphicSum [identity] m = 1 := by
      simp [holomorphicSum, holomorphic_identity]
    rw [inverseSqrtExpression, holomorphicSum_scale, holomorphicSum_compose,
      holomorphicSum_append, holomorphicSum_scale, holomorphicSum_scale,
      holomorphicSum_compose, holomorphicSum_compose, ih, hid]
    exact (complex_newton_step _ _).trans (inverseSqrt_aeval_succ _ n).symm

theorem regularSum_inverseSqrt (e : Expression) (n : ℕ) (z : UpperHalfPlane) :
    regularSum (inverseSqrtExpression e n) z =
      Polynomial.aeval (regularSum e z) (inverseSqrtPolynomial n) := by
  induction n with
  | zero => simp [inverseSqrtExpression, inverseSqrtPolynomial, regularSum, regular_identity]
  | succ n ih =>
    let q := inverseSqrtExpression e n
    let T := Polynomial.aeval (regularSum e z) (inverseSqrtPolynomial n)
    have hid : regularSum [identity] z = 1 := by simp [regularSum, regular_identity]
    have hqq : regularSum (composeExpression q q) z = T.comp T :=
      (regularSum_compose q q z).trans (congrArg₂ (fun U V => U.comp V) ih ih)
    have heqq : regularSum (composeExpression e (composeExpression q q)) z =
        (regularSum e z).comp (T.comp T) :=
      (regularSum_compose e _ z).trans (congrArg (fun U => (regularSum e z).comp U) hqq)
    have hsum : regularSum (scaleExpression 3 [identity] ++ scaleExpression (-1)
        (composeExpression e (composeExpression q q))) z =
        (3 : ℂ) • 1 + (-1 : ℂ) • (regularSum e z).comp (T.comp T) := by
      exact (regularSum_append _ _ z).trans (congrArg₂ (· + ·)
        ((regularSum_scale 3 _ z).trans (congrArg (fun U => (3 : ℂ) • U) hid))
        ((regularSum_scale (-1) _ z).trans (congrArg (fun U => (-1 : ℂ) • U) heqq)))
    change regularSum (scaleExpression (1 / 2) (composeExpression q _)) z = _
    exact (regularSum_scale (1 / 2) _ z).trans
      ((congrArg (fun U => (1 / 2 : ℂ) • U) ((regularSum_compose q _ z).trans
        (congrArg₂ (fun U V => U.comp V) ih hsum))).trans
          ((complex_newton_step _ _).trans (inverseSqrt_aeval_succ _ n).symm))

theorem expressionBound_inverseSqrt_succ (e : Expression) (n : ℕ) :
    expressionBound (inverseSqrtExpression e (n + 1)) =
      (1 / 2) * expressionBound (inverseSqrtExpression e n) *
        (3 + expressionBound e * expressionBound (inverseSqrtExpression e n) ^ 2) := by
  rw [inverseSqrtExpression, expressionBound_scale, expressionBound_compose,
    expressionBound_append, expressionBound_scale, expressionBound_scale,
    expressionBound_compose, expressionBound_compose]
  norm_num [expressionBound, identity]
  ring

theorem length_inverseSqrt_succ (e : Expression) (n : ℕ) :
    (inverseSqrtExpression e (n + 1)).length =
      (inverseSqrtExpression e n).length *
        (1 + e.length * (inverseSqrtExpression e n).length ^ 2) := by
  simp only [inverseSqrtExpression, scaleExpression, List.length_map,
    length_composeExpression, List.length_append, List.length_cons, List.length_nil]
  ring

/-- A coarse but explicit coefficient-mass bound.  Since the Newton depth
is logarithmic in the logarithm of the accuracy, this is polynomial in
the logarithm of the requested accuracy for a fixed certificate. -/
theorem expressionBound_inverseSqrt_le (e : Expression) (n : ℕ) :
    expressionBound (inverseSqrtExpression e n) ≤ (3 + expressionBound e) ^ (4 ^ n) := by
  let D := 3 + expressionBound e
  have hE := expressionBound_nonneg e
  have hD : 1 ≤ D := by dsimp [D]; linarith
  induction n with
  | zero => simpa [inverseSqrtExpression, expressionBound, identity, D] using hD
  | succ n ih =>
    let L := D ^ (4 ^ n)
    have hL : 1 ≤ L := one_le_pow₀ hD
    have hQ := expressionBound_nonneg (inverseSqrtExpression e n)
    have hpart : 3 + expressionBound e * expressionBound (inverseSqrtExpression e n) ^ 2 ≤
        D * L ^ 2 := by
      have hp := pow_le_pow_left₀ hQ ih 2
      have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
      dsimp [D] at *
      nlinarith [mul_le_mul_of_nonneg_left hp hE]
    rw [expressionBound_inverseSqrt_succ]
    calc
      _ ≤ L * (D * L ^ 2) := by
        apply mul_le_mul _ hpart (by positivity) (by positivity)
        nlinarith
      _ = D ^ (1 + 3 * 4 ^ n) := by dsimp [L]; simp only [pow_add, pow_one, pow_mul]; ring
      _ ≤ D ^ (4 ^ (n + 1)) := by
        apply pow_le_pow_right₀ hD
        have hp : 1 ≤ 4 ^ n := Nat.one_le_pow n 4 (by omega)
        rw [pow_succ]
        omega

theorem length_inverseSqrt_le (e : Expression) (n : ℕ) :
    (inverseSqrtExpression e n).length ≤ (3 + e.length) ^ (4 ^ n) := by
  let D := 3 + e.length
  have hD : 1 ≤ D := by dsimp [D]; omega
  induction n with
  | zero => simpa only [inverseSqrtExpression, List.length_cons, List.length_nil,
      Nat.add_zero, pow_zero, pow_one] using hD
  | succ n ih =>
    let L := D ^ (4 ^ n)
    have hL : 1 ≤ L := Nat.one_le_pow _ _ hD
    have hp : (inverseSqrtExpression e n).length ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left ih 2
    have hpart : 1 + e.length * (inverseSqrtExpression e n).length ^ 2 ≤ D * L ^ 2 := by
      have hL2 : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ hL
      dsimp [D] at *
      nlinarith [Nat.mul_le_mul_left e.length hp]
    rw [length_inverseSqrt_succ]
    calc
      _ ≤ L * (D * L ^ 2) := Nat.mul_le_mul ih hpart
      _ = D ^ (1 + 3 * 4 ^ n) := by dsimp [L]; simp only [pow_add, pow_one, pow_mul]; ring
      _ ≤ D ^ (4 ^ (n + 1)) := by
        apply Nat.pow_le_pow_right hD
        have hp : 1 ≤ 4 ^ n := Nat.one_le_pow n 4 (by omega)
        rw [pow_succ]
        omega

#print axioms holomorphicSum_inverseSqrt
#print axioms regularSum_inverseSqrt
#print axioms expressionBound_inverseSqrt_le
#print axioms length_inverseSqrt_le

end QuantitativeHolomorphic
