module

public import QuantitativeMaassDistributionExpCancellationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem positiveTestPower_comp (n m : ℕ) (φ : PositiveSmoothTest) :
    positiveTestPower m (positiveTestPower n φ)=positiveTestPower (n+m) φ := by
  ext t
  simp only [positiveTestPower_apply,pow_add,mul_assoc]

private theorem expMoment_pow_norm (B : H →L[ℝ] H) (x : H) (n : ℕ) :
    ‖(B^n) x‖≤‖B‖^n*‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp]
    calc
      _ ≤ ‖B‖*‖(B^n) x‖ := B.le_opNorm _
      _ ≤ ‖B‖*(‖B‖^n*‖x‖) := mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = _ := by rw [pow_succ']; ring

theorem distributionExpMoment_bound (T : PositiveSmoothTest →ₗ[ℝ] H)
    (B : H →L[ℝ] H) (φ : PositiveSmoothTest) (C R : ℝ)
    (hb : ∀ n,‖T (positiveTestPower n φ)‖≤C*R^n) (n : ℕ) :
    ‖(B^n) (T (positiveTestPower n φ))‖≤C*(‖B‖*R)^n := by
  calc
    _ ≤ ‖B‖^n*‖T (positiveTestPower n φ)‖ := expMoment_pow_norm B _ n
    _ ≤ ‖B‖^n*(C*R^n) := mul_le_mul_of_nonneg_left (hb n) (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem distributionExp_mixed_term (T : PositiveSmoothTest →ₗ[ℝ] H)
    (B : H →L[ℝ] H) (φ : PositiveSmoothTest) (n m : ℕ) :
    ((-1:ℝ)^n*(n.factorial:ℝ)⁻¹) • (B^n) (distributionExpTerm T B (positiveTestPower n φ) m)=
      inverseExpCoefficient n m • (B^(n+m)) (T (positiveTestPower (n+m) φ)) := by
  simp only [distributionExpTerm,map_smul,smul_smul,positiveTestPower_comp,
    inverseExpCoefficient,pow_add,mul_apply_eq_comp]

/-- Each coefficient of the inverse transform is an absolutely convergent
row of the double exponential series. -/
theorem distributionExpTransform_inverse_row (T : PositiveSmoothTest →ₗ[ℝ] H)
    (B : H →L[ℝ] H) (hs : ∀ φ,Summable (distributionExpTerm T B φ))
    (φ : PositiveSmoothTest) (n : ℕ) :
    (-1:ℝ)^n • distributionExpTerm (distributionExpTransform T B hs) B φ n=
      ∑' m,inverseExpCoefficient n m • (B^(n+m)) (T (positiveTestPower (n+m) φ)) := by
  change (-1:ℝ)^n • ((n.factorial:ℝ)⁻¹ • (B^n)
    (∑' m,distributionExpTerm T B (positiveTestPower n φ) m))=_
  rw [smul_smul,(B^n).map_tsum (hs (positiveTestPower n φ)),
    ← ((B^n).summable (hs (positiveTestPower n φ))).tsum_const_smul]
  apply tsum_congr
  exact distributionExp_mixed_term T B φ n

/-- The constructed integrating factor is invertible on distributions with
exponentially bounded polynomial test moments. Its inverse is proved by an
absolutely convergent double series, not postulated as a multiplier rule. -/
theorem distributionExpTransform_inverse [CompleteSpace H]
    (T : PositiveSmoothTest →ₗ[ℝ] H) (B : H →L[ℝ] H)
    (hs : ∀ φ,Summable (distributionExpTerm T B φ))
    (φ : PositiveSmoothTest) (C R : ℝ) (hC : 0≤C) (hR : 0≤R)
    (hb : ∀ n,‖T (positiveTestPower n φ)‖≤C*R^n) :
    (∑' n,(-1:ℝ)^n • distributionExpTerm (distributionExpTransform T B hs) B φ n)=T φ := by
  let x : ℕ → H := fun n => (B^n) (T (positiveTestPower n φ))
  have hx : ∀ n,‖x n‖≤C*(‖B‖*R)^n := distributionExpMoment_bound T B φ C R hb
  have hd : Summable (fun p : ℕ×ℕ => inverseExpCoefficient p.1 p.2 • x (p.1+p.2)) :=
    inverseExp_double_summable x C (‖B‖*R) hC (mul_nonneg (norm_nonneg _) hR) hx
  have he : (∑' n,∑' m,inverseExpCoefficient n m • x (n+m))=x 0 :=
    inverseExp_double_sum x hd
  have hrow : (∑' n,(-1:ℝ)^n • distributionExpTerm (distributionExpTransform T B hs) B φ n)=
      ∑' n,∑' m,inverseExpCoefficient n m • x (n+m) :=
    tsum_congr (distributionExpTransform_inverse_row T B hs φ)
  have hz : x 0=T φ := by
    change (B^0) (T (positiveTestPower 0 φ))=T φ
    rw [pow_zero,one_apply_eq_self,positiveTestPower_zero]
  exact hrow.trans (he.trans hz)

/-- Exact first-order distribution representation by the convergent
exponential moment series of one constant vector. Identifying this series
with the integrated smooth exponential evolution is a separate step. -/
theorem distributionExpTransform_series_representation [CompleteSpace H]
    (T : PositiveSmoothTest →ₗ[ℝ] H) (B : H →L[ℝ] H)
    (hs : ∀ φ,Summable (distributionExpTerm T B φ))
    (hT : ∀ φ,T (positiveSmoothTestDeriv φ)=B (T φ))
    (φ : PositiveSmoothTest) (C R : ℝ) (hC : 0≤C) (hR : 0≤R)
    (hb : ∀ n,‖T (positiveTestPower n φ)‖≤C*R^n) :
    T φ=∑' n,((-1:ℝ)^n*(n.factorial:ℝ)⁻¹) •
      ((∫ t,φ t*t^n) • (B^n) (distributionExpTransform T B hs positiveUnitTest)) := by
  calc
    _ = ∑' n,(-1:ℝ)^n • distributionExpTerm (distributionExpTransform T B hs) B φ n :=
      (distributionExpTransform_inverse T B hs φ C R hC hR hb).symm
    _ = _ := by
      apply tsum_congr
      intro n
      rw [distributionExpTerm,distributionExpTransform_constant T B hs hT]
      simp only [positiveTestPower_apply,map_smul,smul_smul,mul_assoc]

#print axioms distributionExpTransform_inverse
#print axioms distributionExpTransform_series_representation

end QuantitativeMaass
