module

public import QuantitativeArithmeticRetainedFiniteBoundsV1
public import QuantitativeHolomorphicRawComplexityV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedFiniteExpressions

open UpperHalfPlane MeasureTheory Set Filter SpanningIntegerRows
open AsymptoticFiniteBranch AsymptoticFoldMajorant
open QuantitativeHolomorphic
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators
  (cell cell_measurable shift residue_nonneg residue_lt_one primitiveLowCost primitiveTerminalCost
   rowLowCost rowTerminalCost lowConstant terminalConstant)
open QuantitativeArithmeticRetainedRegularOperators
  (shiftQ shiftQ_cast level_pos residueQ_nonneg residueQ_le_one retained_pos)
open AsymptoticCertificateOperators (lowStrip highStrip lowStrip_measurable highStrip_measurable)
open AsymptoticCertificateBranches (residues)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)

theorem primitiveLow_mass (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 1≤t) (I : Finset ℤ) :
    expressionBound (primitiveLowExpression A hN P j i t I)≤P.ρ^(t-1)*primitiveLowCost A P i := by
  simp only [primitiveLowExpression,expressionBound_sumExpressions,expressionBound_ofFinset]
  calc
    _ ≤ ∑ _d : residues i.val.1,P.ρ^(t-1)*(3*P.ρ+16/(Nat.lcm N (i.val.1^2):ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      change (∑ n∈I,majorant P.ρ (4/((Nat.lcm N (i.val.1^2):ℚ):ℝ)) n^t)≤_
      rw [Rat.cast_natCast]
      have hD : 0≤4/(Nat.lcm N (i.val.1^2):ℝ) := by positivity
      have hb := power_summable_bound P.rho_pos.le hD ht
      apply (Summable.sum_le_tsum I (fun n _ => pow_nonneg (majorant_nonneg P.rho_pos.le hD n) t) hb.1).trans
      convert hb.2 using 1
      ring
    _ = _ := by simp [primitiveLowCost]; ring

theorem primitiveTerminal_mass (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) :
    expressionBound (primitiveTerminalExpression A hN P j i ht I)≤primitiveTerminalCost A P i := by
  simp only [primitiveTerminalExpression,expressionBound_sumExpressions,expressionBound_ofFinset]
  calc
    _ ≤ ∑ _d : residues i.val.1,(3+4*((P.ε*(Nat.lcm N (i.val.1^2):ℝ))^2)⁻¹) := by
      apply Finset.sum_le_sum
      intro d _
      change (∑ n∈I,majorant 1 ((P.ε*((Nat.lcm N (i.val.1^2):ℚ):ℝ))^2)⁻¹ n)≤_
      rw [Rat.cast_natCast]
      have hD : 0≤((P.ε*(Nat.lcm N (i.val.1^2):ℝ))^2)⁻¹ := by positivity
      have hb := majorant_summable_bound zero_le_one hD
      exact (Summable.sum_le_tsum I (fun n _ => majorant_nonneg zero_le_one hD n) hb.1).trans
        (by simpa using hb.2)
    _ = _ := by simp [primitiveTerminalCost]; ring

variable (hS : ∀p∈S,p.Prime)

theorem retainedLow_mass (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ)
    {t : ℕ} (ht : 1≤t) :
    expressionBound (retainedLowExpression A hS P j p u t)≤
      P.ρ^(t-1)*(QuantitativeArithmeticRetainedDilationOperator.folds
        (p.val:ℝ) ((p.val:ℝ)*shift j u)).card := by
  simp only [retainedLowExpression,expressionBound_ofFinset,
    QuantitativeArithmeticRetainedDilationBranches.lowBranch_bound,Rat.cast_natCast,
    Finset.sum_const,nsmul_eq_mul]
  have hp : 1≤(p.val:ℝ) := by exact_mod_cast (hS p.val p.property).one_lt.le
  have hpow : (p.val:ℝ)⁻¹^t≤P.ρ^(t-1) := by
    calc
      _ ≤ (p.val:ℝ)⁻¹^(t-1) := pow_le_pow_of_le_one (by positivity)
        (inv_le_one_of_one_le₀ hp) (by omega)
      _ ≤ _ := pow_le_pow_left₀ (by positivity)
        (QuantitativeArithmeticRetainedCertificateOperators.retained_inverse_le A hS P p) _
  nlinarith [mul_le_mul_of_nonneg_left hpow
    (Nat.cast_nonneg (QuantitativeArithmeticRetainedDilationOperator.folds
      (p.val:ℝ) ((p.val:ℝ)*shift j u)).card)]

theorem retainedTerminal_mass (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ) (t : ℕ) :
    expressionBound (retainedTerminalExpression A hS P j p u t)=
      (QuantitativeArithmeticRetainedDilationOperator.folds
        (p.val:ℝ) ((p.val:ℝ)*shift j u)).card := by
  simp [retainedTerminalExpression,expressionBound_ofFinset,
    QuantitativeArithmeticRetainedDilationBranches.terminalBranch]

theorem rowLow_mass (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    (j : Fin Q) {t : ℕ} (ht : 1≤t) (I : Finset ℤ) (i : AugIndex N (S:Set ℕ) Q) :
    expressionBound (rowLowExpression A hS hN P χ β j t I i)≤P.ρ^(t-1)*rowLowCost A P j i := by
  cases i with
  | inl i =>
    simpa only [rowLowExpression,expressionBound_scale,rowLowCost,
      hχ i.val.1 i.property.1,one_mul] using primitiveLow_mass A hN P j i ht I
  | inr i =>
    simp only [rowLowExpression,expressionBound_scale,rowLowCost]
    apply (mul_le_mul_of_nonneg_right (hβ i.1.val i.1.property) (expressionBound_nonneg _)).trans
    rw [one_mul]
    exact retainedLow_mass A hS P j i.1 i.2 ht

/-- Coefficient mass is bounded by the same constant as the operator norm. -/
theorem low_mass (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 1≤t) (I : Finset ℤ) :
    expressionBound (lowExpression A hS hN P χ β t I)≤P.ρ^(t-1)*lowConstant A P := by
  simp only [lowExpression,expressionBound_sumExpressions,expressionBound_scale]
  rw [lowConstant,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Complex.norm_ratCast]
  have hb := mul_le_mul_of_nonneg_left
    (rowLow_mass A hS hN P χ β hχ hβ j ht I i) (abs_nonneg (A.coeff j i:ℝ))
  convert hb using 1
  ring

theorem rowTerminal_mass (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    (j : Fin Q) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (i : AugIndex N (S:Set ℕ) Q) :
    expressionBound (rowTerminalExpression A hS hN P χ β j ht I i)≤rowTerminalCost A P j i := by
  cases i with
  | inl i =>
    simpa only [rowTerminalExpression,expressionBound_scale,rowTerminalCost,
      hχ i.val.1 i.property.1,one_mul] using primitiveTerminal_mass A hN P j i ht I
  | inr i =>
    simp only [rowTerminalExpression,expressionBound_scale,rowTerminalCost]
    apply (mul_le_mul_of_nonneg_right (hβ i.1.val i.1.property) (expressionBound_nonneg _)).trans
    rw [one_mul]
    exact (retainedTerminal_mass A hS P j i.1 i.2 t).le

/-- Coefficient mass is bounded by the same constant as the operator norm. -/
theorem terminal_mass (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (I : Finset ℤ) :
    expressionBound (terminalExpression A hS hN P χ β ht I)≤terminalConstant A P := by
  simp only [terminalExpression,expressionBound_sumExpressions,expressionBound_scale]
  rw [terminalConstant]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  rw [Complex.norm_ratCast]
  have hb := mul_le_mul_of_nonneg_left
    (rowTerminal_mass A hS hN P χ β hχ hβ j ht I i) (abs_nonneg (A.coeff j i:ℝ))
  convert hb using 1

#print axioms low_mass
#print axioms terminal_mass
end QuantitativeArithmeticRetainedFiniteExpressions
