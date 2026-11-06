module

public import QuantitativeArithmeticRetainedFiniteConvergenceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedFiniteExpressions

open UpperHalfPlane MeasureTheory Set Filter SpanningIntegerRows
open AsymptoticFiniteBranch
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators
  (cell cell_measurable shift residue_nonneg residue_lt_one primitiveLowCost primitiveTerminalCost
   rowLowCost rowTerminalCost lowConstant terminalConstant)
open QuantitativeArithmeticRetainedRegularOperators
  (shiftQ shiftQ_cast level_pos residueQ_nonneg residueQ_le_one retained_pos)
open AsymptoticCertificateOperators (lowStrip highStrip lowStrip_measurable highStrip_measurable)
open AsymptoticCertificateBranches (residues)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)

theorem primitiveLow_holomorphic_norm_le (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 1≤t) (I : Finset ℤ) (m : ℕ) :
    ‖holomorphicSum (primitiveLowExpression A hN P j i t I) m‖≤P.ρ^(t-1)*primitiveLowCost A P i := by
  simp only [primitiveLowExpression,holomorphicSum_sumExpressions,holomorphicSum_ofFinset,holomorphic_lowFold]
  simp only [Rat.cast_natCast,Rat.cast_div,shiftQ_cast]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,P.ρ^(t-1)*(3*P.ρ+16/(Nat.lcm N (i.val.1^2):ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      exact AsymptoticFoldedLow.finite_folds_norm_le
        (QuantitativeArithmeticRetainedCertificateOperators.row_level_pos (hQ:=hQ) hN i)
        (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
        (lowStrip_measurable P.ε) P.rho_pos.le
        (residue_nonneg _ d) (residue_lt_one _ d).le
        (fun _ hz => hz.1) ht I m
    _ = _ := by simp [primitiveLowCost]; ring

theorem primitiveLow_regular_norm_le (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 1≤t) (I : Finset ℤ) (z : ℍ) :
    ‖regularSum (primitiveLowExpression A hN P j i t I) z‖≤P.ρ^(t-1)*primitiveLowCost A P i := by
  simp only [primitiveLowExpression,regularSum_sumExpressions,regularSum_ofFinset,regular_lowFold]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,P.ρ^(t-1)*(3*P.ρ+16/(Nat.lcm N (i.val.1^2):ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      simpa only [Rat.cast_natCast] using AsymptoticRegularFoldedLow.finite_folds_norm_le
        (level_pos (hQ:=hQ) hN i) (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
        (cell P.ε j) (lowStrip P.ε)
        P.rho_pos.le (residueQ_nonneg _ d) (residueQ_le_one _ d)
        (fun _ hz => hz.1) ht I z
    _ = _ := by simp [primitiveLowCost]; ring

theorem primitiveTerminal_holomorphic_norm_le (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (m : ℕ) :
    ‖holomorphicSum (primitiveTerminalExpression A hN P j i ht I) m‖≤primitiveTerminalCost A P i := by
  simp only [primitiveTerminalExpression,holomorphicSum_sumExpressions,holomorphicSum_ofFinset,holomorphic_terminalFold]
  simp only [Rat.cast_natCast,Rat.cast_div,shiftQ_cast]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,(3+4*((P.ε*(Nat.lcm N (i.val.1^2):ℝ))^2)⁻¹) := by
      apply Finset.sum_le_sum
      intro d _
      exact AsymptoticFoldedTerminal.finite_folds_norm_le
        (QuantitativeArithmeticRetainedCertificateOperators.row_level_pos (hQ:=hQ) hN i)
        (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
        (highStrip_measurable P.ε) P.epsilon_pos
        (residue_nonneg _ d) (residue_lt_one _ d).le
        (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le)
        (fun _ hz => hz.1) ht I m
    _ = _ := by simp [primitiveTerminalCost]; ring

theorem primitiveTerminal_regular_norm_le (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (z : ℍ) :
    ‖regularSum (primitiveTerminalExpression A hN P j i ht I) z‖≤primitiveTerminalCost A P i := by
  simp only [primitiveTerminalExpression,regularSum_sumExpressions,regularSum_ofFinset,regular_terminalFold]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,(3+4*((P.ε*(Nat.lcm N (i.val.1^2):ℝ))^2)⁻¹) := by
      apply Finset.sum_le_sum
      intro d _
      simpa only [Rat.cast_natCast] using AsymptoticRegularFoldedTerminal.finite_folds_norm_le
        (level_pos (hQ:=hQ) hN i) (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
        (cell P.ε j) (highStrip P.ε)
        P.epsilon_pos (residueQ_nonneg _ d) (residueQ_le_one _ d)
        (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le)
        (fun _ hz => hz.1) ht I z
    _ = _ := by simp [primitiveTerminalCost]; ring

variable (hS : ∀p∈S,p.Prime)

theorem rowLow_holomorphic_norm_le (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    (j : Fin Q) {t : ℕ} (ht : 1≤t) (I : Finset ℤ) (m : ℕ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖holomorphicSum (rowLowExpression A hS hN P χ β j t I i) m‖≤P.ρ^(t-1)*rowLowCost A P j i := by
  cases i with
  | inl i =>
    simpa only [rowLowExpression,holomorphicSum_scale,rowLowCost,norm_smul,
      hχ i.val.1 i.property.1,one_mul] using
      primitiveLow_holomorphic_norm_le A hN P j i ht I m
  | inr i =>
    have he : holomorphicSum (rowLowExpression A hS hN P χ β j t I (Sum.inr i)) m=
        QuantitativeArithmeticRetainedCertificateOperators.rowLow A hS hN P χ β j t m (Sum.inr i) := by
      simp only [rowLowExpression,QuantitativeArithmeticRetainedCertificateOperators.rowLow,retainedLow_holomorphic]
    rw [he]
    exact QuantitativeArithmeticRetainedCertificateOperators.rowLow_norm_le A hS hN P χ β hχ hβ j ht m (Sum.inr i)

/-- Truncation preserves the original uniform operator bound. -/
theorem low_holomorphic_norm_le (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 1≤t) (I : Finset ℤ) (m : ℕ) :
    ‖holomorphicSum (lowExpression A hS hN P χ β t I) m‖≤P.ρ^(t-1)*lowConstant A P := by
  simp only [lowExpression,holomorphicSum_sumExpressions,holomorphicSum_scale]
  apply (norm_sum_le _ _).trans
  rw [lowConstant,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,Complex.norm_ratCast]
  have hb := mul_le_mul_of_nonneg_left
    (rowLow_holomorphic_norm_le A hS hN P χ β hχ hβ j ht I m i) (abs_nonneg (A.coeff j i:ℝ))
  convert hb using 1
  ring

theorem rowLow_regular_norm_le (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    (j : Fin Q) {t : ℕ} (ht : 1≤t) (I : Finset ℤ) (z : ℍ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖regularSum (rowLowExpression A hS hN P χ β j t I i) z‖≤P.ρ^(t-1)*rowLowCost A P j i := by
  cases i with
  | inl i =>
    simpa only [rowLowExpression,regularSum_scale,rowLowCost,norm_smul,
      hχ i.val.1 i.property.1,one_mul] using
      primitiveLow_regular_norm_le A hN P j i ht I z
  | inr i =>
    have he : regularSum (rowLowExpression A hS hN P χ β j t I (Sum.inr i)) z=
        QuantitativeArithmeticRetainedRegularOperators.rowLow A hS hN P χ β j t z (Sum.inr i) := by
      simp only [rowLowExpression,QuantitativeArithmeticRetainedRegularOperators.rowLow,retainedLow_regular,regularSum_scale]
    rw [he]
    exact QuantitativeArithmeticRetainedRegularOperators.rowLow_norm_le A hS hN P χ β hχ hβ j ht z (Sum.inr i)

/-- Truncation preserves the original uniform operator bound. -/
theorem low_regular_norm_le (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 1≤t) (I : Finset ℤ) (z : ℍ) :
    ‖regularSum (lowExpression A hS hN P χ β t I) z‖≤P.ρ^(t-1)*lowConstant A P := by
  simp only [lowExpression,regularSum_sumExpressions,regularSum_scale]
  apply (norm_sum_le _ _).trans
  rw [lowConstant,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,Complex.norm_ratCast]
  have hb := mul_le_mul_of_nonneg_left
    (rowLow_regular_norm_le A hS hN P χ β hχ hβ j ht I z i) (abs_nonneg (A.coeff j i:ℝ))
  convert hb using 1
  ring

theorem rowTerminal_holomorphic_norm_le (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    (j : Fin Q) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (m : ℕ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖holomorphicSum (rowTerminalExpression A hS hN P χ β j ht I i) m‖≤rowTerminalCost A P j i := by
  cases i with
  | inl i =>
    simpa only [rowTerminalExpression,holomorphicSum_scale,rowTerminalCost,norm_smul,
      hχ i.val.1 i.property.1,one_mul] using
      primitiveTerminal_holomorphic_norm_le A hN P j i ht I m
  | inr i =>
    have he : holomorphicSum (rowTerminalExpression A hS hN P χ β j ht I (Sum.inr i)) m=
        QuantitativeArithmeticRetainedCertificateOperators.rowTerminal A hS hN P χ β j ht m (Sum.inr i) := by
      simp only [rowTerminalExpression,QuantitativeArithmeticRetainedCertificateOperators.rowTerminal,retainedTerminal_holomorphic]
    rw [he]
    exact QuantitativeArithmeticRetainedCertificateOperators.rowTerminal_norm_le A hS hN P χ β hχ hβ j ht m (Sum.inr i)

/-- Truncation preserves the original uniform operator bound. -/
theorem terminal_holomorphic_norm_le (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (m : ℕ) :
    ‖holomorphicSum (terminalExpression A hS hN P χ β ht I) m‖≤terminalConstant A P := by
  simp only [terminalExpression,holomorphicSum_sumExpressions,holomorphicSum_scale]
  apply (norm_sum_le _ _).trans
  rw [terminalConstant]
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,Complex.norm_ratCast]
  exact mul_le_mul_of_nonneg_left
    (rowTerminal_holomorphic_norm_le A hS hN P χ β hχ hβ j ht I m i) (abs_nonneg _)

theorem rowTerminal_regular_norm_le (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    (j : Fin Q) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (z : ℍ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖regularSum (rowTerminalExpression A hS hN P χ β j ht I i) z‖≤rowTerminalCost A P j i := by
  cases i with
  | inl i =>
    simpa only [rowTerminalExpression,regularSum_scale,rowTerminalCost,norm_smul,
      hχ i.val.1 i.property.1,one_mul] using
      primitiveTerminal_regular_norm_le A hN P j i ht I z
  | inr i =>
    have he : regularSum (rowTerminalExpression A hS hN P χ β j ht I (Sum.inr i)) z=
        QuantitativeArithmeticRetainedRegularOperators.rowTerminal A hS hN P χ β j ht z (Sum.inr i) := by
      simp only [rowTerminalExpression,QuantitativeArithmeticRetainedRegularOperators.rowTerminal,retainedTerminal_regular,regularSum_scale]
    rw [he]
    exact QuantitativeArithmeticRetainedRegularOperators.rowTerminal_norm_le A hS hN P χ β hχ hβ j ht z (Sum.inr i)

/-- Truncation preserves the original uniform operator bound. -/
theorem terminal_regular_norm_le (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1) (hβ : ∀p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (z : ℍ) :
    ‖regularSum (terminalExpression A hS hN P χ β ht I) z‖≤terminalConstant A P := by
  simp only [terminalExpression,regularSum_sumExpressions,regularSum_scale]
  apply (norm_sum_le _ _).trans
  rw [terminalConstant]
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,Complex.norm_ratCast]
  exact mul_le_mul_of_nonneg_left
    (rowTerminal_regular_norm_le A hS hN P χ β hχ hβ j ht I z i) (abs_nonneg _)

#print axioms low_holomorphic_norm_le
#print axioms low_regular_norm_le
#print axioms terminal_holomorphic_norm_le
#print axioms terminal_regular_norm_le

end QuantitativeArithmeticRetainedFiniteExpressions
