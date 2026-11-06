module

public import QuantitativeArithmeticRetainedFiniteBoundsV1
public import QuantitativeHolomorphicFoldTailV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedFiniteExpressions

open UpperHalfPlane MeasureTheory Set Filter SpanningIntegerRows
open AsymptoticFiniteBranch
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators
  (cell cell_measurable shift residue_nonneg residue_lt_one)
open QuantitativeArithmeticRetainedRegularOperators
  (shiftQ shiftQ_cast level_pos residueQ_nonneg residueQ_le_one retained_pos)
open AsymptoticCertificateOperators (lowStrip highStrip lowStrip_measurable highStrip_measurable)
open AsymptoticCertificateBranches (residues)

def symmetricFolds (J : ℕ) : Finset ℤ := Finset.Icc (-(J:ℤ)) J

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)

def primitiveLowTailCost (i : RowIndex N Q) : ℝ :=
  (residues i.val.1).card*(8/(Nat.lcm N (i.val.1^2):ℝ))

def primitiveTerminalTailCost (P : Parameters A) (i : RowIndex N Q) : ℝ :=
  (residues i.val.1).card*(2*((P.ε*(Nat.lcm N (i.val.1^2):ℝ))^2)⁻¹)

theorem primitiveLow_holomorphic_error (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 1≤t) (J : ℕ) (hJ : 0<J) (m : ℕ) :
    ‖QuantitativeArithmeticRetainedCertificateOperators.primitiveLow A hN P j i t m-
      holomorphicSum (primitiveLowExpression A hN P j i t (symmetricFolds J)) m‖≤P.ρ^(t-1)*primitiveLowTailCost i/(J:ℝ) := by
  simp only [primitiveLowExpression,holomorphicSum_sumExpressions,holomorphicSum_ofFinset,
    holomorphic_lowFold,QuantitativeArithmeticRetainedCertificateOperators.primitiveLow]
  simp only [Rat.cast_natCast,Rat.cast_div,shiftQ_cast]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,P.ρ^(t-1)*(2*(4/(Nat.lcm N (i.val.1^2):ℝ))/(J:ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      exact QuantitativeHolomorphic.physical_low_fold_truncation_bound
        (QuantitativeArithmeticRetainedCertificateOperators.row_level_pos (hQ:=hQ) hN i)
        (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
        (lowStrip_measurable P.ε) P.rho_pos.le
        (residue_nonneg _ d) (residue_lt_one _ d).le
        (fun _ hz => hz.1) ht m J hJ
    _ = _ := by simp [primitiveLowTailCost]; ring

theorem primitiveLow_regular_error (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 1≤t) (J : ℕ) (hJ : 0<J) (z : ℍ) :
    ‖QuantitativeArithmeticRetainedRegularOperators.primitiveLow A hN P j i t z-
      regularSum (primitiveLowExpression A hN P j i t (symmetricFolds J)) z‖≤P.ρ^(t-1)*primitiveLowTailCost i/(J:ℝ) := by
  simp only [primitiveLowExpression,regularSum_sumExpressions,regularSum_ofFinset,
    regular_lowFold,QuantitativeArithmeticRetainedRegularOperators.primitiveLow]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,P.ρ^(t-1)*(2*(4/(Nat.lcm N (i.val.1^2):ℝ))/(J:ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      simpa only [Rat.cast_natCast,symmetricFolds] using QuantitativeHolomorphic.regular_low_fold_truncation_bound
        (level_pos (hQ:=hQ) hN i) (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
        (cell P.ε j) (lowStrip P.ε)
        P.rho_pos.le (residueQ_nonneg _ d) (residueQ_le_one _ d)
        (fun _ hz => hz.1) ht z J hJ
    _ = _ := by simp [primitiveLowTailCost]; ring

theorem primitiveTerminal_holomorphic_error (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 2≤t) (J : ℕ) (hJ : 0<J) (m : ℕ) :
    ‖QuantitativeArithmeticRetainedCertificateOperators.primitiveTerminal A hN P j i ht m-
      holomorphicSum (primitiveTerminalExpression A hN P j i ht (symmetricFolds J)) m‖≤primitiveTerminalTailCost A P i/(J:ℝ) := by
  simp only [primitiveTerminalExpression,holomorphicSum_sumExpressions,holomorphicSum_ofFinset,
    holomorphic_terminalFold,QuantitativeArithmeticRetainedCertificateOperators.primitiveTerminal]
  simp only [Rat.cast_natCast,Rat.cast_div,shiftQ_cast]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,2*((P.ε*(Nat.lcm N (i.val.1^2):ℝ))^2)⁻¹/(J:ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      exact QuantitativeHolomorphic.physical_terminal_fold_truncation_bound
        (QuantitativeArithmeticRetainedCertificateOperators.row_level_pos (hQ:=hQ) hN i)
        (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
        (highStrip_measurable P.ε) P.epsilon_pos
        (residue_nonneg _ d) (residue_lt_one _ d).le
        (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le)
        (fun _ hz => hz.1) ht m J hJ
    _ = _ := by simp [primitiveTerminalTailCost]; ring

theorem primitiveTerminal_regular_error (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 2≤t) (J : ℕ) (hJ : 0<J) (z : ℍ) :
    ‖QuantitativeArithmeticRetainedRegularOperators.primitiveTerminal A hN P j i ht z-
      regularSum (primitiveTerminalExpression A hN P j i ht (symmetricFolds J)) z‖≤primitiveTerminalTailCost A P i/(J:ℝ) := by
  simp only [primitiveTerminalExpression,regularSum_sumExpressions,regularSum_ofFinset,
    regular_terminalFold,QuantitativeArithmeticRetainedRegularOperators.primitiveTerminal]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,2*((P.ε*(Nat.lcm N (i.val.1^2):ℝ))^2)⁻¹/(J:ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      simpa only [Rat.cast_natCast,symmetricFolds] using QuantitativeHolomorphic.regular_terminal_fold_truncation_bound
        (level_pos (hQ:=hQ) hN i) (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
        (cell P.ε j) (highStrip P.ε)
        P.epsilon_pos (residueQ_nonneg _ d) (residueQ_le_one _ d)
        (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le)
        (fun _ hz => hz.1) ht z J hJ
    _ = _ := by simp [primitiveTerminalTailCost]; ring

def rowLowTailCost : AugIndex N (S:Set ℕ) Q → ℝ
  | Sum.inl i => primitiveLowTailCost i
  | Sum.inr _ => 0

def rowTerminalTailCost (P : Parameters A) : AugIndex N (S:Set ℕ) Q → ℝ
  | Sum.inl i => primitiveTerminalTailCost A P i
  | Sum.inr _ => 0

def lowTailConstant : ℝ :=
  ∑j : Fin Q,∑i∈(A.coeff j).support,|(A.coeff j i:ℝ)| * rowLowTailCost i

def terminalTailConstant (P : Parameters A) : ℝ :=
  ∑j : Fin Q,∑i∈(A.coeff j).support,|(A.coeff j i:ℝ)| * rowTerminalTailCost A P i

variable (hS : ∀p∈S,p.Prime)

theorem rowLow_holomorphic_error (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1)
    (j : Fin Q) {t : ℕ} (ht : 1≤t) (J : ℕ) (hJ : 0<J) (m : ℕ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖QuantitativeArithmeticRetainedCertificateOperators.rowLow A hS hN P χ β j t m i-
      holomorphicSum (rowLowExpression A hS hN P χ β j t (symmetricFolds J) i) m‖≤P.ρ^(t-1)*rowLowTailCost i/(J:ℝ) := by
  cases i with
  | inl i =>
    simpa only [rowLowExpression,holomorphicSum_scale,QuantitativeArithmeticRetainedCertificateOperators.rowLow,rowLowTailCost,
      ← _root_.smul_sub (χ i.val.1) (QuantitativeArithmeticRetainedCertificateOperators.primitiveLow A hN P j i t m) (holomorphicSum (primitiveLowExpression A hN P j i t (symmetricFolds J)) m),norm_smul,hχ i.val.1 i.property.1,one_mul] using
      primitiveLow_holomorphic_error A hN P j i ht J hJ m
  | inr i =>
    simp only [rowLowExpression,QuantitativeArithmeticRetainedCertificateOperators.rowLow,rowLowTailCost,
      retainedLow_holomorphic,sub_self,norm_zero,mul_zero,zero_div,le_refl]

/-- Explicit inverse-cutoff error for the actual mixed certificate. -/
theorem low_holomorphic_error (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1)
    {t : ℕ} (ht : 1≤t) (J : ℕ) (hJ : 0<J) (m : ℕ) :
    ‖QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P χ β t m-
      holomorphicSum (lowExpression A hS hN P χ β t (symmetricFolds J)) m‖≤P.ρ^(t-1)*lowTailConstant A/(J:ℝ) := by
  simp only [lowExpression,holomorphicSum_sumExpressions,holomorphicSum_scale,QuantitativeArithmeticRetainedCertificateOperators.low]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [lowTailConstant]
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  rw [← _root_.smul_sub (A.coeff j i : ℂ) (QuantitativeArithmeticRetainedCertificateOperators.rowLow A hS hN P χ β j t m i) (holomorphicSum (rowLowExpression A hS hN P χ β j t (symmetricFolds J) i) m),norm_smul,Complex.norm_ratCast]
  have hh := mul_le_mul_of_nonneg_left
    (rowLow_holomorphic_error A hS hN P χ β hχ j ht J hJ m i) (abs_nonneg (A.coeff j i:ℝ))
  convert hh using 1
  ring

theorem rowLow_regular_error (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1)
    (j : Fin Q) {t : ℕ} (ht : 1≤t) (J : ℕ) (hJ : 0<J) (z : ℍ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖QuantitativeArithmeticRetainedRegularOperators.rowLow A hS hN P χ β j t z i-
      regularSum (rowLowExpression A hS hN P χ β j t (symmetricFolds J) i) z‖≤P.ρ^(t-1)*rowLowTailCost i/(J:ℝ) := by
  cases i with
  | inl i =>
    simpa only [rowLowExpression,regularSum_scale,QuantitativeArithmeticRetainedRegularOperators.rowLow,rowLowTailCost,
      ← _root_.smul_sub (χ i.val.1) (QuantitativeArithmeticRetainedRegularOperators.primitiveLow A hN P j i t z) (regularSum (primitiveLowExpression A hN P j i t (symmetricFolds J)) z),norm_smul,hχ i.val.1 i.property.1,one_mul] using
      primitiveLow_regular_error A hN P j i ht J hJ z
  | inr i =>
    simp only [rowLowExpression,QuantitativeArithmeticRetainedRegularOperators.rowLow,rowLowTailCost,
      retainedLow_regular,regularSum_scale,sub_self,norm_zero,mul_zero,zero_div,le_refl]

/-- Explicit inverse-cutoff error for the actual mixed certificate. -/
theorem low_regular_error (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1)
    {t : ℕ} (ht : 1≤t) (J : ℕ) (hJ : 0<J) (z : ℍ) :
    ‖QuantitativeArithmeticRetainedRegularOperators.low A hS hN P χ β t z-
      regularSum (lowExpression A hS hN P χ β t (symmetricFolds J)) z‖≤P.ρ^(t-1)*lowTailConstant A/(J:ℝ) := by
  simp only [lowExpression,regularSum_sumExpressions,regularSum_scale,QuantitativeArithmeticRetainedRegularOperators.low]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [lowTailConstant]
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  rw [← _root_.smul_sub (A.coeff j i : ℂ) (QuantitativeArithmeticRetainedRegularOperators.rowLow A hS hN P χ β j t z i) (regularSum (rowLowExpression A hS hN P χ β j t (symmetricFolds J) i) z),norm_smul,Complex.norm_ratCast]
  have hh := mul_le_mul_of_nonneg_left
    (rowLow_regular_error A hS hN P χ β hχ j ht J hJ z i) (abs_nonneg (A.coeff j i:ℝ))
  convert hh using 1
  ring

theorem rowTerminal_holomorphic_error (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1)
    (j : Fin Q) {t : ℕ} (ht : 2≤t) (J : ℕ) (hJ : 0<J) (m : ℕ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖QuantitativeArithmeticRetainedCertificateOperators.rowTerminal A hS hN P χ β j ht m i-
      holomorphicSum (rowTerminalExpression A hS hN P χ β j ht (symmetricFolds J) i) m‖≤rowTerminalTailCost A P i/(J:ℝ) := by
  cases i with
  | inl i =>
    simpa only [rowTerminalExpression,holomorphicSum_scale,QuantitativeArithmeticRetainedCertificateOperators.rowTerminal,rowTerminalTailCost,
      ← _root_.smul_sub (χ i.val.1) (QuantitativeArithmeticRetainedCertificateOperators.primitiveTerminal A hN P j i ht m) (holomorphicSum (primitiveTerminalExpression A hN P j i ht (symmetricFolds J)) m),norm_smul,hχ i.val.1 i.property.1,one_mul] using
      primitiveTerminal_holomorphic_error A hN P j i ht J hJ m
  | inr i =>
    simp only [rowTerminalExpression,QuantitativeArithmeticRetainedCertificateOperators.rowTerminal,rowTerminalTailCost,
      retainedTerminal_holomorphic,sub_self,norm_zero,zero_div,le_refl]

/-- Explicit inverse-cutoff error for the actual mixed certificate. -/
theorem terminal_holomorphic_error (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1)
    {t : ℕ} (ht : 2≤t) (J : ℕ) (hJ : 0<J) (m : ℕ) :
    ‖QuantitativeArithmeticRetainedCertificateOperators.terminal A hS hN P χ β ht m-
      holomorphicSum (terminalExpression A hS hN P χ β ht (symmetricFolds J)) m‖≤terminalTailConstant A P/(J:ℝ) := by
  simp only [terminalExpression,holomorphicSum_sumExpressions,holomorphicSum_scale,QuantitativeArithmeticRetainedCertificateOperators.terminal]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [terminalTailConstant]
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  rw [← _root_.smul_sub (A.coeff j i : ℂ) (QuantitativeArithmeticRetainedCertificateOperators.rowTerminal A hS hN P χ β j ht m i) (holomorphicSum (rowTerminalExpression A hS hN P χ β j ht (symmetricFolds J) i) m),norm_smul,Complex.norm_ratCast]
  have hh := mul_le_mul_of_nonneg_left
    (rowTerminal_holomorphic_error A hS hN P χ β hχ j ht J hJ m i) (abs_nonneg (A.coeff j i:ℝ))
  convert hh using 1
  ring

theorem rowTerminal_regular_error (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1)
    (j : Fin Q) {t : ℕ} (ht : 2≤t) (J : ℕ) (hJ : 0<J) (z : ℍ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖QuantitativeArithmeticRetainedRegularOperators.rowTerminal A hS hN P χ β j ht z i-
      regularSum (rowTerminalExpression A hS hN P χ β j ht (symmetricFolds J) i) z‖≤rowTerminalTailCost A P i/(J:ℝ) := by
  cases i with
  | inl i =>
    simpa only [rowTerminalExpression,regularSum_scale,QuantitativeArithmeticRetainedRegularOperators.rowTerminal,rowTerminalTailCost,
      ← _root_.smul_sub (χ i.val.1) (QuantitativeArithmeticRetainedRegularOperators.primitiveTerminal A hN P j i ht z) (regularSum (primitiveTerminalExpression A hN P j i ht (symmetricFolds J)) z),norm_smul,hχ i.val.1 i.property.1,one_mul] using
      primitiveTerminal_regular_error A hN P j i ht J hJ z
  | inr i =>
    simp only [rowTerminalExpression,QuantitativeArithmeticRetainedRegularOperators.rowTerminal,rowTerminalTailCost,
      retainedTerminal_regular,regularSum_scale,sub_self,norm_zero,zero_div,le_refl]

/-- Explicit inverse-cutoff error for the actual mixed certificate. -/
theorem terminal_regular_error (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (hχ : ∀q,q∣Q → ‖χ q‖=1)
    {t : ℕ} (ht : 2≤t) (J : ℕ) (hJ : 0<J) (z : ℍ) :
    ‖QuantitativeArithmeticRetainedRegularOperators.terminal A hS hN P χ β ht z-
      regularSum (terminalExpression A hS hN P χ β ht (symmetricFolds J)) z‖≤terminalTailConstant A P/(J:ℝ) := by
  simp only [terminalExpression,regularSum_sumExpressions,regularSum_scale,QuantitativeArithmeticRetainedRegularOperators.terminal]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [terminalTailConstant]
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  rw [← _root_.smul_sub (A.coeff j i : ℂ) (QuantitativeArithmeticRetainedRegularOperators.rowTerminal A hS hN P χ β j ht z i) (regularSum (rowTerminalExpression A hS hN P χ β j ht (symmetricFolds J) i) z),norm_smul,Complex.norm_ratCast]
  have hh := mul_le_mul_of_nonneg_left
    (rowTerminal_regular_error A hS hN P χ β hχ j ht J hJ z i) (abs_nonneg (A.coeff j i:ℝ))
  convert hh using 1
  ring

#print axioms low_holomorphic_error
#print axioms low_regular_error
#print axioms terminal_holomorphic_error
#print axioms terminal_regular_error

end QuantitativeArithmeticRetainedFiniteExpressions
