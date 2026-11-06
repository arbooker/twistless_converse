module

public import QuantitativeArithmeticRetainedFiniteExpressionsV1

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

section Uniform
variable {ι α E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
theorem uniform_constant (f : α → E) :
    TendstoUniformly (fun _I : Finset ℤ => f) f atTop := by
  intro u hu
  exact Filter.Eventually.of_forall (fun _ x => refl_mem_uniformity hu)

omit [NormedSpace ℂ E] in
theorem uniform_sum (s : Finset ι) (f : ι → Finset ℤ → α → E) (g : ι → α → E)
    (h : ∀i∈s,TendstoUniformly (f i) (g i) atTop) :
    TendstoUniformly (fun I x => ∑i∈s,f i I x) (fun x => ∑i∈s,g i x) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (uniform_constant (fun _ : α => (0:E)))
  | @insert i s hi ih =>
    have ha := h i (Finset.mem_insert_self i s)
    have hb := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    exact ha.add hb

theorem uniform_smul (c : ℂ) {f : Finset ℤ → α → E} {g : α → E}
    (h : TendstoUniformly f g atTop) :
    TendstoUniformly (fun I x => c • f I x) (fun x => c • g x) atTop :=
  (uniformContinuous_const_smul c).comp_tendstoUniformly h
end Uniform

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)

/-- The same finite folds converge uniformly over every weight. -/
theorem primitiveLow_holomorphic_uniform (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 1≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun m : ℕ =>
        holomorphicSum (primitiveLowExpression A hN P j i t I) m)
      (QuantitativeArithmeticRetainedCertificateOperators.primitiveLow A hN P j i t) atTop := by
  simp only [primitiveLowExpression,holomorphicSum_sumExpressions,holomorphicSum_ofFinset,
    holomorphic_lowFold]
  simp only [Rat.cast_natCast,Rat.cast_div,shiftQ_cast]
  apply uniform_sum
  intro d _
  exact AsymptoticFoldedLow.finite_folds_tendstoUniformly
    (QuantitativeArithmeticRetainedCertificateOperators.row_level_pos (hQ:=hQ) hN i)
    (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
    (lowStrip_measurable P.ε) P.rho_pos.le
    (residue_nonneg _ d) (residue_lt_one _ d).le
    (fun _ hz => hz.1) ht

/-- The same finite folds converge uniformly over every regular root. -/
theorem primitiveLow_regular_uniform (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 1≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun z : ℍ =>
        regularSum (primitiveLowExpression A hN P j i t I) z)
      (QuantitativeArithmeticRetainedRegularOperators.primitiveLow A hN P j i t) atTop := by
  simp only [primitiveLowExpression,regularSum_sumExpressions,regularSum_ofFinset,
    regular_lowFold]
  apply uniform_sum
  intro d _
  exact AsymptoticRegularFoldedLow.finite_folds_tendstoUniformly
    (level_pos (hQ:=hQ) hN i) (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
    (cell P.ε j) (lowStrip P.ε)
    P.rho_pos.le (residueQ_nonneg _ d) (residueQ_le_one _ d)
    (fun _ hz => hz.1) ht

/-- The same finite folds converge uniformly over every weight. -/
theorem primitiveTerminal_holomorphic_uniform (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 2≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun m : ℕ =>
        holomorphicSum (primitiveTerminalExpression A hN P j i ht I) m)
      (QuantitativeArithmeticRetainedCertificateOperators.primitiveTerminal A hN P j i ht) atTop := by
  simp only [primitiveTerminalExpression,holomorphicSum_sumExpressions,holomorphicSum_ofFinset,
    holomorphic_terminalFold]
  simp only [Rat.cast_natCast,Rat.cast_div,shiftQ_cast]
  apply uniform_sum
  intro d _
  exact AsymptoticFoldedTerminal.finite_folds_tendstoUniformly
    (QuantitativeArithmeticRetainedCertificateOperators.row_level_pos (hQ:=hQ) hN i)
    (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
    (highStrip_measurable P.ε) P.epsilon_pos
    (residue_nonneg _ d) (residue_lt_one _ d).le
    (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le)
    (fun _ hz => hz.1) ht

/-- The same finite folds converge uniformly over every regular root. -/
theorem primitiveTerminal_regular_uniform (hN : 0<N) (P : Parameters A)
    (j : Fin Q) (i : RowIndex N Q) {t : ℕ} (ht : 2≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun z : ℍ =>
        regularSum (primitiveTerminalExpression A hN P j i ht I) z)
      (QuantitativeArithmeticRetainedRegularOperators.primitiveTerminal A hN P j i ht) atTop := by
  simp only [primitiveTerminalExpression,regularSum_sumExpressions,regularSum_ofFinset,
    regular_terminalFold]
  apply uniform_sum
  intro d _
  exact AsymptoticRegularFoldedTerminal.finite_folds_tendstoUniformly
    (level_pos (hQ:=hQ) hN i) (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
    (cell P.ε j) (highStrip P.ε)
    P.epsilon_pos (residueQ_nonneg _ d) (residueQ_le_one _ d)
    (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le)
    (fun _ hz => hz.1) ht

variable (hS : ∀p∈S,p.Prime)

theorem rowLow_holomorphic_uniform (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (j : Fin Q) {t : ℕ} (ht : 1≤t) (i : AugIndex N (S:Set ℕ) Q) :
    TendstoUniformly
      (fun I : Finset ℤ => fun m : ℕ =>
        holomorphicSum (rowLowExpression A hS hN P χ β j t I i) m)
      (fun m => QuantitativeArithmeticRetainedCertificateOperators.rowLow A hS hN P χ β j t m i) atTop := by
  cases i with
  | inl i =>
    simpa only [rowLowExpression,holomorphicSum_scale,QuantitativeArithmeticRetainedCertificateOperators.rowLow] using
      uniform_smul (χ i.val.1) (primitiveLow_holomorphic_uniform A hN P j i ht)
  | inr i =>
    simp only [rowLowExpression,QuantitativeArithmeticRetainedCertificateOperators.rowLow,retainedLow_holomorphic]
    exact uniform_constant _

/-- Common finite expressions approximate the actual mixed certificate
uniformly, retaining every complete-row affine branch exactly. -/
theorem low_holomorphic_uniform (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) {t : ℕ} (ht : 1≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun m : ℕ =>
        holomorphicSum (lowExpression A hS hN P χ β t I) m)
      (QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P χ β t) atTop := by
  simp only [lowExpression,holomorphicSum_sumExpressions,holomorphicSum_scale]
  apply uniform_sum
  intro j _
  apply uniform_sum
  intro i _
  exact uniform_smul (A.coeff j i:ℂ) (rowLow_holomorphic_uniform A hS hN P χ β j ht i)

theorem rowLow_regular_uniform (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (j : Fin Q) {t : ℕ} (ht : 1≤t) (i : AugIndex N (S:Set ℕ) Q) :
    TendstoUniformly
      (fun I : Finset ℤ => fun z : ℍ =>
        regularSum (rowLowExpression A hS hN P χ β j t I i) z)
      (fun z => QuantitativeArithmeticRetainedRegularOperators.rowLow A hS hN P χ β j t z i) atTop := by
  cases i with
  | inl i =>
    simpa only [rowLowExpression,regularSum_scale,QuantitativeArithmeticRetainedRegularOperators.rowLow] using
      uniform_smul (χ i.val.1) (primitiveLow_regular_uniform A hN P j i ht)
  | inr i =>
    simp only [rowLowExpression,QuantitativeArithmeticRetainedRegularOperators.rowLow,retainedLow_regular,regularSum_scale]
    exact uniform_constant _

/-- Common finite expressions approximate the actual mixed certificate
uniformly, retaining every complete-row affine branch exactly. -/
theorem low_regular_uniform (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) {t : ℕ} (ht : 1≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun z : ℍ =>
        regularSum (lowExpression A hS hN P χ β t I) z)
      (QuantitativeArithmeticRetainedRegularOperators.low A hS hN P χ β t) atTop := by
  simp only [lowExpression,regularSum_sumExpressions,regularSum_scale]
  apply uniform_sum
  intro j _
  apply uniform_sum
  intro i _
  exact uniform_smul (A.coeff j i:ℂ) (rowLow_regular_uniform A hS hN P χ β j ht i)

theorem rowTerminal_holomorphic_uniform (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (j : Fin Q) {t : ℕ} (ht : 2≤t) (i : AugIndex N (S:Set ℕ) Q) :
    TendstoUniformly
      (fun I : Finset ℤ => fun m : ℕ =>
        holomorphicSum (rowTerminalExpression A hS hN P χ β j ht I i) m)
      (fun m => QuantitativeArithmeticRetainedCertificateOperators.rowTerminal A hS hN P χ β j ht m i) atTop := by
  cases i with
  | inl i =>
    simpa only [rowTerminalExpression,holomorphicSum_scale,QuantitativeArithmeticRetainedCertificateOperators.rowTerminal] using
      uniform_smul (χ i.val.1) (primitiveTerminal_holomorphic_uniform A hN P j i ht)
  | inr i =>
    simp only [rowTerminalExpression,QuantitativeArithmeticRetainedCertificateOperators.rowTerminal,retainedTerminal_holomorphic]
    exact uniform_constant _

/-- Common finite expressions approximate the actual mixed certificate
uniformly, retaining every complete-row affine branch exactly. -/
theorem terminal_holomorphic_uniform (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) {t : ℕ} (ht : 2≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun m : ℕ =>
        holomorphicSum (terminalExpression A hS hN P χ β ht I) m)
      (QuantitativeArithmeticRetainedCertificateOperators.terminal A hS hN P χ β ht) atTop := by
  simp only [terminalExpression,holomorphicSum_sumExpressions,holomorphicSum_scale]
  apply uniform_sum
  intro j _
  apply uniform_sum
  intro i _
  exact uniform_smul (A.coeff j i:ℂ) (rowTerminal_holomorphic_uniform A hS hN P χ β j ht i)

theorem rowTerminal_regular_uniform (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) (j : Fin Q) {t : ℕ} (ht : 2≤t) (i : AugIndex N (S:Set ℕ) Q) :
    TendstoUniformly
      (fun I : Finset ℤ => fun z : ℍ =>
        regularSum (rowTerminalExpression A hS hN P χ β j ht I i) z)
      (fun z => QuantitativeArithmeticRetainedRegularOperators.rowTerminal A hS hN P χ β j ht z i) atTop := by
  cases i with
  | inl i =>
    simpa only [rowTerminalExpression,regularSum_scale,QuantitativeArithmeticRetainedRegularOperators.rowTerminal] using
      uniform_smul (χ i.val.1) (primitiveTerminal_regular_uniform A hN P j i ht)
  | inr i =>
    simp only [rowTerminalExpression,QuantitativeArithmeticRetainedRegularOperators.rowTerminal,retainedTerminal_regular,regularSum_scale]
    exact uniform_constant _

/-- Common finite expressions approximate the actual mixed certificate
uniformly, retaining every complete-row affine branch exactly. -/
theorem terminal_regular_uniform (hN : 0<N) (P : Parameters A)
    (χ β : ℕ → ℂ) {t : ℕ} (ht : 2≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun z : ℍ =>
        regularSum (terminalExpression A hS hN P χ β ht I) z)
      (QuantitativeArithmeticRetainedRegularOperators.terminal A hS hN P χ β ht) atTop := by
  simp only [terminalExpression,regularSum_sumExpressions,regularSum_scale]
  apply uniform_sum
  intro j _
  apply uniform_sum
  intro i _
  exact uniform_smul (A.coeff j i:ℂ) (rowTerminal_regular_uniform A hS hN P χ β j ht i)

#print axioms low_holomorphic_uniform
#print axioms low_regular_uniform
#print axioms terminal_holomorphic_uniform
#print axioms terminal_regular_uniform

end QuantitativeArithmeticRetainedFiniteExpressions
