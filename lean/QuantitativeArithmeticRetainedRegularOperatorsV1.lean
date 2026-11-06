module

public import QuantitativeArithmeticRetainedCertificateOperatorsV1
public import QuantitativeArithmeticRetainedDilationBranchesV1
public import AsymptoticRegularFoldedTerminalV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedRegularOperators

open UpperHalfPlane MeasureTheory Set Filter ContinuousLinearMap SpanningIntegerRows
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open AsymptoticCertificateBranches (residues)
open AsymptoticCertificateOperators (lowStrip highStrip lowStrip_measurable highStrip_measurable)
open QuantitativeArithmeticRetainedCertificateOperators
  (cell cell_measurable shift residue_nonneg residue_lt_one primitiveLowCost primitiveTerminalCost
   rowLowCost rowTerminalCost lowConstant terminalConstant retained_inverse_le)
open AsymptoticRegularFoldedLow (Space)
open AsymptoticFiniteBranch (regular)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)

def shiftQ (j : Fin Q) (u : ℤ) : ℚ := (u-(j:ℕ):ℚ)/Q

theorem shiftQ_cast (j : Fin Q) (u : ℤ) : (shiftQ j u:ℝ)=shift j u := by simp [shiftQ,shift]

include hQ in
theorem level_pos (hN : 0<N) (i : RowIndex N Q) : (0:ℚ)<Nat.lcm N (i.val.1^2) := by
  exact_mod_cast Nat.lcm_pos hN (pow_pos (Nat.pos_of_dvd_of_pos i.property.1 hQ) 2)

theorem residueQ_nonneg (q : ℕ) (d : residues q) : (0:ℝ)≤((d.val:ℚ)/q:ℚ) := by positivity

theorem residueQ_le_one (q : ℕ) (d : residues q) : (((d.val:ℚ)/q:ℚ):ℝ)≤1 := by
  simpa only [Rat.cast_div,Rat.cast_natCast] using (residue_lt_one q d).le

def primitiveLow (hN : 0<N) (P : Parameters A) (j : Fin Q) (i : RowIndex N Q)
    (t : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  ∑ d : residues i.val.1,
    AsymptoticRegularFoldedLow.operator (level_pos (hQ:=hQ) hN i)
      (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1) (cell P.ε j) (lowStrip P.ε) P.rho_pos.le
      (residueQ_nonneg _ d) (residueQ_le_one _ d) (fun _ hz => hz.1) t z

def primitiveTerminal (hN : 0<N) (P : Parameters A) (j : Fin Q) (i : RowIndex N Q)
    {t : ℕ} (ht : 2≤t) (z : ℍ) : Space →L[ℂ] Space :=
  ∑ d : residues i.val.1,
    AsymptoticRegularFoldedTerminal.operator (level_pos (hQ:=hQ) hN i)
      (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1) (cell P.ε j) (highStrip P.ε) P.epsilon_pos
      (residueQ_nonneg _ d) (residueQ_le_one _ d)
      (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht z

theorem primitiveLow_norm_le (hN : 0<N) (P : Parameters A) (j : Fin Q) (i : RowIndex N Q)
    {t : ℕ} (ht : 1≤t) (z : ℍ) :
    ‖primitiveLow A hN P j i t z‖≤P.ρ^(t-1)*primitiveLowCost A P i := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,
        P.ρ^(t-1)*(3*P.ρ+16/(Nat.lcm N (i.val.1^2):ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      simpa only [Rat.cast_natCast] using AsymptoticRegularFoldedLow.operator_norm_le
        (level_pos (hQ:=hQ) hN i) (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
        (cell P.ε j) (lowStrip P.ε) P.rho_pos.le
        (residueQ_nonneg _ d) (residueQ_le_one _ d) (fun _ hz => hz.1) ht z
    _ = _ := by simp [primitiveLowCost]; ring

theorem primitiveTerminal_norm_le (hN : 0<N) (P : Parameters A) (j : Fin Q)
    (i : RowIndex N Q) {t : ℕ} (ht : 2≤t) (z : ℍ) :
    ‖primitiveTerminal A hN P j i ht z‖≤primitiveTerminalCost A P i := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,(3+4*((P.ε*(Nat.lcm N (i.val.1^2):ℝ))^2)⁻¹) := by
      apply Finset.sum_le_sum
      intro d _
      simpa only [Rat.cast_natCast] using AsymptoticRegularFoldedTerminal.operator_norm_le
        (level_pos (hQ:=hQ) hN i) (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
        (cell P.ε j) (highStrip P.ε) P.epsilon_pos (residueQ_nonneg _ d) (residueQ_le_one _ d)
        (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht z
    _ = _ := by simp [primitiveTerminalCost]; ring

variable (hS : ∀ p∈S,p.Prime)

include hS in
theorem retained_pos (p : S) : (0:ℚ)<p.val := by exact_mod_cast (hS p.val p.property).pos

def retainedLow (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ) (t : ℕ) (z : ℍ) :
    Space →L[ℂ] Space :=
  ∑ n∈QuantitativeArithmeticRetainedDilationOperator.folds (p.val:ℝ) ((p.val:ℝ)*shift j u),
    regular (QuantitativeArithmeticRetainedDilationBranches.lowBranch
      (p.val:ℚ) ((p.val:ℚ)*shiftQ j u) (retained_pos hS p)
      (cell_measurable P.ε j) (lowStrip_measurable P.ε) t n) z

def retainedTerminal (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ) (t : ℕ) (z : ℍ) :
    Space →L[ℂ] Space :=
  ∑ n∈QuantitativeArithmeticRetainedDilationOperator.folds (p.val:ℝ) ((p.val:ℝ)*shift j u),
    regular (QuantitativeArithmeticRetainedDilationBranches.terminalBranch
      (p.val:ℚ) ((p.val:ℚ)*shiftQ j u) (retained_pos hS p)
      (cell_measurable P.ε j) (highStrip_measurable P.ε) P.ε P.epsilon_pos t n) z

def rowLow (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ) (j : Fin Q)
    (t : ℕ) (z : ℍ) : AugIndex N (S:Set ℕ) Q → Space →L[ℂ] Space
  | Sum.inl i => χ i.val.1 • primitiveLow A hN P j i t z
  | Sum.inr i => β i.1.val • retainedLow A hS P j i.1 i.2 t z

def rowTerminal (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ) (j : Fin Q)
    {t : ℕ} (ht : 2≤t) (z : ℍ) : AugIndex N (S:Set ℕ) Q → Space →L[ℂ] Space
  | Sum.inl i => χ i.val.1 • primitiveTerminal A hN P j i ht z
  | Sum.inr i => β i.1.val • retainedTerminal A hS P j i.1 i.2 t z

theorem retainedLow_norm_le (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ)
    (t : ℕ) (z : ℍ) : ‖retainedLow A hS P j p u t z‖≤
      (p.val:ℝ)⁻¹^t*(QuantitativeArithmeticRetainedDilationOperator.folds
        (p.val:ℝ) ((p.val:ℝ)*shift j u)).card := by
  simpa only [retainedLow,Rat.cast_natCast,Rat.cast_mul,shiftQ_cast] using
    QuantitativeArithmeticRetainedDilationBranches.regular_low_norm_le
      (p.val:ℚ) ((p.val:ℚ)*shiftQ j u) (retained_pos hS p)
      (cell_measurable P.ε j) (lowStrip_measurable P.ε) t z

theorem retainedTerminal_norm_le (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ)
    (t : ℕ) (z : ℍ) : ‖retainedTerminal A hS P j p u t z‖≤
      (QuantitativeArithmeticRetainedDilationOperator.folds (p.val:ℝ) ((p.val:ℝ)*shift j u)).card := by
  simpa only [retainedTerminal,Rat.cast_natCast,Rat.cast_mul,shiftQ_cast] using
    QuantitativeArithmeticRetainedDilationBranches.regular_terminal_norm_le
      (p.val:ℚ) ((p.val:ℚ)*shiftQ j u) (retained_pos hS p)
      (cell_measurable P.ε j) (highStrip_measurable P.ε) P.ε P.epsilon_pos t z

theorem rowLow_norm_le (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hβ : ∀ p∈S,‖β p‖≤1)
    (j : Fin Q) {t : ℕ} (ht : 1≤t) (z : ℍ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖rowLow A hS hN P χ β j t z i‖≤P.ρ^(t-1)*rowLowCost A P j i := by
  cases i with
  | inl i =>
    simpa only [rowLow,rowLowCost,norm_smul,hχ i.val.1 i.property.1,one_mul] using
      primitiveLow_norm_le A hN P j i ht z
  | inr i =>
    rw [rowLow,norm_smul]
    apply (mul_le_mul_of_nonneg_right (hβ i.1.val i.1.property) (norm_nonneg _)).trans
    rw [one_mul]
    apply (retainedLow_norm_le A hS P j i.1 i.2 t z).trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply (pow_le_pow_left₀ (by positivity) (retained_inverse_le A hS P i.1) t).trans
    exact pow_le_pow_of_le_one P.rho_pos.le P.rho_lt_one.le (Nat.sub_le _ _)

theorem rowTerminal_norm_le (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hβ : ∀ p∈S,‖β p‖≤1)
    (j : Fin Q) {t : ℕ} (ht : 2≤t) (z : ℍ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖rowTerminal A hS hN P χ β j ht z i‖≤rowTerminalCost A P j i := by
  cases i with
  | inl i =>
    simpa only [rowTerminal,rowTerminalCost,norm_smul,hχ i.val.1 i.property.1,one_mul] using
      primitiveTerminal_norm_le A hN P j i ht z
  | inr i =>
    rw [rowTerminal,norm_smul]
    apply (mul_le_mul_of_nonneg_right (hβ i.1.val i.1.property) (norm_nonneg _)).trans
    rw [one_mul]
    exact retainedTerminal_norm_le A hS P j i.1 i.2 t z

def low (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ) (t : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  ∑ j : Fin Q,∑ i∈(A.coeff j).support,(A.coeff j i:ℂ) • rowLow A hS hN P χ β j t z i

def terminal (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) : Space →L[ℂ] Space :=
  ∑ j : Fin Q,∑ i∈(A.coeff j).support,(A.coeff j i:ℂ) • rowTerminal A hS hN P χ β j ht z i

theorem low_norm_le (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hβ : ∀ p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 1≤t) (z : ℍ) :
    ‖low A hS hN P χ β t z‖≤P.ρ^(t-1)*lowConstant A P := by
  apply (norm_sum_le _ _).trans
  rw [lowConstant,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,Complex.norm_ratCast]
  have h := mul_le_mul_of_nonneg_left (rowLow_norm_le A hS hN P χ β hχ hβ j ht z i)
    (abs_nonneg (A.coeff j i:ℝ))
  convert h using 1
  ring

theorem terminal_norm_le (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hβ : ∀ p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (z : ℍ) :
    ‖terminal A hS hN P χ β ht z‖≤terminalConstant A P := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,Complex.norm_ratCast]
  exact mul_le_mul_of_nonneg_left (rowTerminal_norm_le A hS hN P χ β hχ hβ j ht z i) (abs_nonneg _)

/-- One exponent contracts both actual realizations for every sector,
weight and orbit root, with the very same certificate constant. -/
theorem common_contraction (hN : 0<N) (P : Parameters A) :
    ∃ s : ℕ,P.s≤s ∧ ∀ χ β : ℕ → ℂ,
      (∀ q,q∣Q → ‖χ q‖=1) → (∀ p∈S,‖β p‖≤1) →
        (∀ z,‖low A hS hN P χ β (s+3) z‖<1/2) ∧
        (∀ m,‖QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P χ β (s+3) m‖<1/2) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one P.rho_pos.le P.rho_lt_one).mul_const
    (P.ρ^2*lowConstant A P)
  simp only [zero_mul] at h
  obtain ⟨n,hn⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  let s := max n P.s
  have hb : P.ρ^(s+3-1)*lowConstant A P<1/2 := by
    have hsn := hn s (le_max_left _ _)
    convert hsn using 1
    rw [show s+3-1=s+2 by omega,pow_add]
    ring
  refine ⟨s,le_max_right _ _,fun χ β hχ hβ => ⟨?_,?_⟩⟩
  · intro z
    exact (low_norm_le A hS hN P χ β hχ hβ (by omega) z).trans_lt hb
  · intro m
    exact (QuantitativeArithmeticRetainedCertificateOperators.low_norm_le
      A hS hN P χ β hχ hβ (by omega) m).trans_lt hb

/-- Covariance and measurability are inherited from the literal rational
branch data; neither is an additional certificate hypothesis. -/
theorem branch_covariant (b : AsymptoticFiniteBranch.Branch) :
    AsymptoticRegularTrace.Covariant (regular b) :=
  AsymptoticOrbitBranch.operator_covariant b.label b.coefficient b.bound_nonneg b.norm_le

theorem branch_matrix_measurable (b : AsymptoticFiniteBranch.Branch)
    (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => AsymptoticRegularTrace.matrix (regular b z) g h) :=
  AsymptoticOrbitBranch.operator_matrix_measurable
    (fun g => (AsymptoticRationalBranches.action_continuous g).measurable)
    b.label b.coefficient b.bound_nonneg b.norm_le b.measurable g h

theorem low_covariant (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 1≤t) :
    AsymptoticRegularTrace.Covariant (low A hS hN P χ β t) := by
  unfold low
  apply AsymptoticRegularTrace.covariant_finsetSum
  intro j _
  apply AsymptoticRegularTrace.covariant_finsetSum
  intro i _
  apply AsymptoticRegularTrace.covariant_smul
  cases i with
  | inl i =>
    simp only [rowLow]
    apply AsymptoticRegularTrace.covariant_smul
    unfold primitiveLow
    apply AsymptoticRegularTrace.covariant_finsetSum
    intro d _
    exact AsymptoticRegularFoldedLow.operator_covariant (level_pos (hQ:=hQ) hN i)
      (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
      (cell P.ε j) (lowStrip P.ε) P.rho_pos.le
      (residueQ_nonneg _ d) (residueQ_le_one _ d)
      (fun _ hz => hz.1) ht
  | inr i =>
    simp only [rowLow]
    apply AsymptoticRegularTrace.covariant_smul
    unfold retainedLow
    apply AsymptoticRegularTrace.covariant_finsetSum
    intro n _
    exact branch_covariant _

theorem low_matrix_measurable (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 1≤t) (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => AsymptoticRegularTrace.matrix (low A hS hN P χ β t z) g h) := by
  unfold low
  apply AsymptoticRegularTrace.matrix_finsetSum_measurable
  intro j _ g h
  apply AsymptoticRegularTrace.matrix_finsetSum_measurable
  intro i _ g h
  apply AsymptoticRegularTrace.matrix_smul_measurable
  intro g h
  cases i with
  | inl i =>
    simp only [rowLow]
    apply AsymptoticRegularTrace.matrix_smul_measurable
    intro g h
    unfold primitiveLow
    apply AsymptoticRegularTrace.matrix_finsetSum_measurable
    intro d _ g h
    exact AsymptoticRegularFoldedLow.operator_matrix_measurable (level_pos (hQ:=hQ) hN i)
      (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
      (cell_measurable P.ε j) (lowStrip_measurable P.ε) P.rho_pos.le
      (residueQ_nonneg _ d) (residueQ_le_one _ d)
      (fun _ hz => hz.1) ht g h
  | inr i =>
    simp only [rowLow]
    apply AsymptoticRegularTrace.matrix_smul_measurable
    intro g h
    unfold retainedLow
    apply AsymptoticRegularTrace.matrix_finsetSum_measurable
    intro n _ g h
    exact branch_matrix_measurable _ g h

theorem terminal_covariant (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) :
    AsymptoticRegularTrace.Covariant (terminal A hS hN P χ β ht) := by
  unfold terminal
  apply AsymptoticRegularTrace.covariant_finsetSum
  intro j _
  apply AsymptoticRegularTrace.covariant_finsetSum
  intro i _
  apply AsymptoticRegularTrace.covariant_smul
  cases i with
  | inl i =>
    simp only [rowTerminal]
    apply AsymptoticRegularTrace.covariant_smul
    unfold primitiveTerminal
    apply AsymptoticRegularTrace.covariant_finsetSum
    intro d _
    exact AsymptoticRegularFoldedTerminal.operator_covariant (level_pos (hQ:=hQ) hN i)
      (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
      (cell P.ε j) (highStrip P.ε) P.epsilon_pos
      (residueQ_nonneg _ d) (residueQ_le_one _ d)
      (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht
  | inr i =>
    simp only [rowTerminal]
    apply AsymptoticRegularTrace.covariant_smul
    unfold retainedTerminal
    apply AsymptoticRegularTrace.covariant_finsetSum
    intro n _
    exact branch_covariant _

theorem terminal_matrix_measurable (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => AsymptoticRegularTrace.matrix (terminal A hS hN P χ β ht z) g h) := by
  unfold terminal
  apply AsymptoticRegularTrace.matrix_finsetSum_measurable
  intro j _ g h
  apply AsymptoticRegularTrace.matrix_finsetSum_measurable
  intro i _ g h
  apply AsymptoticRegularTrace.matrix_smul_measurable
  intro g h
  cases i with
  | inl i =>
    simp only [rowTerminal]
    apply AsymptoticRegularTrace.matrix_smul_measurable
    intro g h
    unfold primitiveTerminal
    apply AsymptoticRegularTrace.matrix_finsetSum_measurable
    intro d _ g h
    exact AsymptoticRegularFoldedTerminal.operator_matrix_measurable (level_pos (hQ:=hQ) hN i)
      (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1)
      (cell_measurable P.ε j) (highStrip_measurable P.ε) P.epsilon_pos
      (residueQ_nonneg _ d) (residueQ_le_one _ d)
      (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht g h
  | inr i =>
    simp only [rowTerminal]
    apply AsymptoticRegularTrace.matrix_smul_measurable
    intro g h
    unfold retainedTerminal
    apply AsymptoticRegularTrace.matrix_finsetSum_measurable
    intro n _ g h
    exact branch_matrix_measurable _ g h

#print axioms low_covariant
#print axioms low_matrix_measurable
#print axioms terminal_covariant
#print axioms terminal_matrix_measurable

#print axioms primitiveLow_norm_le
#print axioms primitiveTerminal_norm_le
#print axioms retainedLow_norm_le
#print axioms retainedTerminal_norm_le
#print axioms rowLow_norm_le
#print axioms rowTerminal_norm_le
#print axioms low_norm_le
#print axioms terminal_norm_le
#print axioms common_contraction

end QuantitativeArithmeticRetainedRegularOperators
