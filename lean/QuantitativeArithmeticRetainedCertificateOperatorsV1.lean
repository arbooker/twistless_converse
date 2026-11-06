module

public import QuantitativeArithmeticRetainedGlobalHeightV1
public import QuantitativeArithmeticRetainedDilationOperatorV1
public import AsymptoticCertificateOperatorsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedCertificateOperators

open UpperHalfPlane MeasureTheory Set Filter ContinuousLinearMap SpanningIntegerRows
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open AsymptoticHyperbolicSlash
open AsymptoticCertificateOperators (lowStrip highStrip lowStrip_measurable highStrip_measurable)
open AsymptoticCertificateBranches (residues)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)

/-- Source cells are shared by the primitive and retained branches. -/
def cell (ε : ℝ) (j : Fin Q) : Set ℍ :=
  {z | (j:ℝ)/Q≤z.re ∧ z.re<((j:ℝ)+1)/Q}∩{z | z.im<ε}

theorem cell_measurable (ε : ℝ) (j : Fin Q) : MeasurableSet (cell ε j) :=
  (measurableSet_Ico.preimage continuous_re.measurable).inter
    (measurableSet_Iio.preimage continuous_im.measurable)

def shift (j : Fin Q) (u : ℤ) : ℝ := (u-(j:ℕ):ℝ)/Q

include hQ in
theorem row_level_pos (hN : 0<N) (i : RowIndex N Q) :
    (0:ℝ)<Nat.lcm N (i.val.1^2) := by
  exact_mod_cast Nat.lcm_pos hN (pow_pos (Nat.pos_of_dvd_of_pos i.property.1 hQ) 2)

theorem residue_nonneg (q : ℕ) (d : residues q) : (0:ℝ)≤(d.val:ℝ)/q := by positivity

theorem residue_lt_one (q : ℕ) (d : residues q) : (d.val:ℝ)/q<1 := by
  have hd : d.val<q := Finset.mem_range.mp (Finset.mem_filter.mp d.property).1
  exact (div_lt_one (by exact_mod_cast (show 0<q by omega))).mpr (by exact_mod_cast hd)

def primitiveLow (hN : 0<N) (P : Parameters A) (j : Fin Q) (i : RowIndex N Q)
    (t m : ℕ) : Space →L[ℂ] Space :=
  ∑ d : residues i.val.1,
    AsymptoticFoldedLow.operator (row_level_pos (hQ:=hQ) hN i) (shift j i.val.2) ((d.val:ℝ)/i.val.1)
      (cell_measurable P.ε j) (lowStrip_measurable P.ε) P.rho_pos.le
      (residue_nonneg _ d) (residue_lt_one _ d).le (fun _ hz => hz.1) t m

def primitiveTerminal (hN : 0<N) (P : Parameters A) (j : Fin Q) (i : RowIndex N Q)
    {t : ℕ} (ht : 2≤t) (m : ℕ) : Space →L[ℂ] Space :=
  ∑ d : residues i.val.1,
    AsymptoticFoldedTerminal.operator (row_level_pos (hQ:=hQ) hN i) (shift j i.val.2) ((d.val:ℝ)/i.val.1)
      (cell_measurable P.ε j) (highStrip_measurable P.ε) P.epsilon_pos
      (residue_nonneg _ d) (residue_lt_one _ d).le
      (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht m

def primitiveLowCost (P : Parameters A) (i : RowIndex N Q) : ℝ :=
  (residues i.val.1).card*(3*P.ρ+16/(Nat.lcm N (i.val.1^2):ℝ))

def primitiveTerminalCost (P : Parameters A) (i : RowIndex N Q) : ℝ :=
  (residues i.val.1).card*(3+4*((P.ε*(Nat.lcm N (i.val.1^2):ℝ))^2)⁻¹)

theorem primitiveLow_norm_le (hN : 0<N) (P : Parameters A) (j : Fin Q) (i : RowIndex N Q)
    {t : ℕ} (ht : 1≤t) (m : ℕ) :
    ‖primitiveLow A hN P j i t m‖≤P.ρ^(t-1)*primitiveLowCost A P i := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,
        P.ρ^(t-1)*(3*P.ρ+16/(Nat.lcm N (i.val.1^2):ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      exact AsymptoticFoldedLow.operator_norm_le (row_level_pos (hQ:=hQ) hN i) (shift j i.val.2)
        ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j) (lowStrip_measurable P.ε) P.rho_pos.le
        (residue_nonneg _ d) (residue_lt_one _ d).le (fun _ hz => hz.1) ht m
    _ = _ := by simp [primitiveLowCost]; ring

theorem primitiveTerminal_norm_le (hN : 0<N) (P : Parameters A) (j : Fin Q)
    (i : RowIndex N Q) {t : ℕ} (ht : 2≤t) (m : ℕ) :
    ‖primitiveTerminal A hN P j i ht m‖≤primitiveTerminalCost A P i := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : residues i.val.1,(3+4*((P.ε*(Nat.lcm N (i.val.1^2):ℝ))^2)⁻¹) := by
      apply Finset.sum_le_sum
      intro d _
      exact AsymptoticFoldedTerminal.operator_norm_le (row_level_pos (hQ:=hQ) hN i) (shift j i.val.2)
        ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j) (highStrip_measurable P.ε) P.epsilon_pos
        (residue_nonneg _ d) (residue_lt_one _ d).le
        (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht m
    _ = _ := by simp [primitiveTerminalCost]; ring

variable (hS : ∀ p∈S,p.Prime)

include hS in
theorem retained_pos (p : S) : (0:ℝ)<p.val := by exact_mod_cast (hS p.val p.property).pos

def rowLow (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ) (j : Fin Q)
    (t m : ℕ) : AugIndex N (S:Set ℕ) Q → Space →L[ℂ] Space
  | Sum.inl i => χ i.val.1 • primitiveLow A hN P j i t m
  | Sum.inr i =>
    QuantitativeArithmeticRetainedDilationOperator.weighted
      (i.1.val:ℝ) ((i.1.val:ℝ)*shift j i.2) (retained_pos hS i.1)
      (cell_measurable P.ε j) (lowStrip_measurable P.ε) (β i.1.val) t (2*m)

def rowTerminal (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ) (j : Fin Q)
    {t : ℕ} (ht : 2≤t) (m : ℕ) : AugIndex N (S:Set ℕ) Q → Space →L[ℂ] Space
  | Sum.inl i => χ i.val.1 • primitiveTerminal A hN P j i ht m
  | Sum.inr i =>
    QuantitativeArithmeticRetainedDilationOperator.terminal
      (i.1.val:ℝ) ((i.1.val:ℝ)*shift j i.2) (retained_pos hS i.1)
      (cell_measurable P.ε j) (highStrip_measurable P.ε) P.ε P.epsilon_pos (β i.1.val) t (2*m)

def rowLowCost (P : Parameters A) (j : Fin Q) : AugIndex N (S:Set ℕ) Q → ℝ
  | Sum.inl i => primitiveLowCost A P i
  | Sum.inr i => (QuantitativeArithmeticRetainedDilationOperator.folds
      (i.1.val:ℝ) ((i.1.val:ℝ)*shift j i.2)).card

def rowTerminalCost (P : Parameters A) (j : Fin Q) : AugIndex N (S:Set ℕ) Q → ℝ
  | Sum.inl i => primitiveTerminalCost A P i
  | Sum.inr i => (QuantitativeArithmeticRetainedDilationOperator.folds
      (i.1.val:ℝ) ((i.1.val:ℝ)*shift j i.2)).card

include hS in
theorem retained_inverse_le (P : Parameters A) (p : S) : (p.val:ℝ)⁻¹≤P.ρ := by
  have hp : (2:ℝ)≤p.val := by exact_mod_cast (hS p.val p.property).two_le
  exact (inv_anti₀ (by norm_num : (0:ℝ)<2) hp).trans (by simpa using P.rho_half)

theorem rowLow_norm_le (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hβ : ∀ p∈S,‖β p‖≤1)
    (j : Fin Q) {t : ℕ} (ht : 1≤t) (m : ℕ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖rowLow A hS hN P χ β j t m i‖≤P.ρ^(t-1)*rowLowCost A P j i := by
  cases i with
  | inl i =>
    simpa only [rowLow,rowLowCost,norm_smul,hχ i.val.1 i.property.1,one_mul] using
      primitiveLow_norm_le A hN P j i ht m
  | inr i =>
    apply (QuantitativeArithmeticRetainedDilationOperator.weighted_norm_le_rho
      (i.1.val:ℝ) ((i.1.val:ℝ)*shift j i.2) (retained_pos hS i.1)
      (cell_measurable P.ε j) (lowStrip_measurable P.ε) (hβ i.1.val i.1.property)
      (retained_inverse_le A hS P i.1) t (2*m)).trans
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one P.rho_pos.le P.rho_lt_one.le (Nat.sub_le _ _)) (Nat.cast_nonneg _)

theorem rowTerminal_norm_le (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hβ : ∀ p∈S,‖β p‖≤1)
    (j : Fin Q) {t : ℕ} (ht : 2≤t) (m : ℕ) (i : AugIndex N (S:Set ℕ) Q) :
    ‖rowTerminal A hS hN P χ β j ht m i‖≤rowTerminalCost A P j i := by
  cases i with
  | inl i =>
    simpa only [rowTerminal,rowTerminalCost,norm_smul,hχ i.val.1 i.property.1,one_mul] using
      primitiveTerminal_norm_le A hN P j i ht m
  | inr i =>
    exact QuantitativeArithmeticRetainedDilationOperator.terminal_norm_le
      (i.1.val:ℝ) ((i.1.val:ℝ)*shift j i.2) (retained_pos hS i.1)
      (cell_measurable P.ε j) (highStrip_measurable P.ε) P.ε P.epsilon_pos
      (hβ i.1.val i.1.property) t (2*m)

/-- The same rational coefficients used by pointwise reconstruction. -/
def low (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ) (t m : ℕ) : Space →L[ℂ] Space :=
  ∑ j : Fin Q, ∑ i∈(A.coeff j).support,
    (A.coeff j i:ℂ) • rowLow A hS hN P χ β j t m i

def terminal (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) : Space →L[ℂ] Space :=
  ∑ j : Fin Q, ∑ i∈(A.coeff j).support,
    (A.coeff j i:ℂ) • rowTerminal A hS hN P χ β j ht m i

def lowConstant (P : Parameters A) : ℝ :=
  ∑ j : Fin Q, ∑ i∈(A.coeff j).support, |(A.coeff j i:ℝ)| * rowLowCost A P j i

def terminalConstant (P : Parameters A) : ℝ :=
  ∑ j : Fin Q, ∑ i∈(A.coeff j).support, |(A.coeff j i:ℝ)| * rowTerminalCost A P j i

theorem low_norm_le (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hβ : ∀ p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 1≤t) (m : ℕ) :
    ‖low A hS hN P χ β t m‖≤P.ρ^(t-1)*lowConstant A P := by
  apply (norm_sum_le _ _).trans
  rw [lowConstant,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,Complex.norm_ratCast]
  have h := mul_le_mul_of_nonneg_left (rowLow_norm_le A hS hN P χ β hχ hβ j ht m i)
    (abs_nonneg (A.coeff j i:ℝ))
  convert h using 1
  ring

theorem terminal_norm_le (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hβ : ∀ p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (m : ℕ) :
    ‖terminal A hS hN P χ β ht m‖≤terminalConstant A P := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,Complex.norm_ratCast]
  exact mul_le_mul_of_nonneg_left (rowTerminal_norm_le A hS hN P χ β hχ hβ j ht m i)
    (abs_nonneg _)

/-- A single auxiliary exponent works for the full mixed certificate,
uniformly over every weight and permitted ramified sign pattern. -/
theorem contraction (hN : 0<N) (P : Parameters A) :
    ∃ s : ℕ, P.s≤s ∧ ∀ χ β : ℕ → ℂ,
      (∀ q,q∣Q → ‖χ q‖=1) → (∀ p∈S,‖β p‖≤1) → ∀ m : ℕ,
        ‖low A hS hN P χ β (s+3) m‖<1/2 := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one P.rho_pos.le P.rho_lt_one).mul_const
    (P.ρ^2*lowConstant A P)
  simp only [zero_mul] at h
  obtain ⟨n,hn⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  refine ⟨max n P.s,le_max_right _ _,fun χ β hχ hβ m => ?_⟩
  apply (low_norm_le A hS hN P χ β hχ hβ (by omega : 1≤max n P.s+3) m).trans_lt
  have hb := hn (max n P.s) (le_max_left _ _)
  convert hb using 1
  rw [show max n P.s+3-1=max n P.s+2 by omega,pow_add]
  ring

#print axioms primitiveLow_norm_le
#print axioms primitiveTerminal_norm_le
#print axioms rowLow_norm_le
#print axioms rowTerminal_norm_le
#print axioms low_norm_le
#print axioms terminal_norm_le
#print axioms contraction

end QuantitativeArithmeticRetainedCertificateOperators
