module

public import QuantitativeArithmeticRetainedRegularOperatorsV1
public import AsymptoticRegularFoldedSupportV1
public import AsymptoticOrbitRegionV1
public import AsymptoticNeumannReconstructionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedRegularExtension

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap SpanningIntegerRows
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedRegularOperators
open QuantitativeArithmeticRetainedCertificateOperators (cell cell_measurable shift terminalConstant)
open AsymptoticCertificateBranches (residues)
open AsymptoticCertificateOperators (lowStrip highStrip lowStrip_measurable highStrip_measurable)
open AsymptoticRegularFoldedLow (Space)
open AsymptoticFiniteBranch (regular)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
variable (hS : ∀ p∈S,p.Prime)

def highProjection (P : Parameters A) (z : ℍ) : Space →L[ℂ] Space :=
  AsymptoticOrbitDiagonal.corner (highStrip P.ε) z

theorem branch_high_zero (P : Parameters A) (b : AsymptoticFiniteBranch.Branch)
    (hb : ∀ w∈highStrip P.ε,b.coefficient w=0) (z : ℍ) (f : Space) :
    highProjection A P z (regular b z f)=0 := by
  apply (AsymptoticOrbitRegion.corner_eq_zero_iff _ _ _).mpr
  intro g hg
  change b.coefficient (g • z)*f (b.label*g)=0
  rw [hb _ hg,zero_mul]

theorem high_rowLow_zero (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (j : Fin Q) {t : ℕ} (ht : 1≤t) (i : AugIndex N (S:Set ℕ) Q) (z : ℍ) (f : Space) :
    highProjection A P z (rowLow A hS hN P χ β j t z i f)=0 := by
  classical
  cases i with
  | inl i =>
    have hd (d : residues i.val.1) : highProjection A P z
        (AsymptoticRegularFoldedLow.operator (level_pos (hQ:=hQ) hN i)
          (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1) (cell P.ε j) (lowStrip P.ε)
          P.rho_pos.le
          (residueQ_nonneg _ d) (residueQ_le_one _ d)
          (fun _ hz => hz.1) t z f)=0 := by
      apply (AsymptoticOrbitRegion.corner_eq_zero_iff _ _ _).mpr
      intro g hg
      apply AsymptoticRegularFoldedLow.operator_zero_off_source (level_pos (hQ:=hQ) hN i)
        (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1) (cell P.ε j) (lowStrip P.ε)
        P.rho_pos.le
        (residueQ_nonneg _ d) (residueQ_le_one _ d)
        (fun _ hz => hz.1) ht z f g
      intro hc
      exact (not_lt_of_ge (show P.ε≤(g • z).im from hg.2)) (show (g • z).im<P.ε from hc.2)
    simp only [rowLow,primitiveLow,_root_.smul_apply,_root_.sum_apply,map_sum,map_smul,
      hd,Finset.sum_const_zero,smul_zero]
  | inr i =>
    have hn (n : ℤ) : highProjection A P z
        (regular (QuantitativeArithmeticRetainedDilationBranches.lowBranch
          (i.1.val:ℚ) ((i.1.val:ℚ)*shiftQ j i.2) (retained_pos hS i.1)
          (cell_measurable P.ε j) (lowStrip_measurable P.ε) t n) z f)=0 := by
      apply branch_high_zero A P
      intro w hw
      have hc : w∉cell P.ε j := fun hc =>
        (not_lt_of_ge (show P.ε≤w.im from hw.2)) (show w.im<P.ε from hc.2)
      have hreg : w∉QuantitativeArithmeticRetainedDilationOperator.region
          (((i.1.val:ℚ):ℝ)) ((((i.1.val:ℚ)*shiftQ j i.2):ℚ):ℝ)
          (QuantitativeArithmeticRetainedDilationBranches.real_positive (retained_pos hS i.1))
          (cell P.ε j) (lowStrip P.ε) n := fun h => hc h.1
      simp only [QuantitativeArithmeticRetainedDilationBranches.lowBranch,
        AsymptoticFiniteBranch.scale,QuantitativeArithmeticRetainedDilationBranches.branch,
        QuantitativeArithmeticRetainedDilationOperator.coefficient,Set.indicator_of_notMem hreg,mul_zero]
    simp only [rowLow,retainedLow,_root_.smul_apply,_root_.sum_apply,map_sum,map_smul,
      hn,Finset.sum_const_zero,smul_zero]

theorem high_low_zero (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 1≤t) (z : ℍ) (f : Space) :
    highProjection A P z (low A hS hN P χ β t z f)=0 := by
  simp only [low,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    high_rowLow_zero A hS hN P χ β _ ht,smul_zero,Finset.sum_const_zero]

theorem high_rowTerminal_zero (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (j : Fin Q) {t : ℕ} (ht : 2≤t) (i : AugIndex N (S:Set ℕ) Q) (z : ℍ) (f : Space) :
    highProjection A P z (rowTerminal A hS hN P χ β j ht z i f)=0 := by
  classical
  cases i with
  | inl i =>
    have hd (d : residues i.val.1) : highProjection A P z
        (AsymptoticRegularFoldedTerminal.operator (level_pos (hQ:=hQ) hN i)
          (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1) (cell P.ε j) (highStrip P.ε)
          P.epsilon_pos
          (residueQ_nonneg _ d) (residueQ_le_one _ d)
          (fun w hw => show w.im≤P.ε from (show w.im<P.ε from hw.2).le) (fun _ hz => hz.1) ht z f)=0 := by
      apply (AsymptoticOrbitRegion.corner_eq_zero_iff _ _ _).mpr
      intro g hg
      apply AsymptoticRegularFoldedTerminal.operator_zero_off_source (level_pos (hQ:=hQ) hN i)
        (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1) (cell P.ε j) (highStrip P.ε)
        P.epsilon_pos
        (residueQ_nonneg _ d) (residueQ_le_one _ d)
        (fun w hw => show w.im≤P.ε from (show w.im<P.ε from hw.2).le) (fun _ hz => hz.1) ht z f g
      intro hc
      exact (not_lt_of_ge (show P.ε≤(g • z).im from hg.2)) (show (g • z).im<P.ε from hc.2)
    simp only [rowTerminal,primitiveTerminal,_root_.smul_apply,_root_.sum_apply,map_sum,map_smul,
      hd,Finset.sum_const_zero,smul_zero]
  | inr i =>
    have hn (n : ℤ) : highProjection A P z
        (regular (QuantitativeArithmeticRetainedDilationBranches.terminalBranch
          (i.1.val:ℚ) ((i.1.val:ℚ)*shiftQ j i.2) (retained_pos hS i.1)
          (cell_measurable P.ε j) (highStrip_measurable P.ε) P.ε P.epsilon_pos t n) z f)=0 := by
      apply branch_high_zero A P
      intro w hw
      have hc : w∉cell P.ε j := fun hc =>
        (not_lt_of_ge (show P.ε≤w.im from hw.2)) (show w.im<P.ε from hc.2)
      have hreg : w∉QuantitativeArithmeticRetainedDilationOperator.region
          (((i.1.val:ℚ):ℝ)) ((((i.1.val:ℚ)*shiftQ j i.2):ℚ):ℝ)
          (QuantitativeArithmeticRetainedDilationBranches.real_positive (retained_pos hS i.1))
          (cell P.ε j) (highStrip P.ε) n := fun h => hc h.1
      simp only [QuantitativeArithmeticRetainedDilationBranches.terminalBranch,
        QuantitativeArithmeticRetainedDilationBranches.branch,
        QuantitativeArithmeticRetainedDilationOperator.coefficient,Set.indicator_of_notMem hreg,mul_zero]
    simp only [rowTerminal,retainedTerminal,_root_.smul_apply,_root_.sum_apply,map_sum,map_smul,
      hn,Finset.sum_const_zero,smul_zero]

theorem high_terminal_zero (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) (f : Space) :
    highProjection A P z (terminal A hS hN P χ β ht z f)=0 := by
  simp only [terminal,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    high_rowTerminal_zero A hS hN P χ β _ ht,smul_zero,Finset.sum_const_zero]

/-- Actual regular terminal corner, with its induced complete Hilbert norm. -/
abbrev TerminalSpace (P : Parameters A) (z : ℍ) :=
  AsymptoticOrbitRegion.Space (G:=AsymptoticRationalGroup.Group) (highStrip P.ε) z

/-- The same Neumann formula as in the holomorphic realization. -/
def extension (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) : TerminalSpace A P z →L[ℂ] Space :=
  AsymptoticReconstruction.low (low A hS hN P χ β t z)
    (((ContinuousLinearMap.id ℂ Space)+terminal A hS hN P χ β ht z).comp
      (TerminalSpace A P z).subtypeL)

theorem extension_terminal (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) (hK : ‖low A hS hN P χ β t z‖<1)
    (g : TerminalSpace A P z) :
    highProjection A P z (extension A hS hN P χ β ht z g)=(g:Space) := by
  have he := AsymptoticReconstruction.low_equation (low A hS hN P χ β t z)
    (((ContinuousLinearMap.id ℂ Space)+terminal A hS hN P χ β ht z).comp
      (TerminalSpace A P z).subtypeL) hK g
  change extension A hS hN P χ β ht z g=
    low A hS hN P χ β t z (extension A hS hN P χ β ht z g)+
      ((g:Space)+terminal A hS hN P χ β ht z (g:Space)) at he
  rw [he,map_add,high_low_zero A hS hN P χ β (by omega : 1≤t),zero_add,
    map_add,high_terminal_zero,add_zero]
  exact (AsymptoticOrbitRegion.mem_space _ _ _).mp g.property

theorem extension_norm_ge (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) (hK : ‖low A hS hN P χ β t z‖<1)
    (g : TerminalSpace A P z) : ‖g‖≤‖extension A hS hN P χ β ht z g‖ := by
  calc
    ‖g‖=‖highProjection A P z (extension A hS hN P χ β ht z g)‖ := by
      rw [extension_terminal A hS hN P χ β ht z hK g]
      rfl
    _ ≤ ‖highProjection A P z‖*‖extension A hS hN P χ β ht z g‖ := (highProjection A P z).le_opNorm _
    _ ≤ ‖extension A hS hN P χ β ht z g‖ := by
      simpa only [highProjection,one_mul] using mul_le_mul_of_nonneg_right
        (AsymptoticOrbitRegion.corner_norm_le (G:=AsymptoticRationalGroup.Group) (highStrip P.ε) z)
        (norm_nonneg (extension A hS hN P χ β ht z g))

theorem extension_norm_le (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hβ : ∀ p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (z : ℍ) (hK : ‖low A hS hN P χ β t z‖<1/2) :
    ‖extension A hS hN P χ β ht z‖≤2*(1+terminalConstant A P) := by
  have hK1 : ‖low A hS hN P χ β t z‖<1 := lt_trans hK (by norm_num)
  have hR := terminal_norm_le A hS hN P χ β hχ hβ ht z
  have hC : 0≤terminalConstant A P := (norm_nonneg _).trans hR
  have hinc : ‖(TerminalSpace A P z).subtypeL‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    simp
  have hB : ‖(((ContinuousLinearMap.id ℂ Space)+terminal A hS hN P χ β ht z).comp
      (TerminalSpace A P z).subtypeL)‖≤1+terminalConstant A P := by
    apply (opNorm_comp_le _ _).trans
    have hsum : ‖(ContinuousLinearMap.id ℂ Space)+terminal A hS hN P χ β ht z‖≤
        1+terminalConstant A P :=
      (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hR)
    simpa only [mul_one] using mul_le_mul hsum hinc (norm_nonneg (TerminalSpace A P z).subtypeL) (by positivity)
  apply (AsymptoticReconstruction.low_norm_le _ _ hK1).trans
  apply (div_le_iff₀ (by linarith : 0<1-‖low A hS hN P χ β t z‖)).mpr
  nlinarith

#print axioms high_low_zero
#print axioms high_terminal_zero
#print axioms extension_terminal
#print axioms extension_norm_ge
#print axioms extension_norm_le

end QuantitativeArithmeticRetainedRegularExtension
