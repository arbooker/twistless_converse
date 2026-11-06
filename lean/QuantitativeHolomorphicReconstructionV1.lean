module

public import QuantitativeHolomorphicUniformTraceV1
public import QuantitativeHolomorphicFoldTailV1
public import AsymptoticFiniteBranchNormalV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open MeasureTheory UpperHalfPlane AsymptoticUnweightedKernel AsymptoticFiniteBranch
open AsymptoticRegularTrace FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns

/-- Exact coefficient mass for the same finite Neumann reconstruction
used by both actual realizations. -/
theorem expressionBound_neumann (K B : Expression) (n : ℕ) :
    expressionBound (neumannExpression K B n) =
      (∑ j ∈ Finset.range n, expressionBound K ^ j) * expressionBound B := by
  rw [neumannExpression, expressionBound_compose, expressionBound_geometric]

theorem length_neumannExpression (K B : Expression) (n : ℕ) :
    (neumannExpression K B n).length = (∑ j ∈ Finset.range n, K.length ^ j) * B.length := by
  rw [neumannExpression, length_composeExpression, length_geometricExpression]

theorem expressionBound_inversePolynomial (C : ℝ) (e : Expression) (n : ℕ) :
    expressionBound (inversePolynomialExpression C e n) =
      ‖(AsymptoticCoerciveNeumann.scale C : ℂ)‖ *
        ∑ j ∈ Finset.range n, (1 + ‖(AsymptoticCoerciveNeumann.scale C : ℂ)‖ * expressionBound e) ^ j := by
  rw [inversePolynomialExpression, expressionBound_scale, expressionBound_geometric]
  simp only [stepExpression, expressionBound_append, expressionBound_scale, norm_neg]
  simp [expressionBound, identity]

theorem length_inversePolynomialExpression (C : ℝ) (e : Expression) (n : ℕ) :
    (inversePolynomialExpression C e n).length = ∑ j ∈ Finset.range n, (1 + e.length) ^ j := by
  simp only [inversePolynomialExpression, scaleExpression, List.length_map, length_geometricExpression]
  simp [stepExpression, scaleExpression, Nat.add_comm]

theorem expressionBound_completedNormal (R G : Expression) (P : Branch) :
    expressionBound (completedNormalExpression R G P) =
      expressionBound R ^ 2 * (1 + expressionBound G) + (1 + P.bound) := by
  rw [completedNormalExpression, expressionBound_append, expressionBound_compose,
    expressionBound_adjoint, expressionBound_compose, expressionBound_append,
    expressionBound_append, expressionBound_scale]
  simp only [expressionBound, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    identity, norm_neg, norm_one, add_zero, one_mul]
  ring

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

theorem expressionBound_fullExpression (hN : 0 < N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) :
    expressionBound (fullExpression A hN P χ n I) =
      1 + (∑ j ∈ Finset.range n,
        expressionBound (lowExpression A hN P χ (P.s + 3) I) ^ j) *
        expressionBound (terminalExpression A hN P χ (by omega : 2 ≤ P.s + 3) I) := by
  rw [fullExpression, expressionBound_compose, expressionBound_append, expressionBound_neumann]
  simp [expressionBound, identity, corner]

theorem expressionBound_cutFullExpression (hN : 0 < N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) :
    expressionBound (cutFullExpression A hN P χ Y n I) =
      expressionBound (fullExpression A hN P χ n I) := by
  rw [cutFullExpression, expressionBound_compose, expressionBound_compose]
  simp [expressionBound, heightCorner, corner, weight]

/-- Explicit coefficient of the reciprocal symmetric fold cutoff. -/
def lowFoldTailConstant (P : Parameters A) (t : ℕ) : ℝ :=
  ∑ v : AsymptoticCertificateBranches.Index A,
    |(AsymptoticCertificateBranches.scalar A v : ℝ)| *
      (P.ρ ^ (t - 1) * (2 * (4 / AsymptoticCertificateBranches.level A v)))

def terminalFoldTailConstant (P : Parameters A) : ℝ :=
  ∑ v : AsymptoticCertificateBranches.Index A,
    |(AsymptoticCertificateBranches.scalar A v : ℝ)| *
      (2 * ((P.ε * AsymptoticCertificateBranches.level A v) ^ 2)⁻¹)

/-- The actual holomorphic certificate uses the explicit cutoff
`[-J,J]`; no qualitative choice of a finite fold set remains. -/
theorem physical_low_certificate_truncation_bound (hN : 0 < N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) {t : ℕ} (ht : 1 ≤ t)
    (m : ℕ) (J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticCertificateOperators.low A hN P χ t m -
      AsymptoticCertificateOperators.finiteLow A hN P χ t (Finset.Icc (-(J : ℤ)) J) m‖ ≤
        lowFoldTailConstant A P t / (J : ℝ) := by
  classical
  rw [AsymptoticCertificateOperators.low, AsymptoticCertificateOperators.finiteLow, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [lowFoldTailConstant, Finset.sum_div]
  apply Finset.sum_le_sum
  intro v _
  rw [← _root_.smul_sub (AsymptoticCertificateOperators.amplitude A χ v)
    (AsymptoticCertificateOperators.lowPart A hN P t m v)
    (AsymptoticCertificateOperators.finiteLowPart A hN P t m v (Finset.Icc (-(J : ℤ)) J)), norm_smul, AsymptoticCertificateOperators.amplitude_norm A χ hχ]
  have hb := physical_low_fold_truncation_bound
    (AsymptoticCertificateBranches.level_pos A hN v) (AsymptoticCertificateBranches.inputShift A v) (AsymptoticCertificateBranches.outputShift A v)
    (AsymptoticCertificateOperators.lowCell_measurable A P.ε v) (AsymptoticCertificateOperators.lowStrip_measurable P.ε) P.rho_pos.le
    (AsymptoticCertificateBranches.outputShift_nonneg A v) ((AsymptoticCertificateBranches.outputShift_lt_one A v).le)  (fun _ hz => hz.1) ht m J hJ
  have hb' := mul_le_mul_of_nonneg_left hb
    (abs_nonneg (AsymptoticCertificateBranches.scalar A v : ℝ))
  simpa only [AsymptoticCertificateOperators.lowPart, AsymptoticCertificateOperators.finiteLowPart,
    mul_div_assoc] using hb'

#print axioms physical_low_certificate_truncation_bound

/-- The actual holomorphic certificate uses the explicit cutoff
`[-J,J]`; no qualitative choice of a finite fold set remains. -/
theorem physical_terminal_certificate_truncation_bound (hN : 0 < N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) {t : ℕ} (ht : 2 ≤ t)
    (m : ℕ) (J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticCertificateOperators.terminal A hN P χ ht m -
      AsymptoticCertificateOperators.finiteTerminal A hN P χ ht (Finset.Icc (-(J : ℤ)) J) m‖ ≤
        terminalFoldTailConstant A P / (J : ℝ) := by
  classical
  rw [AsymptoticCertificateOperators.terminal, AsymptoticCertificateOperators.finiteTerminal, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [terminalFoldTailConstant, Finset.sum_div]
  apply Finset.sum_le_sum
  intro v _
  rw [← _root_.smul_sub (AsymptoticCertificateOperators.amplitude A χ v)
    (AsymptoticCertificateOperators.terminalPart A hN P ht m v)
    (AsymptoticCertificateOperators.finiteTerminalPart A hN P ht m v (Finset.Icc (-(J : ℤ)) J)), norm_smul, AsymptoticCertificateOperators.amplitude_norm A χ hχ]
  have hb := physical_terminal_fold_truncation_bound
    (AsymptoticCertificateBranches.level_pos A hN v) (AsymptoticCertificateBranches.inputShift A v) (AsymptoticCertificateBranches.outputShift A v)
    (AsymptoticCertificateOperators.lowCell_measurable A P.ε v) (AsymptoticCertificateOperators.highStrip_measurable P.ε) P.epsilon_pos
    (AsymptoticCertificateBranches.outputShift_nonneg A v) ((AsymptoticCertificateBranches.outputShift_lt_one A v).le) (fun _ hz => (show _ < P.ε from hz.2).le) (fun _ hz => hz.1) ht m J hJ
  have hb' := mul_le_mul_of_nonneg_left hb
    (abs_nonneg (AsymptoticCertificateBranches.scalar A v : ℝ))
  simpa only [AsymptoticCertificateOperators.terminalPart, AsymptoticCertificateOperators.finiteTerminalPart,
    mul_div_assoc] using hb'

#print axioms physical_terminal_certificate_truncation_bound

/-- The actual regular certificate uses the explicit cutoff
`[-J,J]`; no qualitative choice of a finite fold set remains. -/
theorem regular_low_certificate_truncation_bound (hN : 0 < N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) {t : ℕ} (ht : 1 ≤ t)
    (z : ℍ) (J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticRegularCertificate.low A hN P χ t z -
      AsymptoticRegularCertificate.finiteLow A hN P χ t (Finset.Icc (-(J : ℤ)) J) z‖ ≤
        lowFoldTailConstant A P t / (J : ℝ) := by
  classical
  rw [AsymptoticRegularCertificate.low, AsymptoticRegularCertificate.finiteLow, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [lowFoldTailConstant, Finset.sum_div]
  apply Finset.sum_le_sum
  intro v _
  rw [← _root_.smul_sub (AsymptoticCertificateOperators.amplitude A χ v)
    (AsymptoticRegularCertificate.lowPart A hN P t v z)
    (AsymptoticRegularCertificate.finiteLowPart A hN P t z v (Finset.Icc (-(J : ℤ)) J)), norm_smul, AsymptoticCertificateOperators.amplitude_norm A χ hχ]
  have hb := regular_low_fold_truncation_bound
    (AsymptoticRegularCertificate.levelQ_pos A hN v) (AsymptoticRegularCertificate.inputShiftQ A v) (AsymptoticRegularCertificate.outputShiftQ A v)
    (AsymptoticCertificateOperators.lowCell A P.ε v) (AsymptoticCertificateOperators.lowStrip P.ε) P.rho_pos.le
    (AsymptoticRegularCertificate.outputShiftQ_nonneg A v) (AsymptoticRegularCertificate.outputShiftQ_le_one A v)  (fun _ hz => hz.1) ht z J hJ
  have hb' := mul_le_mul_of_nonneg_left hb
    (abs_nonneg (AsymptoticCertificateBranches.scalar A v : ℝ))
  simpa only [AsymptoticRegularCertificate.lowPart, AsymptoticRegularCertificate.finiteLowPart,
    mul_div_assoc, AsymptoticRegularCertificate.levelQ_cast] using hb'

#print axioms regular_low_certificate_truncation_bound

/-- The actual regular certificate uses the explicit cutoff
`[-J,J]`; no qualitative choice of a finite fold set remains. -/
theorem regular_terminal_certificate_truncation_bound (hN : 0 < N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) {t : ℕ} (ht : 2 ≤ t)
    (z : ℍ) (J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticRegularCertificate.terminal A hN P χ ht z -
      AsymptoticRegularCertificate.finiteTerminal A hN P χ ht (Finset.Icc (-(J : ℤ)) J) z‖ ≤
        terminalFoldTailConstant A P / (J : ℝ) := by
  classical
  rw [AsymptoticRegularCertificate.terminal, AsymptoticRegularCertificate.finiteTerminal, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [terminalFoldTailConstant, Finset.sum_div]
  apply Finset.sum_le_sum
  intro v _
  rw [← _root_.smul_sub (AsymptoticCertificateOperators.amplitude A χ v)
    (AsymptoticRegularCertificate.terminalPart A hN P ht v z)
    (AsymptoticRegularCertificate.finiteTerminalPart A hN P ht z v (Finset.Icc (-(J : ℤ)) J)), norm_smul, AsymptoticCertificateOperators.amplitude_norm A χ hχ]
  have hb := regular_terminal_fold_truncation_bound
    (AsymptoticRegularCertificate.levelQ_pos A hN v) (AsymptoticRegularCertificate.inputShiftQ A v) (AsymptoticRegularCertificate.outputShiftQ A v)
    (AsymptoticCertificateOperators.lowCell A P.ε v) (AsymptoticCertificateOperators.highStrip P.ε) P.epsilon_pos
    (AsymptoticRegularCertificate.outputShiftQ_nonneg A v) (AsymptoticRegularCertificate.outputShiftQ_le_one A v) (fun _ hz => (show _ < P.ε from hz.2).le) (fun _ hz => hz.1) ht z J hJ
  have hb' := mul_le_mul_of_nonneg_left hb
    (abs_nonneg (AsymptoticCertificateBranches.scalar A v : ℝ))
  simpa only [AsymptoticRegularCertificate.terminalPart, AsymptoticRegularCertificate.finiteTerminalPart,
    mul_div_assoc, AsymptoticRegularCertificate.levelQ_cast] using hb'

#print axioms regular_terminal_certificate_truncation_bound

/-- The fold error after a depth-`n` Neumann polynomial. -/
def reconstructionFoldTailConstant (P : Parameters A) (n : ℕ) : ℝ :=
  (n : ℝ) * terminalFoldTailConstant A P + (n : ℝ) ^ 2 *
    lowFoldTailConstant A P (P.s + 3) * AsymptoticCertificateOperators.terminalConstant A P

theorem physical_neumann_fold_truncation_bound (hN : 0 < N) (P : Parameters A)
    (hP : P.ρ ^ (P.s + 3 - 1) * AsymptoticCertificateOperators.lowConstant A P ≤ 1)
    (χ : ℕ → ℂ) (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1)
    (m : ℕ) (n J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticReconstruction.finiteLow (AsymptoticCertificateOperators.low A hN P χ (P.s + 3) m) (AsymptoticCertificateOperators.terminal A hN P χ (by omega : 2 ≤ P.s + 3) m) n -
      AsymptoticReconstruction.finiteLow (AsymptoticCertificateOperators.finiteLow A hN P χ (P.s + 3) (Finset.Icc (-(J : ℤ)) J) m) (AsymptoticCertificateOperators.finiteTerminal A hN P χ (by omega : 2 ≤ P.s + 3) (Finset.Icc (-(J : ℤ)) J) m) n‖ ≤
        reconstructionFoldTailConstant A P n / (J : ℝ) := by
  have hK := (AsymptoticCertificateOperators.low_norm_le A hN P χ hχ (by omega : 1 ≤ P.s + 3) m).trans hP
  have hK' := (AsymptoticCertificateOperators.finiteLow_norm_le A hN P χ hχ (by omega : 1 ≤ P.s + 3) (Finset.Icc (-(J : ℤ)) J) m).trans hP
  have hB' := AsymptoticCertificateOperators.finiteTerminal_norm_le A hN P χ hχ (by omega : 2 ≤ P.s + 3) (Finset.Icc (-(J : ℤ)) J) m
  have hk := physical_low_certificate_truncation_bound A hN P χ hχ (by omega : 1 ≤ P.s + 3) m J hJ
  have hb := physical_terminal_certificate_truncation_bound A hN P χ hχ (by omega : 2 ≤ P.s + 3) m J hJ
  apply (AsymptoticReconstruction.finiteLow_difference_norm_le _ _ _ _ hK hK' n).trans
  calc
    _ ≤ (n : ℝ) * (terminalFoldTailConstant A P / J) +
        (n : ℝ) ^ 2 * (lowFoldTailConstant A P (P.s + 3) / J) *
          AsymptoticCertificateOperators.terminalConstant A P :=
      add_le_add (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
        (mul_le_mul (mul_le_mul_of_nonneg_left hk (sq_nonneg _)) hB'
          (norm_nonneg _) (mul_nonneg (sq_nonneg _) ((norm_nonneg _).trans hk)))
    _ = _ := by unfold reconstructionFoldTailConstant; ring

#print axioms physical_neumann_fold_truncation_bound

theorem regular_neumann_fold_truncation_bound (hN : 0 < N) (P : Parameters A)
    (hP : P.ρ ^ (P.s + 3 - 1) * AsymptoticCertificateOperators.lowConstant A P ≤ 1)
    (χ : ℕ → ℂ) (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1)
    (z : ℍ) (n J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticReconstruction.finiteLow (AsymptoticRegularCertificate.low A hN P χ (P.s + 3) z) (AsymptoticRegularCertificate.terminal A hN P χ (by omega : 2 ≤ P.s + 3) z) n -
      AsymptoticReconstruction.finiteLow (AsymptoticRegularCertificate.finiteLow A hN P χ (P.s + 3) (Finset.Icc (-(J : ℤ)) J) z) (AsymptoticRegularCertificate.finiteTerminal A hN P χ (by omega : 2 ≤ P.s + 3) (Finset.Icc (-(J : ℤ)) J) z) n‖ ≤
        reconstructionFoldTailConstant A P n / (J : ℝ) := by
  have hK := (AsymptoticRegularCertificate.low_norm_le A hN P χ hχ (by omega : 1 ≤ P.s + 3) z).trans hP
  have hK' := (AsymptoticRegularCertificate.finiteLow_norm_le A hN P χ hχ (by omega : 1 ≤ P.s + 3) (Finset.Icc (-(J : ℤ)) J) z).trans hP
  have hB' := AsymptoticRegularCertificate.finiteTerminal_norm_le A hN P χ hχ (by omega : 2 ≤ P.s + 3) (Finset.Icc (-(J : ℤ)) J) z
  have hk := regular_low_certificate_truncation_bound A hN P χ hχ (by omega : 1 ≤ P.s + 3) z J hJ
  have hb := regular_terminal_certificate_truncation_bound A hN P χ hχ (by omega : 2 ≤ P.s + 3) z J hJ
  apply (AsymptoticReconstruction.finiteLow_difference_norm_le _ _ _ _ hK hK' n).trans
  calc
    _ ≤ (n : ℝ) * (terminalFoldTailConstant A P / J) +
        (n : ℝ) ^ 2 * (lowFoldTailConstant A P (P.s + 3) / J) *
          AsymptoticCertificateOperators.terminalConstant A P :=
      add_le_add (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
        (mul_le_mul (mul_le_mul_of_nonneg_left hk (sq_nonneg _)) hB'
          (norm_nonneg _) (mul_nonneg (sq_nonneg _) ((norm_nonneg _).trans hk)))
    _ = _ := by unfold reconstructionFoldTailConstant; ring

#print axioms regular_neumann_fold_truncation_bound

/-- Explicit finite-fold and finite-depth error for the actual holomorphic
reconstruction. Both approximation parameters are displayed. -/
theorem physical_reconstruction_explicit_error (hN : 0 < N) (P : Parameters A)
    (hP : P.ρ ^ (P.s + 3 - 1) * AsymptoticCertificateOperators.lowConstant A P ≤ 1 / 2)
    (χ : ℕ → ℂ) (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1)
    (m n J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticGeometricReconstruction.finiteFoldExtension A hN P χ n
        (Finset.Icc (-(J : ℤ)) J) m -
      AsymptoticGeometricReconstruction.extension A hN P χ m‖ ≤
        reconstructionFoldTailConstant A P n / (J : ℝ) +
          2 * AsymptoticCertificateOperators.terminalConstant A P * (1 / 2 : ℝ) ^ n := by
  have hP1 := hP.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hfold := physical_neumann_fold_truncation_bound A hN P hP1 χ hχ m n J hJ
  have he : AsymptoticGeometricReconstruction.finiteExtension A hN P χ m n =
      (AsymptoticGeometricReconstruction.TerminalSpace A P).subtypeL +
        (AsymptoticReconstruction.finiteLow
          (AsymptoticCertificateOperators.low A hN P χ (P.s + 3) m)
          (AsymptoticCertificateOperators.terminal A hN P χ (by omega : 2 ≤ P.s + 3) m) n).comp
            (AsymptoticGeometricReconstruction.TerminalSpace A P).subtypeL := by
    simp only [AsymptoticGeometricReconstruction.finiteExtension,
      AsymptoticReconstruction.finiteLow, ContinuousLinearMap.comp_assoc]
  have herr : ‖AsymptoticGeometricReconstruction.finiteExtension A hN P χ m n -
      AsymptoticGeometricReconstruction.finiteFoldExtension A hN P χ n
        (Finset.Icc (-(J : ℤ)) J) m‖ ≤ reconstructionFoldTailConstant A P n / (J : ℝ) := by
    rw [he, AsymptoticGeometricReconstruction.finiteFoldExtension,
      add_sub_add_left_eq_sub _ _ (AsymptoticGeometricReconstruction.TerminalSpace A P).subtypeL,
      ← ContinuousLinearMap.sub_comp]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_left
      (AsymptoticGeometricReconstruction.terminal_inclusion_norm_le A P) (norm_nonneg _)).trans
    simpa only [mul_one] using hfold
  have hdepth := AsymptoticGeometricReconstruction.finiteExtension_error A hN P χ hχ m n
    ((AsymptoticCertificateOperators.low_norm_le A hN P χ hχ
      (by omega : 1 ≤ P.s + 3) m).trans hP)
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (AsymptoticGeometricReconstruction.finiteExtension A hN P χ m n) _).trans
  exact add_le_add (by simpa only [norm_sub_rev] using herr) hdepth

/-- The identical explicit parameters work for every regular orbit root. -/
theorem regular_reconstruction_explicit_error (hN : 0 < N) (P : Parameters A)
    (hP : P.ρ ^ (P.s + 3 - 1) * AsymptoticCertificateOperators.lowConstant A P ≤ 1 / 2)
    (χ : ℕ → ℂ) (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1)
    (z : ℍ) (n J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticRegularReconstruction.finiteFoldFull A hN P χ n
        (Finset.Icc (-(J : ℤ)) J) z -
      AsymptoticRegularReconstruction.full A hN P χ z‖ ≤
        reconstructionFoldTailConstant A P n / (J : ℝ) +
          2 * AsymptoticCertificateOperators.terminalConstant A P * (1 / 2 : ℝ) ^ n := by
  have hP1 := hP.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hfold := regular_neumann_fold_truncation_bound A hN P hP1 χ hχ z n J hJ
  have herr : ‖AsymptoticRegularReconstruction.finiteFull A hN P χ n z -
      AsymptoticRegularReconstruction.finiteFoldFull A hN P χ n
        (Finset.Icc (-(J : ℤ)) J) z‖ ≤ reconstructionFoldTailConstant A P n / (J : ℝ) := by
    rw [AsymptoticRegularReconstruction.finiteFull,
      AsymptoticRegularReconstruction.finiteFoldFull, ← ContinuousLinearMap.sub_comp,
      add_sub_add_left_eq_sub]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_left
      (AsymptoticRegularCertificate.highProjection_norm_le A P z) (norm_nonneg _)).trans
    simpa only [mul_one] using hfold
  have hdepth := AsymptoticRegularReconstruction.finiteFull_error A hN P χ hχ n z
    ((AsymptoticRegularCertificate.low_norm_le A hN P χ hχ
      (by omega : 1 ≤ P.s + 3) z).trans hP)
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (AsymptoticRegularReconstruction.finiteFull A hN P χ n z) _).trans
  exact add_le_add (by simpa only [norm_sub_rev] using herr) hdepth

#print axioms physical_reconstruction_explicit_error
#print axioms regular_reconstruction_explicit_error

variable {ι : Type*} [Fintype ι]

/-- The bound is for the actual retained reconstruction/observation
operator already present in the qualitative development.  The regular
term is its literal cut ambient operator, not an abstract trace symbol. -/
theorem finiteAmbientExpression_quantitative_trace_bound
    (hN : 0 < N) (P : Parameters A)
    (r : ι → AsymptoticCompactObservationCount.Row N) (s : ι → Set ℍ)
    (hs : ∀ i, IsCompact (s i)) (e : Sector N) {Y H D : ℝ}
    (hY : 0 < Y) (hH : 0 < H) (hD : 0 ≤ D)
    (n d : ℕ) (I S : Finset ℤ) (h : ℕ)
    (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (hfar : ∀ j : ℤ, j ∉ S → 2 * compactBaseBound Y H 1 ≤ 1 + |(j : ℝ)|)
    (geom : ∀ b ∈ finiteAmbientExpression A hN P r s hs e Y n d I,
      b.label ≠ 1 → RetainedBranchGeometry b Y H D S) :
    |liftedTrace h (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        (holomorphicSum (retainedExpression Y H
          (finiteAmbientExpression A hN P r s hs e Y n d I)) (h + 1)) /
        ((2 * h + 2 : ℕ) : ℝ) -
      signedTrace volume
        (fun z => (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
          ((AsymptoticRegularObservation.finiteCutPolynomialAmbient A hN P r s hs e Y n d I z).comp
            (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z))) / (4 * Real.pi)| ≤
      (expressionBound (finiteAmbientExpression A hN P r s hs e Y n d I) +
        ((finiteAmbientExpression A hN P r s hs e Y n d I).length : ℝ)) *
        uniformRetainedTraceError D Y H h S.card := by
  have ht := retained_expression_uniform_trace_bound
    (finiteAmbientExpression A hN P r s hs e Y n d I)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos hD hY hH h hsmall S hfar geom
  have he : regularSum (retainedExpression Y H (finiteAmbientExpression A hN P r s hs e Y n d I)) =
      (fun z => (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
        ((AsymptoticRegularObservation.finiteCutPolynomialAmbient A hN P r s hs e Y n d I z).comp
          (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z))) := by
    funext z
    rw [regularSum_retainedExpression, regularSum_finiteAmbientExpression]
  rw [he] at ht
  exact ht

#print axioms expressionBound_neumann
#print axioms expressionBound_inversePolynomial
#print axioms expressionBound_fullExpression
#print axioms expressionBound_cutFullExpression
#print axioms finiteAmbientExpression_quantitative_trace_bound

end QuantitativeHolomorphic
