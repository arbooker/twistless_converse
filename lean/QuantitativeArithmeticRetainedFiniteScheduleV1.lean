module

public import QuantitativeArithmeticRetainedPreparedReconstructionV1
public import QuantitativeHolomorphicSimultaneousCutoffsV1
public import QuantitativeArithmeticRetainedFiniteMatrixV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedFiniteSchedule
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteExpressions
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedCertificateOperators (terminalConstant)
open QuantitativeHolomorphic.Schedule (binaryDepth geometric_depth_bound reciprocal_ceil_bound)
open AsymptoticSectorSigns QuantitativeArithmeticRetainedSectorReconstruction

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ) (P : Parameters A)

/-- The literal numerator in the finite-fold error. -/
def foldNumerator (n : ℕ) : ℝ :=
  (n:ℝ)*terminalTailConstant A P+(n:ℝ)^2*(P.ρ^(exponent A P+3-1)*lowTailConstant A)*
    (1+terminalConstant A P)

/-- Binary-logarithmic depth and a natural ceiling make the error choice
explicit; neither depends on weight or on a sector. -/
def depth (δ : ℝ) : ℕ := binaryDepth ((2*(1+terminalConstant A P))/(δ/2))
def cutoff (δ : ℝ) : ℕ := ⌈foldNumerator A P (depth A P δ)/(δ/2)⌉₊+1

theorem cutoff_pos (δ : ℝ) : 0<cutoff A P δ := by unfold cutoff; omega

theorem error_bound {δ : ℝ} (hδ : 0<δ) :
    neumannError A P (exponent A P+3) (depth A P δ) (cutoff A P δ)≤δ := by
  have ht : 0<δ/2 := by positivity
  have hf : foldNumerator A P (depth A P δ)/(cutoff A P δ:ℝ)≤δ/2 := reciprocal_ceil_bound ht
  have hg : 2*(1+terminalConstant A P)*(1/2:ℝ)^(depth A P δ)≤δ/2 := geometric_depth_bound ht
  change foldNumerator A P (depth A P δ)/(cutoff A P δ:ℝ)+
    2*(1+terminalConstant A P)*(1/2:ℝ)^(depth A P δ)≤δ
  linarith

variable (hS : ∀p∈S,p.Prime) (hN : 0<N)

def expression (δ : ℝ) (e : Sector N) : AsymptoticFiniteBranch.Expression :=
  fullExpression A hS hN P (multiplier e) (ramifiedParameter e)
    (by omega : 2≤exponent A P+3) (depth A P δ) (symmetricFolds (cutoff A P δ))

theorem expression_mass (δ : ℝ) (e : Sector N) :
    AsymptoticFiniteBranch.expressionBound (expression A P hS hN δ e)≤
      QuantitativeArithmeticRetainedCylinderNormalization.bound A P :=
  finite_mass A P hS hN e (depth A P δ) (symmetricFolds (cutoff A P δ))

theorem physical_error {δ : ℝ} (hδ : 0<δ) (e : Sector N) (m : ℕ) :
    ‖(AsymptoticFiniteBranch.holomorphicSum (expression A P hS hN δ e) m).comp
      (QuantitativeArithmeticRetainedTerminalExtension.TerminalSpace A P).subtypeL-
      QuantitativeArithmeticRetainedTerminalExtension.extension A hS hN P
        (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) m‖≤δ :=
  (holomorphic_extension_rate A hS hN P (multiplier e) (ramifiedParameter e)
    (fun q _ => multiplier_norm e q) (fun p _ => ramifiedParameter_norm e p)
    (by omega) (scalar_contraction A P).le (depth A P δ) (cutoff A P δ)
    (cutoff_pos A P δ) m).trans (error_bound A P hδ)

theorem regular_error {δ : ℝ} (hδ : 0<δ) (e : Sector N) (z : UpperHalfPlane) :
    ‖(AsymptoticFiniteBranch.regularSum (expression A P hS hN δ e) z).comp
      (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL-
      QuantitativeArithmeticRetainedRegularExtension.extension A hS hN P
        (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) z‖≤δ :=
  (regular_extension_rate A hS hN P (multiplier e) (ramifiedParameter e)
    (fun q _ => multiplier_norm e q) (fun p _ => ramifiedParameter_norm e p)
    (by omega) (scalar_contraction A P).le (depth A P δ) (cutoff A P δ)
    (cutoff_pos A P δ) z).trans (error_bound A P hδ)

/-- One certificate-dependent matrix constant bounds every scheduled
approximant explicitly in its chosen depth and fold cutoff. -/
theorem matrix_bound : ∃C : ℝ,1≤C ∧ ∀ (δ : ℝ) (e : Sector N),
    QuantitativeHolomorphic.ExpressionMatrixBound (expression A P hS hN δ e)
      (4*(4*(1+(cutoff A P δ:ℝ))*C)^(depth A P δ)*(2*(1+(cutoff A P δ:ℝ))*C)) := by
  obtain ⟨C,hC,hM⟩ := fullExpression_matrix_height A hS hN
  refine ⟨C,hC,?_⟩
  intro δ e
  convert hM P (multiplier e) (ramifiedParameter e) (exponent A P+3)
    (by omega) (depth A P δ) (cutoff A P δ) using 1 <;> try rfl
  congr 2
  ring

#print axioms matrix_bound
#print axioms error_bound
#print axioms expression_mass
#print axioms physical_error
#print axioms regular_error
end QuantitativeArithmeticRetainedFiniteSchedule
