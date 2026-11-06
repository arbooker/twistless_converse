module

public import QuantitativeArithmeticRetainedRegularOperatorsV1
public import AsymptoticFiniteBranchCertificateV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
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

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)

def primitiveLowExpression (hN : 0<N) (P : Parameters A) (j : Fin Q)
    (i : RowIndex N Q) (t : ℕ) (I : Finset ℤ) : Expression :=
  sumExpressions Finset.univ (fun d : residues i.val.1 =>
    ofFinset I (fun n => lowFold (level_pos (hQ:=hQ) hN i) (shiftQ j i.val.2)
      ((d.val:ℚ)/i.val.1) (cell_measurable P.ε j) (lowStrip_measurable P.ε) P.rho_pos.le
      (residueQ_nonneg _ d) (residueQ_le_one _ d) (fun _ hz => hz.1) t n))

def primitiveTerminalExpression (hN : 0<N) (P : Parameters A) (j : Fin Q)
    (i : RowIndex N Q) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) : Expression :=
  sumExpressions Finset.univ (fun d : residues i.val.1 =>
    ofFinset I (fun n => terminalFold (level_pos (hQ:=hQ) hN i) (shiftQ j i.val.2)
      ((d.val:ℚ)/i.val.1) (cell_measurable P.ε j) (highStrip_measurable P.ε) P.epsilon_pos
      (residueQ_nonneg _ d) (residueQ_le_one _ d)
      (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le)
      (fun _ hz => hz.1) ht n))

variable (hS : ∀p∈S,p.Prime)

def retainedLowExpression (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ) (t : ℕ) : Expression :=
  ofFinset (QuantitativeArithmeticRetainedDilationOperator.folds
    (p.val:ℝ) ((p.val:ℝ)*shift j u)) (fun n =>
    QuantitativeArithmeticRetainedDilationBranches.lowBranch (p.val:ℚ)
      ((p.val:ℚ)*shiftQ j u) (retained_pos hS p)
      (cell_measurable P.ε j) (lowStrip_measurable P.ε) t n)

def retainedTerminalExpression (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ) (t : ℕ) : Expression :=
  ofFinset (QuantitativeArithmeticRetainedDilationOperator.folds
    (p.val:ℝ) ((p.val:ℝ)*shift j u)) (fun n =>
    QuantitativeArithmeticRetainedDilationBranches.terminalBranch (p.val:ℚ)
      ((p.val:ℚ)*shiftQ j u) (retained_pos hS p)
      (cell_measurable P.ε j) (highStrip_measurable P.ε) P.ε P.epsilon_pos t n)

theorem retainedLow_holomorphic (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ)
    (β : ℂ) (t m : ℕ) :
    holomorphicSum (scaleExpression β (retainedLowExpression A hS P j p u t)) m=
      QuantitativeArithmeticRetainedDilationOperator.weighted
        (p.val:ℝ) ((p.val:ℝ)*shift j u)
        (QuantitativeArithmeticRetainedCertificateOperators.retained_pos hS p)
        (cell_measurable P.ε j) (lowStrip_measurable P.ε) β t (2*m) := by
  rw [holomorphicSum_scale,retainedLowExpression,holomorphicSum_ofFinset,Finset.smul_sum]
  simpa only [Rat.cast_natCast,Rat.cast_mul,shiftQ_cast] using
    QuantitativeArithmeticRetainedDilationBranches.holomorphic_low_sum (p.val:ℚ)
      ((p.val:ℚ)*shiftQ j u) (retained_pos hS p)
      (cell_measurable P.ε j) (lowStrip_measurable P.ε) β t m

theorem retainedTerminal_holomorphic (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ)
    (β : ℂ) (t m : ℕ) :
    holomorphicSum (scaleExpression β (retainedTerminalExpression A hS P j p u t)) m=
      QuantitativeArithmeticRetainedDilationOperator.terminal
        (p.val:ℝ) ((p.val:ℝ)*shift j u)
        (QuantitativeArithmeticRetainedCertificateOperators.retained_pos hS p)
        (cell_measurable P.ε j) (highStrip_measurable P.ε) P.ε P.epsilon_pos β t (2*m) := by
  rw [holomorphicSum_scale,retainedTerminalExpression,holomorphicSum_ofFinset,Finset.smul_sum]
  simpa only [Rat.cast_natCast,Rat.cast_mul,shiftQ_cast] using
    QuantitativeArithmeticRetainedDilationBranches.holomorphic_terminal_sum (p.val:ℚ)
      ((p.val:ℚ)*shiftQ j u) (retained_pos hS p)
      (cell_measurable P.ε j) (highStrip_measurable P.ε) P.ε P.epsilon_pos β t m

theorem retainedLow_regular (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ) (t : ℕ) (z : ℍ) :
    regularSum (retainedLowExpression A hS P j p u t) z=
      QuantitativeArithmeticRetainedRegularOperators.retainedLow A hS P j p u t z := by
  rw [retainedLowExpression,regularSum_ofFinset]
  rfl

theorem retainedTerminal_regular (P : Parameters A) (j : Fin Q) (p : S) (u : ℤ) (t : ℕ) (z : ℍ) :
    regularSum (retainedTerminalExpression A hS P j p u t) z=
      QuantitativeArithmeticRetainedRegularOperators.retainedTerminal A hS P j p u t z := by
  rw [retainedTerminalExpression,regularSum_ofFinset]
  rfl

def rowLowExpression (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ) (j : Fin Q)
    (t : ℕ) (I : Finset ℤ) : AugIndex N (S:Set ℕ) Q → Expression
  | Sum.inl i => scaleExpression (χ i.val.1) (primitiveLowExpression A hN P j i t I)
  | Sum.inr i => scaleExpression (β i.1.val) (retainedLowExpression A hS P j i.1 i.2 t)

def rowTerminalExpression (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ) (j : Fin Q)
    {t : ℕ} (ht : 2≤t) (I : Finset ℤ) : AugIndex N (S:Set ℕ) Q → Expression
  | Sum.inl i => scaleExpression (χ i.val.1) (primitiveTerminalExpression A hN P j i ht I)
  | Sum.inr i => scaleExpression (β i.1.val) (retainedTerminalExpression A hS P j i.1 i.2 t)

/-- The common finite expression uses the original rational certificate
coefficients and keeps the retained affine terms exactly. -/
def lowExpression (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ) (t : ℕ) (I : Finset ℤ) : Expression :=
  sumExpressions Finset.univ (fun j : Fin Q =>
    sumExpressions (A.coeff j).support (fun i =>
      scaleExpression (A.coeff j i:ℂ) (rowLowExpression A hS hN P χ β j t I i)))

def terminalExpression (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (I : Finset ℤ) : Expression :=
  sumExpressions Finset.univ (fun j : Fin Q =>
    sumExpressions (A.coeff j).support (fun i =>
      scaleExpression (A.coeff j i:ℂ) (rowTerminalExpression A hS hN P χ β j ht I i)))

#print axioms retainedLow_holomorphic
#print axioms retainedTerminal_holomorphic
#print axioms retainedLow_regular
#print axioms retainedTerminal_regular

end QuantitativeArithmeticRetainedFiniteExpressions
