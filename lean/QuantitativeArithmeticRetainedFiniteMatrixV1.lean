module

public import QuantitativeArithmeticRetainedFiniteExtensionV1
public import QuantitativeHolomorphicCertificateHeightV1
public import QuantitativeHolomorphicCompactBoundsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedFiniteExpressions
open UpperHalfPlane MeasureTheory Set SpanningIntegerRows AsymptoticFiniteBranch
open QuantitativeHolomorphic QuantitativeEulerIntegerHeight
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators (cell shift)
open QuantitativeArithmeticRetainedRegularOperators (shiftQ level_pos retained_pos)
open AsymptoticCertificateBranches (residues)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)

theorem primitive_matrix_height (hN : 0<N) (j : Fin Q) (i : RowIndex N Q) :
    ∃ C : ℝ,1≤C ∧ ∀ (P : Parameters A) (t : ℕ) (ht : 2≤t) (J : ℕ),
      ExpressionMatrixBound (primitiveLowExpression A hN P j i t (Finset.Icc (-(J:ℤ)) J))
        (2*(1+(J:ℝ))*C) ∧
      ExpressionMatrixBound (primitiveTerminalExpression A hN P j i ht (Finset.Icc (-(J:ℤ)) J))
        (2*(1+(J:ℝ))*C) := by
  obtain ⟨C,hC,hrep⟩ := finite_family_height (fun d : residues i.val.1 =>
    AsymptoticRationalBranches.fold (level_pos (hQ:=hQ) hN i)
      (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1) 0)
  refine ⟨C,hC,?_⟩
  intro P t ht J
  have hf (d : residues i.val.1) (n : ℤ) (hn : n∈Finset.Icc (-(J:ℤ)) J) :
      ∃ M : IntegerMatrix2,IntegerAction
        (AsymptoticRationalBranches.fold (level_pos (hQ:=hQ) hN i)
          (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1) n) M ∧
        MatrixEntryBound M (2*(1+(J:ℝ))*C) := by
    obtain ⟨M,hm,hM⟩ := hrep d
    obtain ⟨L,hl,hL⟩ := fold_integer_height (level_pos (hQ:=hQ) hN i)
      (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1) hm hM n
    have habs : |(n:ℝ)|≤J := by
      apply abs_le.mpr
      constructor
      · exact_mod_cast (Finset.mem_Icc.mp hn).1
      · exact_mod_cast (Finset.mem_Icc.mp hn).2
    exact ⟨L,hl,fun a b => (hL a b).trans (by nlinarith)⟩
  constructor
  · apply expressionMatrixBound_sum
    intro d _ b hb
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hb
    exact hf d n (Finset.mem_toList.mp hn)
  · apply expressionMatrixBound_sum
    intro d _ b hb
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hb
    exact hf d n (Finset.mem_toList.mp hn)

variable (hS : ∀p∈S,p.Prime)

theorem retained_matrix_height (j : Fin Q) (p : S) (u : ℤ) :
    ∃ C : ℝ,1≤C ∧ ∀ (P : Parameters A) (t : ℕ),
      ExpressionMatrixBound (retainedLowExpression A hS P j p u t) C ∧
      ExpressionMatrixBound (retainedTerminalExpression A hS P j p u t) C := by
  let I := QuantitativeArithmeticRetainedDilationOperator.folds (p.val:ℝ)
    ((p.val:ℝ)*shift j u)
  obtain ⟨C,hC,hrep⟩ := finite_family_height (fun n : I =>
    AsymptoticRationalBranches.compactFold
      (QuantitativeArithmeticRetainedDilationBranches.rationalAffine (p.val:ℚ)
        ((p.val:ℚ)*shiftQ j u) (retained_pos hS p))
      (QuantitativeArithmeticRetainedDilationBranches.det_positive (p.val:ℚ)
        ((p.val:ℚ)*shiftQ j u) (retained_pos hS p)) n.val)
  refine ⟨C,hC,?_⟩
  intro P t
  constructor
  · intro b hb
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hb
    exact hrep ⟨n,Finset.mem_toList.mp hn⟩
  · intro b hb
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hb
    exact hrep ⟨n,Finset.mem_toList.mp hn⟩

theorem row_matrix_height (hN : 0<N) (j : Fin Q) (i : AugIndex N (S:Set ℕ) Q) :
    ∃ C : ℝ,1≤C ∧ ∀ (P : Parameters A) (χ β : ℕ → ℂ) (t : ℕ) (ht : 2≤t) (J : ℕ),
      ExpressionMatrixBound (rowLowExpression A hS hN P χ β j t (Finset.Icc (-(J:ℤ)) J) i)
        (2*(1+(J:ℝ))*C) ∧
      ExpressionMatrixBound (rowTerminalExpression A hS hN P χ β j ht (Finset.Icc (-(J:ℤ)) J) i)
        (2*(1+(J:ℝ))*C) := by
  cases i with
  | inl i =>
    obtain ⟨C,hC,hb⟩ := primitive_matrix_height A hN j i
    exact ⟨C,hC,fun P χ β t ht J => ⟨((hb P t ht J).1).scale _,((hb P t ht J).2).scale _⟩⟩
  | inr i =>
    obtain ⟨C,hC,hb⟩ := retained_matrix_height A hS j i.1 i.2
    refine ⟨C,hC,?_⟩
    intro P χ β t ht J
    have hCJ : C≤2*(1+(J:ℝ))*C := by nlinarith [Nat.cast_nonneg (α:=ℝ) J]
    exact ⟨((hb P t).1.mono hCJ).scale _,((hb P t).2.mono hCJ).scale _⟩

/-- All matrix labels of the original mixed certificate have a common
linear cutoff bound, independent of its scalar amplitudes and exponent. -/
theorem certificate_matrix_height (hN : 0<N) :
    ∃ C : ℝ,1≤C ∧ ∀ (P : Parameters A) (χ β : ℕ → ℂ) (t : ℕ) (ht : 2≤t) (J : ℕ),
      ExpressionMatrixBound (lowExpression A hS hN P χ β t (Finset.Icc (-(J:ℤ)) J))
        (2*(1+(J:ℝ))*C) ∧
      ExpressionMatrixBound (terminalExpression A hS hN P χ β ht (Finset.Icc (-(J:ℤ)) J))
        (2*(1+(J:ℝ))*C) := by
  classical
  let Idx := Σ j : Fin Q,{i // i∈(A.coeff j).support}
  have hh (v : Idx) := row_matrix_height A hS hN v.1 v.2.val
  choose C hC hrow using hh
  obtain ⟨B,hB⟩ := (Set.finite_range C).bddAbove
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro P χ β t ht J
  have hc (v : Idx) : C v≤max 1 B := (hB ⟨v,rfl⟩).trans (le_max_right _ _)
  constructor
  · apply expressionMatrixBound_sum
    intro j _
    apply expressionMatrixBound_sum
    intro i hi
    apply ExpressionMatrixBound.scale
    exact ((hrow ⟨j,i,hi⟩ P χ β t ht J).1).mono
      (mul_le_mul_of_nonneg_left (hc ⟨j,i,hi⟩) (by positivity))
  · apply expressionMatrixBound_sum
    intro j _
    apply expressionMatrixBound_sum
    intro i hi
    apply ExpressionMatrixBound.scale
    exact ((hrow ⟨j,i,hi⟩ P χ β t ht J).2).mono
      (mul_le_mul_of_nonneg_left (hc ⟨j,i,hi⟩) (by positivity))

/-- Matrix growth of the genuine finite terminal extension. -/
theorem fullExpression_matrix_height (hN : 0<N) :
    ∃ C : ℝ,1≤C ∧ ∀ (P : Parameters A) (χ β : ℕ → ℂ)
      (t : ℕ) (ht : 2≤t) (n J : ℕ),
      ExpressionMatrixBound
        (fullExpression A hS hN P χ β ht n (Finset.Icc (-(J:ℤ)) J))
        (4*(2*(2*(1+(J:ℝ))*C))^n*(2*(1+(J:ℝ))*C)) := by
  obtain ⟨C,hC,hrows⟩ := certificate_matrix_height A hS hN
  refine ⟨C,hC,?_⟩
  intro P χ β t ht n J
  let B := 2*(1+(J:ℝ))*C
  have hB : 1≤B := by dsimp only [B]; nlinarith [Nat.cast_nonneg (α:=ℝ) J]
  have hK := (hrows P χ β t ht J).1
  have hT := (hrows P χ β t ht J).2
  have hforce : ExpressionMatrixBound
      ([identity]++terminalExpression A hS hN P χ β ht (Finset.Icc (-(J:ℤ)) J)) B := by
    exact (expressionMatrixBound_identity.append hT).mono (max_le hB le_rfl)
  have hh := ((hK.geometric hB n).compose hforce (by linarith : 0≤B)).compose
    (expressionMatrixBound_singleton_one
      (corner (AsymptoticCertificateOperators.highStrip P.ε)
        (AsymptoticCertificateOperators.highStrip_measurable P.ε)) rfl) zero_le_one
  convert hh using 1
  · rfl
  · dsimp only [B]
    ring

#print axioms fullExpression_matrix_height

#print axioms certificate_matrix_height
end QuantitativeArithmeticRetainedFiniteExpressions
