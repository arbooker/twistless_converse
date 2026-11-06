module

public import QuantitativeArithmeticCompact35JetRowsSoundnessV1

/-! Consolidated chapter: QuantitativeArithmeticCompact35JetRows.Negative118. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticCompact35JetRowsNegative118DataV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! UNVERIFIED witness transcription. One Laurent term per line. -/
namespace QuantitativeArithmeticCompact35JetRows.Negative118
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticLaurentRegisterProgram

def sourceRows : ℕ → Poly
  | 0 => [((1/1:ℚ),0,(0,0,0,0,0,0,0))]
  | 1 => [((1/1:ℚ),9,(0,0,0,0,0,0,0)),
      ((1/1:ℚ),70,(-2,2,-1,-1,0,0,0))]
  | 2 => [((1/1:ℚ),18,(0,0,0,0,0,0,0)),
      ((1/1:ℚ),140,(0,2,-1,-1,0,0,0))]
  | 3 => [((1/1:ℚ),36,(0,0,0,0,0,0,0)),
      ((1/1:ℚ),175,(2,2,-1,-1,0,0,0))]
  | 4 => [((1/1:ℚ),70,(0,0,0,0,0,0,0)),
      ((1/1:ℚ),192,(0,-2,1,1,0,0,0))]
  | 5 => [((1/1:ℚ),114,(0,0,0,0,0,0,0)),
      ((-1/1:ℚ),192,(0,0,0,0,0,0,0))]
  | 6 => [((-1/1:ℚ),0,(-2,-2,0,0,0,0,0)),
      ((1/1:ℚ),175,(0,0,0,0,0,0,0))]
  | 7 => [((1/1:ℚ),70,(0,0,0,0,0,0,0)),
      ((1/1:ℚ),140,(0,0,0,0,0,0,0))]
  | 8 => [((1/1:ℚ),9,(0,0,0,0,0,0,0)),
      ((-1/1:ℚ),18,(-1,0,0,0,1,0,0)),
      ((1/1:ℚ),36,(-2,0,0,0,0,0,0)),
      ((1/1:ℚ),114,(0,0,0,0,0,0,0))]
  | _ => []

def initialRows : List Poly := QuantitativeArithmeticLaurentProgram.sourceInputs sourceRows 9 (List.range 10)

def program : List Instruction := [
  ⟨0,0,9,[((1/1:ℚ),0,(0,0,0,0,0,0,0))]⟩,
  ⟨6,9,0,[((1/1:ℚ),0,(0,0,0,0,0,0,0)),
      ((1/1:ℚ),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨0,0,6,[((1/1:ℚ),0,(0,0,0,0,0,0,0))]⟩,
  ⟨3,6,0,[((1/1:ℚ),0,(0,0,0,0,0,0,0)),
      ((-1/1:ℚ),1,(2,2,-1,-1,0,0,0))]⟩,
  ⟨0,0,3,[((1/1:ℚ),0,(0,0,0,0,0,0,0))]⟩,
  ⟨8,3,0,[((1/1:ℚ),0,(0,0,0,0,0,0,0)),
      ((-1/1:ℚ),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨1,1,3,[((1/1:ℚ),0,(0,0,0,0,0,0,0))]⟩,
  ⟨0,3,1,[((1/1:ℚ),0,(0,0,0,0,0,0,0)),
      ((-1/1:ℚ),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2,2,0,[((1/1:ℚ),0,(0,0,0,0,0,0,0))]⟩,
  ⟨1,0,2,[((1/1:ℚ),0,(0,0,0,0,0,0,0)),
      ((1/1:ℚ),1,(-1,0,0,0,1,0,0))]⟩,
  ⟨4,4,0,[((1/1:ℚ),0,(0,0,0,0,0,0,0))]⟩,
  ⟨7,0,1,[((1/1:ℚ),0,(0,0,0,0,0,0,0)),
      ((-1/1:ℚ),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2,0,3,[((1/1:ℚ),0,(0,0,0,0,0,0,0)),
      ((1/1:ℚ),1,(-2,2,-1,-1,0,0,0))]⟩,
  ⟨5,5,0,[((1/1:ℚ),0,(0,0,0,0,0,0,0))]⟩,
  ⟨3,0,2,[((1/1:ℚ),0,(0,0,0,0,0,0,0)),
      ((-1/1:ℚ),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1,1,0,[((1/1:ℚ),0,(0,0,0,0,0,0,0))]⟩,
  ⟨2,0,1,[((1/1:ℚ),0,(0,0,0,0,0,0,0)),
      ((-1/1:ℚ),1,(-1,2,-1,-1,1,0,0))]⟩
]

def outputIndices : List ℕ := [1]

def resultRow : Fin 1 → Poly
  | 0 => [((1/1:ℚ),192,(-2,0,0,0,0,0,0)),
      ((1/1:ℚ),192,(-1,0,0,0,1,0,0)),
      ((1/1:ℚ),192,(0,0,0,0,0,0,0))]

def resultRows : List Poly := (List.finRange 1).map resultRow
end QuantitativeArithmeticCompact35JetRows.Negative118
end
end

/-! ## QuantitativeArithmeticCompact35JetRowsNegative118ExpressionsV1 -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! UNVERIFIED finite bridges to the exact original endpoint expressions. -/
namespace QuantitativeArithmeticCompact35JetRows.Negative118
open QuantitativeArithmeticSevenLaurentRows

def sourceExpression (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Fin 9 → ℂ
  | 0 => (1)*v 0
  | 1 => (1)*v 9 + ((y^2)/(x^2*z*w))*v 70
  | 2 => (1)*v 18 + ((y^2)/(z*w))*v 140
  | 3 => (1)*v 36 + ((x^2*y^2)/(z*w))*v 175
  | 4 => (1)*v 70 + ((z*w)/(y^2))*v 192
  | 5 => (1)*v 114 + (-1)*v 192
  | 6 => ((-1)/(x^2*y^2))*v 0 + (1)*v 175
  | 7 => (1)*v 70 + (1)*v 140
  | 8 => (1)*v 9 + (((-1)*a)/(x))*v 18 + ((1)/(x^2))*v 36 + (1)*v 114
  | _ => 0

def resultExpression (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Fin 1 → ℂ
  | 0 => ((1 + x*a + x^2)/(x^2))*v 192
  | _ => 0

theorem source_match (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (v : Fin 210 → ℂ) (i : Fin 9) :
    eval x y z w a b 1 (lift v) (sourceRows i.val)=sourceExpression x y z w a b v i := by
  fin_cases i <;>
    norm_num [sourceRows,sourceExpression,eval,monomial,lift] <;>
    field_simp [hx,hy,hz,hw] <;>
    first | exact Or.inl trivial | exact Or.inr trivial | ring

#print axioms source_match

theorem result_match (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (v : Fin 210 → ℂ) (i : Fin 1) :
    eval x y z w a b 1 (lift v) (resultRow i)=resultExpression x y z w a b v i := by
  fin_cases i <;>
    norm_num [resultRow,resultExpression,eval,monomial,lift] <;>
    field_simp [hx,hy,hz,hw] <;>
    first | exact Or.inl trivial | exact Or.inr trivial | ring

#print axioms result_match

end QuantitativeArithmeticCompact35JetRows.Negative118
end
end

/-! ## QuantitativeArithmeticCompact35JetRowsNegative118VerificationV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! UNVERIFIED kernel computation; no external arithmetic is trusted. -/
namespace QuantitativeArithmeticCompact35JetRows.Negative118
theorem checked : QuantitativeArithmeticLaurentRegisterProgram.verify
    initialRows program outputIndices resultRows=true := by
  decide +kernel
#print axioms checked
end QuantitativeArithmeticCompact35JetRows.Negative118
end
end
