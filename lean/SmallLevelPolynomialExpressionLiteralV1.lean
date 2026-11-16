module
public import SmallLevelSparseIntegerPolynomialCheckV1
public meta import Lean.Elab.Term

public meta section
open Lean Elab Term

/-- Construct integer polynomial expression data from postfix tokens.
This supplies no equalities; evaluation and normalization are checked separately. -/
elab "integer_polynomial_expr% " literal:str : term => do
  let mut stack : List Expr := []
  for token in literal.getString.splitOn ";" do
    if token == "+" || token == "*" then
      match stack with
      | b :: a :: rest =>
        let op := if token == "+" then ``SmallLevelSparseIntegerPolynomialCheck.Expr.add
          else ``SmallLevelSparseIntegerPolynomialCheck.Expr.mul
        stack := mkApp2 (mkConst op) a b :: rest
      | _ => throwError "Missing binary operands"
    else if token == "neg" then
      match stack with
      | a :: rest => stack := mkApp (mkConst ``SmallLevelSparseIntegerPolynomialCheck.Expr.neg) a :: rest
      | _ => throwError "Missing negation operand"
    else
      let [tag, value] := token.splitOn ":" | throwError "Invalid polynomial expression token"
      let some n := value.toNat? | throwError "Invalid natural literal"
      if tag == "n" then
        stack := mkApp (mkConst ``SmallLevelSparseIntegerPolynomialCheck.Expr.natural) (mkRawNatLit n) :: stack
      else if tag == "v" then
        stack := mkApp (mkConst ``SmallLevelSparseIntegerPolynomialCheck.Expr.var) (mkRawNatLit n) :: stack
      else if tag == "p" then
        match stack with
        | a :: rest => stack := mkApp2 (mkConst ``SmallLevelSparseIntegerPolynomialCheck.Expr.pow) a (mkRawNatLit n) :: rest
        | _ => throwError "Missing power operand"
      else throwError "Unknown polynomial expression token"
  let [result] := stack | throwError "Invalid polynomial expression stack"
  return result
end
