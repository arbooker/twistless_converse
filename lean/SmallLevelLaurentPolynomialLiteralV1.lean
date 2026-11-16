module
public import Init.Data.Rat.Basic
public meta import Lean.Elab.Term

public meta section
open Lean Elab Term
namespace SmallLevelLaurentPolynomialLiteral

private def integer (n : Int) : Expr :=
  match n with
  | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (mkRawNatLit n)

/-- Literal data, not a proof-producing oracle. Construct rational Laurent
polynomials directly, avoiding elaboration of thousands of overloaded tuples
and divisions. Every certificate equality is checked by the ordinary kernel. -/
elab "laurent_polynomial% " data:str : term => do
  let natType := Lean.mkConst ``Nat
  let intType := Lean.mkConst ``Int
  let ratType := Lean.mkConst ``Rat
  let prod := Lean.mkConst ``Prod [0,0]
  let types := [intType, intType, intType, intType, natType, natType, natType]
  let exponentType := types.dropLast.foldr (mkApp2 prod) natType
  let indexType := mkApp2 prod natType exponentType
  let termType := mkApp2 prod ratType indexType
  let mut entries : List Expr := []
  if !data.getString.isEmpty then
    for entry in data.getString.splitOn ";" do
      let [coefficient, index, powers] := entry.splitOn ":"
        | throwError "Invalid Laurent polynomial entry"
      let [numerator, denominator] := coefficient.splitOn "/"
        | throwError "Expected a rational coefficient"
      let some a := numerator.toInt? | throwError "Invalid numerator"
      let some b := denominator.toNat? | throwError "Invalid denominator"
      if b == 0 then throwError "Zero denominator"
      let some j := index.toNat? | throwError "Invalid index"
      let keys := powers.splitOn ","
      if keys.length != 7 then throwError "Expected seven exponents"
      let mut values : List Expr := []
      for (key, i) in keys.zipIdx do
        if i < 4 then
          let some n := key.toInt? | throwError "Invalid integer exponent"
          values := integer n :: values
        else
          let some n := key.toNat? | throwError "Invalid natural exponent"
          values := mkRawNatLit n :: values
      let last :: rest := values | throwError "Missing exponents"
      let mut value := last
      let mut ty := natType
      for (v, t) in rest.zip types.dropLast.reverse do
        value := mkApp4 (Lean.mkConst ``Prod.mk [0,0]) t ty v value
        ty := mkApp2 prod t ty
      let coefficient := mkApp2 (Lean.mkConst ``Rat.divInt) (integer a)
        (integer (.ofNat b))
      let indexed := mkApp4 (Lean.mkConst ``Prod.mk [0,0]) natType exponentType
        (mkRawNatLit j) value
      entries := mkApp4 (Lean.mkConst ``Prod.mk [0,0]) ratType indexType
        coefficient indexed :: entries
  return entries.foldl (fun tail entry =>
    mkApp2 (mkApp (Lean.mkConst ``List.cons [0]) termType) entry tail)
    (mkApp (Lean.mkConst ``List.nil [0]) termType)

end SmallLevelLaurentPolynomialLiteral
end
