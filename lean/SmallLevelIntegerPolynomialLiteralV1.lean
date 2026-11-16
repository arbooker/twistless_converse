module
public meta import Lean.Elab.Term
public meta import Lean.Meta.AppBuilder
public import SmallLevelSparseIntegerPolynomialCheckV1

public meta section
open Lean Elab Term
namespace SmallLevelIntegerPolynomialLiteral

private def listExpr (type : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x tail => mkApp2 (mkApp (Lean.mkConst ``List.cons [0]) type) x tail)
    (mkApp (Lean.mkConst ``List.nil [0]) type)

/-- Compact input syntax for a literal sparse integer polynomial. Entries are
`variable,variable:coefficient`, separated by semicolons; an empty variable
list is a constant monomial. This elaborator only constructs constructor
expressions. It supplies no equalities and bypasses no kernel checks. -/
elab "integer_polynomial% " data:str : term => do
  let natType := Lean.mkConst ``Nat
  let intType := Lean.mkConst ``Int
  let monomialType := mkApp (Lean.mkConst ``List [0]) natType
  let pairType := mkApp2 (Lean.mkConst ``Prod [0,0]) monomialType intType
  let mut entries : List Expr := []
  if !data.getString.isEmpty then
    for entry in data.getString.splitOn ";" do
      let [keys, coefficient] := entry.splitOn ":"
        | throwError "Invalid integer polynomial entry"
      let some c := coefficient.toInt?
        | throwError "Invalid integer polynomial coefficient"
      let ce := match c with
        | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (mkRawNatLit n)
        | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (mkRawNatLit n)
      let mut varTerms : List Expr := []
      if !keys.isEmpty then
        for key in keys.splitOn "," do
          let some n := key.toNat? | throwError "Invalid monomial variable"
          varTerms := mkRawNatLit n :: varTerms
      let monomial := listExpr natType varTerms.reverse
      entries := mkApp4 (Lean.mkConst ``Prod.mk [0,0]) monomialType intType monomial ce :: entries
  return listExpr pairType entries.reverse

end SmallLevelIntegerPolynomialLiteral
end
