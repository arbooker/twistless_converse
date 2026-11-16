module
public meta import Lean.Elab.Term

public meta section
open Lean Elab Term
namespace SmallLevelSparsePolynomialLiteral

/-- Literal data only: construct a list of integer coefficients and five
natural exponents. Every equality involving this data is checked separately
by the ordinary kernel. -/
elab "sparse_polynomial% " data:str : term => do
  let natType := Lean.mkConst ``Nat
  let intType := Lean.mkConst ``Int
  let prod := Lean.mkConst ``Prod [0,0]
  let mut exponentType := natType
  for _ in [:4] do
    exponentType := mkApp2 prod natType exponentType
  let pairType := mkApp2 prod intType exponentType
  let mut entries : List Expr := []
  if !data.getString.isEmpty then
    for entry in data.getString.splitOn ";" do
      let [coefficient, powers] := entry.splitOn ":"
        | throwError "Invalid sparse polynomial entry"
      let some c := coefficient.toInt?
        | throwError "Invalid integer coefficient"
      let ce := match c with
        | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (mkRawNatLit n)
        | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (mkRawNatLit n)
      let keys := powers.splitOn ","
      if keys.length != 5 then throwError "Expected five natural exponents"
      let mut values : List Expr := []
      for key in keys do
        let some n := key.toNat? | throwError "Invalid natural exponent"
        values := mkRawNatLit n :: values
      let last :: rest := values | throwError "Missing exponents"
      let mut value := last
      let mut ty := natType
      for v in rest do
        value := mkApp4 (Lean.mkConst ``Prod.mk [0,0]) natType ty v value
        ty := mkApp2 prod natType ty
      entries := mkApp4 (Lean.mkConst ``Prod.mk [0,0]) intType exponentType ce value :: entries
  return entries.foldl (fun tail entry =>
    mkApp2 (mkApp (Lean.mkConst ``List.cons [0]) pairType) entry tail)
    (mkApp (Lean.mkConst ``List.nil [0]) pairType)

end SmallLevelSparsePolynomialLiteral
end
