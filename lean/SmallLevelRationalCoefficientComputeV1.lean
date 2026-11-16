module
public import SmallLevelSparseRationalPolynomialCheckV1
public meta import Lean

/-! Check sparse rational normalization one arithmetic node at a time. Candidate
data and all intermediate equalities are checked by the ordinary kernel. -/
public meta section
open Lean Meta Elab Tactic
namespace SmallLevelRationalCoefficientCompute
private abbrev Data := List (List Nat × Rat)

private def integer (n : Int) : Expr := match n with
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

private def quoteRat (r : Rat) : MetaM Expr := do
  let den := mkRawNatLit r.den
  let nonzero ← mkAppM ``Ne #[den, mkRawNatLit 0]
  let coprime ← mkAppM ``Nat.Coprime #[mkRawNatLit r.num.natAbs, den]
  return mkApp4 (mkConst ``Rat.mk') (integer r.num) den
    (← mkDecideProof nonzero) (← mkDecideProof coprime)

private def quoteData (p : Data) : MetaM Expr := do
  let monomialType := mkApp (mkConst ``List [0]) (mkConst ``Nat)
  let ratType := mkConst ``Rat
  let termType := mkApp2 (mkConst ``Prod [0,0]) monomialType ratType
  let mut result := mkApp (mkConst ``List.nil [0]) termType
  for (m,c) in p.reverse do
    let term := mkApp4 (mkConst ``Prod.mk [0,0]) monomialType ratType (toExpr m) (← quoteRat c)
    result := mkApp3 (mkConst ``List.cons [0]) termType term result
  return result

/-- Constructor data only; denominator and coprimality proofs are checked by
the kernel, and subsequent normalization certificates check all arithmetic. -/
elab "rational_polynomial% " literal:str : term => do
  let mut data : Data := []
  if !literal.getString.isEmpty then
    for entry in literal.getString.splitOn ";" do
      let [coefficient, monomial] := entry.splitOn ":"
        | throwError "Expected rational coefficient and monomial"
      let [num, den] := coefficient.splitOn "/"
        | throwError "Expected numerator/denominator"
      let some num := num.toInt? | throwError "Invalid numerator"
      let some den := den.toNat? | throwError "Invalid denominator"
      if den == 0 then throwError "Zero denominator"
      let mut powers : List Nat := []
      if !monomial.isEmpty then
        for power in monomial.splitOn "," do
          let some power := power.toNat? | throwError "Invalid monomial index"
          powers := power :: powers
      data := (powers.reverse, Rat.divInt num (.ofNat den)) :: data
  quoteData data.reverse

private def lexLE : List Nat → List Nat → Bool
  | [], _ => true
  | _::_, [] => false
  | a::p, b::q => if a == b then lexLE p q else a ≤ b

private def add : Nat → Data → Data → Data
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, (m,c)::p, (k,d)::q =>
    if m == k then
      if c+d == 0 then add n p q else (m,c+d)::add n p q
    else if (if m.length == k.length then lexLE m k else m.length ≤ k.length) then
      (m,c)::add n p ((k,d)::q)
    else (k,d)::add n ((m,c)::p) q

private def insert (n : Nat) : List Nat → List Nat
  | [] => [n]
  | m::p => if n ≤ m then n::m::p else m::insert n p
private def sort : List Nat → List Nat
  | [] => []
  | n::p => insert n (sort p)
private def scale (m : List Nat) (c : Rat) (p : Data) : Data :=
  p.map fun (n,d) => (sort (m++n), c*d)
private def mul : Data → Data → Data
  | [], _ => []
  | (m,c)::p, q =>
    if c == 0 then mul p q else
      let a := scale m c q
      let b := mul p q
      add (a.length+b.length) a b
private def pow (p : Data) : Nat → Data
  | 0 => [([],1)]
  | n+1 => mul p (pow p n)

private def checked (type proof : Expr) : MetaM Expr := do
  resetCache
  let name ← withOptions (Elab.async.set · false) <| mkAuxLemma [] type proof
  resetCache
  return mkConst name
private def decideEq (a b : Expr) : MetaM Expr := do
  let type ← mkEq a b
  checked type (← mkEqRefl b)
private def nat (e : Expr) : MetaM Nat := do
  let some n ← getNatValue? e | throwError "Expected a natural constructor"
  return n
private def int (e : Expr) : MetaM Int := do
  if e.isAppOfArity ``Int.ofNat 1 then return .ofNat (← nat e.getAppArgs[0]!)
  if e.isAppOfArity ``Int.negSucc 1 then return .negSucc (← nat e.getAppArgs[0]!)
  throwError "Expected an integer constructor"

private structure Normal where
  data : Data
  expr : Expr
  proof : Expr

private abbrev LiteralKey := List (List Nat × Int × Nat)
private abbrev ProofM := StateRefT (Std.HashMap LiteralKey Expr) MetaM

/-- Share constructor data in ordinary kernel-checked definitions. This cache
is local to one closed certificate and contains no mathematical assumptions. -/
private def literal (data : Data) : ProofM Expr := do
  let key : LiteralKey := data.map fun (m,c) => (m,c.num,c.den)
  let cache : Std.HashMap LiteralKey Expr ← get
  if let some expr := cache[key]? then return expr
  let name ← mkAuxDeclName (kind := `_ratpoly)
  let value ← quoteData data
  let expr ← mkAuxDefinition name
    (mkConst ``SmallLevelSparseRationalPolynomialCheck.Poly) value (compile := false)
  modify fun cache => cache.insert key expr
  return expr

private def withLiterals (work : ProofM α) : MetaM α := work.run' {}

private partial def normalize (e : Expr) : ProofM Normal := do
  let coefficients := mkApp (mkConst ``SmallLevelSparseRationalPolynomialCheck.Expr.coefficients) e
  let name := e.getAppFn.constName!
  let args := e.getAppArgs
  if name == ``SmallLevelSparseRationalPolynomialCheck.Expr.add ||
      name == ``SmallLevelSparseRationalPolynomialCheck.Expr.mul then
    let p ← normalize args[0]!
    let q ← normalize args[1]!
    let isAdd := name == ``SmallLevelSparseRationalPolynomialCheck.Expr.add
    let data := if isAdd then add (p.data.length+q.data.length) p.data q.data else mul p.data q.data
    let expr ← literal data
    let op := mkConst (if isAdd then ``SmallLevelSparseRationalPolynomialCheck.add
      else ``SmallLevelSparseRationalPolynomialCheck.mul)
    let congruence ← mkAppM ``congrArg₂ #[op, p.proof, q.proof]
    let reduction ← decideEq (mkApp2 op p.expr q.expr) expr
    let proof ← mkAppM ``Eq.trans #[congruence, reduction]
    return ⟨data, expr, ← checked (← mkEq coefficients expr) proof⟩
  if name == ``SmallLevelSparseRationalPolynomialCheck.Expr.neg then
    let p ← normalize args[0]!
    let data := scale [] (-1) p.data
    let expr ← literal data
    let op := mkApp2 (mkConst ``SmallLevelSparseRationalPolynomialCheck.scale) (toExpr ([] : List Nat)) (← quoteRat (-1))
    let congruence ← mkAppM ``congrArg #[op, p.proof]
    let reduction ← decideEq (mkApp op p.expr) expr
    return ⟨data, expr, ← checked (← mkEq coefficients expr) (← mkAppM ``Eq.trans #[congruence, reduction])⟩
  if name == ``SmallLevelSparseRationalPolynomialCheck.Expr.pow then
    let p ← normalize args[0]!
    let n ← nat args[1]!
    let data := pow p.data n
    let expr ← literal data
    let op := mkConst ``SmallLevelSparseRationalPolynomialCheck.pow
    let congruence ← mkAppM ``congrArg₂ #[op, p.proof, ← mkEqRefl args[1]!]
    let reduction ← decideEq (mkApp2 op p.expr args[1]!) expr
    return ⟨data, expr, ← checked (← mkEq coefficients expr) (← mkAppM ``Eq.trans #[congruence, reduction])⟩
  let data ← if name == ``SmallLevelSparseRationalPolynomialCheck.Expr.constant then do
      pure [([], Rat.divInt (← int args[0]!) (.ofNat (← nat args[1]!)))]
    else if name == ``SmallLevelSparseRationalPolynomialCheck.Expr.natural then do
      pure [([], Rat.ofInt (.ofNat (← nat args[0]!)))]
    else if name == ``SmallLevelSparseRationalPolynomialCheck.Expr.var then do
      pure [([← nat args[0]!], 1)]
    else throwError "Unsupported rational expression constructor: {name}"
  let expr ← literal data
  return ⟨data, expr, ← decideEq coefficients expr⟩

elab "staged_rational_coefficients" : tactic => do
  closeMainGoalUsing `staged_rational_coefficients fun type _ => withLiterals do
    let type ← instantiateMVars type
    if type.hasFVar || type.hasMVar then throwError "Expected a closed identity"
    unless type.isAppOfArity ``Eq 3 do throwError "Expected an equality"
    let lhs := type.getAppArgs[1]!
    let rhs := type.getAppArgs[2]!
    unless lhs.isAppOfArity ``SmallLevelSparseRationalPolynomialCheck.Expr.coefficients 1 do
      throwError "Expected rational expression coefficients"
    let ast ← withTransparency .all <| reduce lhs.getAppArgs[0]!
    let result ← normalize ast
    let reduction ← decideEq result.expr rhs
    checked type (← mkAppM ``Eq.trans #[result.proof, reduction])
end SmallLevelRationalCoefficientCompute
end
