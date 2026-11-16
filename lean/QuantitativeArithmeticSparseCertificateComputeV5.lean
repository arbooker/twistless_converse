module
public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public import SmallLevelSparseCoefficientPartitionV1
public meta import Lean

public theorem sparse_slice_append (n : Nat)
    (p q : QuantitativeArithmeticSparsePolynomialCertificate.Poly) :
    SmallLevelSparseCoefficientPartition.slice n (p ++ q) =
      SmallLevelSparseCoefficientPartition.slice n p ++
      SmallLevelSparseCoefficientPartition.slice n q := by
  simp only [SmallLevelSparseCoefficientPartition.slice, List.filterMap_append]

public theorem sparse_bounded_append (n : Nat)
    (p q : QuantitativeArithmeticSparsePolynomialCertificate.Poly) :
    SmallLevelSparseCoefficientPartition.bounded n (p ++ q) =
      (SmallLevelSparseCoefficientPartition.bounded n p &&
       SmallLevelSparseCoefficientPartition.bounded n q) := by
  simp only [SmallLevelSparseCoefficientPartition.bounded, List.all_append]

/-! Staged checking of closed sparse-polynomial identities. Candidate intermediate
lists are computed outside the kernel, but every operation and every link to the
original expression is checked by the ordinary kernel. -/
public meta section
open Lean Meta Elab Tactic
namespace QuantitativeArithmeticSparseCertificateCompute

private abbrev Powers := Nat × Nat × Nat × Nat × Nat
private abbrev Data := List (Int × Powers)

private def nat (e : Expr) : MetaM Nat := do
  let some n ← getNatValue? e | throwError "Expected a natural constructor"
  return n

private def int (e : Expr) : MetaM Int := do
  let e := e.consumeMData
  if e.isAppOfArity ``Int.ofNat 1 then return .ofNat (← nat e.getAppArgs[0]!)
  if e.isAppOfArity ``Int.negSucc 1 then return .negSucc (← nat e.getAppArgs[0]!)
  throwError "Expected an integer constructor"

private def pair (e : Expr) : MetaM (Expr × Expr) := do
  let e := e.consumeMData
  unless e.isAppOfArity ``Prod.mk 4 do throwError "Expected a pair constructor"
  return (e.getAppArgs[2]!, e.getAppArgs[3]!)

private def powers (e : Expr) : MetaM Powers := do
  let (a, e) ← pair e
  let (b, e) ← pair e
  let (c, e) ← pair e
  let (d, e) ← pair e
  return (← nat a, ← nat b, ← nat c, ← nat d, ← nat e)

private partial def decode (e : Expr) : MetaM Data := do
  let e := e.consumeMData
  if e.isAppOfArity ``List.nil 1 then return []
  unless e.isAppOfArity ``List.cons 3 do throwError "Expected a list constructor"
  let (c, p) ← pair e.getAppArgs[1]!
  return (← int c, ← powers p) :: (← decode e.getAppArgs[2]!)

private def key (e : Powers) : Nat :=
  (((e.1 * 16 + e.2.1) * 16 + e.2.2.1) * 16 + e.2.2.2.1) * 16 + e.2.2.2.2

private def merge : Nat → Data → Data → Data
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, (a,e)::p, (b,f)::q =>
    if e == f then
      if a+b == 0 then merge n p q else (a+b,e)::merge n p q
    else if key e < key f then (a,e)::merge n p ((b,f)::q)
    else (b,f)::merge n ((a,e)::p) q

private def addPowers (e f : Powers) : Powers :=
  (e.1+f.1, e.2.1+f.2.1, e.2.2.1+f.2.2.1,
    e.2.2.2.1+f.2.2.2.1, e.2.2.2.2+f.2.2.2.2)

private def multiply (p : Data) : Data → Data
  | [] => []
  | (c,e)::q =>
    let left := p.map fun (d,f) => (c*d, addPowers e f)
    let right := multiply p q
    merge (left.length + right.length) left right

/-- Store a fully kernel-checked closed proof behind an opaque lemma so that
later stages do not repeat the earlier arithmetic reduction. -/
private def checked (type proof : Expr) : MetaM Expr := do
  -- Closed proofs do not need earlier elaborator memo tables. Preserve the
  -- metavariable context and checked environment; release only recomputable caches.
  resetCache
  let name ← withOptions (Elab.async.set · false) <| mkAuxLemma [] type proof
  resetCache
  return mkConst name

private def decideEq (a b : Expr) : MetaM Expr := do
  let type ← mkEq a b
  checked type (← mkEqRefl b)

private structure Normal where
  data : Data
  expr : Expr
  proof : Expr

/-- Store each repeated constructor list once. Proofs refer to a kernel-checked
ordinary definition instead of duplicating the full list in every equality type. -/
private abbrev ProofM := StateRefT (Std.HashMap Data Expr) MetaM

private def literal (data : Data) : ProofM Expr := do
  let cache : Std.HashMap Data Expr ← get
  if let some expr := cache[data]? then return expr
  let name ← mkAuxDeclName (kind := `_poly)
  let expr ← mkAuxDefinition name
    (mkConst ``QuantitativeArithmeticSparsePolynomialCertificate.Poly)
    (toExpr data) (compile := false)
  modify fun cache => cache.insert data expr
  return expr

private def withLiterals (work : ProofM α) : MetaM α :=
  work.run' {}

/-- Reduce at most 32 merge decisions per kernel conversion. Each residual
merge is replaced only using its already checked opaque equality. -/
private partial def normalizeMerge (fuel : Nat) (p q : Data) : ProofM Normal := do
  let input := mkApp3 (mkConst ``QuantitativeArithmeticSparsePolynomialCertificate.mergeFuel)
    (toExpr fuel) (← literal p) (← literal q)
  if fuel ≤ 32 || p.isEmpty || q.isEmpty then
    let data := merge fuel p q
    let expr ← literal data
    return ⟨data, expr, ← decideEq input expr⟩
  let mut n := fuel
  let mut left := p
  let mut right := q
  let mut front : Data := []
  for _ in [:32] do
    match n, left, right with
    | j+1, (a,e)::ps, (b,f)::qs =>
      n := j
      if e == f then
        left := ps
        right := qs
        if a+b != 0 then front := (a+b,e)::front
      else if key e < key f then
        front := (a,e)::front
        left := ps
      else
        front := (b,f)::front
        right := qs
    | _, _, _ => break
  front := front.reverse
  let rest ← normalizeMerge n left right
  let residual := mkApp3 (mkConst ``QuantitativeArithmeticSparsePolynomialCertificate.mergeFuel)
    (toExpr n) (← literal left) (← literal right)
  let split ← mkAppM ``List.append #[toExpr front, residual]
  let splitProof ← checked (← mkEq input split) (← mkEqRefl split)
  let app ← mkAppM ``List.append #[toExpr front, rest.expr]
  let operation := app.getAppFn
  let appendPrefix := mkApp2 operation app.getAppArgs[0]! (← literal front)
  let congruence ← mkAppM ``congrArg #[appendPrefix, rest.proof]
  let data := front ++ rest.data
  let expr ← literal data
  let finish ← decideEq app expr
  let proof ← mkAppM ``Eq.trans #[splitProof, ← mkAppM ``Eq.trans #[congruence, finish]]
  return ⟨data, expr, ← checked (← mkEq input expr) proof⟩

/-- Each product step checks a literal shift and a bounded merge, rather
than asking kernel reduction to expand the entire nested convolution. -/
private partial def normalizeProduct (p : Data) (pe : Expr) (q : Data) : ProofM Normal := do
  let input := mkApp2 (mkConst ``QuantitativeArithmeticSparsePolynomialCertificate.product) pe (← literal q)
  match q with
  | [] => return ⟨[], (← literal ([] : Data)), ← decideEq input ((← literal ([] : Data)))⟩
  | (c,e)::qs =>
    let rest ← normalizeProduct p pe qs
    let shifted := p.map fun (d,f) => (c*d, addPowers e f)
    let shiftedExpr ← literal shifted
    let shift := mkApp3 (mkConst ``QuantitativeArithmeticSparsePolynomialCertificate.shift)
      (toExpr c) (toExpr e) pe
    let shiftProof ← decideEq shift shiftedExpr
    let op := mkConst ``QuantitativeArithmeticSparsePolynomialCertificate.merge
    let residual := mkApp2 (mkConst ``QuantitativeArithmeticSparsePolynomialCertificate.product) pe (← literal qs)
    let split := mkApp2 op shift residual
    let splitProof ← checked (← mkEq input split) (← mkEqRefl split)
    let congruence ← mkAppM ``congrArg₂ #[op, shiftProof, rest.proof]
    let result ← normalizeMerge (shifted.length + rest.data.length) shifted rest.data
    let literalInput := mkApp2 op shiftedExpr rest.expr
    let merged ← checked (← mkEq literalInput result.expr) result.proof
    let proof ← mkAppM ``Eq.trans #[splitProof, ← mkAppM ``Eq.trans #[congruence, merged]]
    return ⟨result.data, result.expr, ← checked (← mkEq input result.expr) proof⟩

private partial def extract (n e : Expr) : ProofM Normal := do
  let mut expanded := e
  if e.isConst then
    if let .defnInfo info ← getConstInfo e.constName! then
      expanded := info.value
  let args := expanded.getAppArgs
  let append := expanded.isAppOfArity ``HAppend.hAppend 6 ||
    expanded.isAppOfArity ``List.append 3
  let input := mkApp2 (mkConst ``SmallLevelSparseCoefficientPartition.slice) n e
  if append then
    let p := args[args.size-2]!
    let q := args[args.size-1]!
    let left ← extract n p
    let right ← extract n q
    let data := left.data ++ right.data
    let expr ← literal data
    let decomposition ← mkAppM ``sparse_slice_append #[n, p, q]
    let app ← mkAppM ``List.append #[left.expr, right.expr]
    let congruence ← mkAppM ``congrArg₂ #[mkApp app.getAppFn app.getAppArgs[0]!, left.proof, right.proof]
    let combined ← mkAppM ``Eq.trans #[decomposition, congruence]
    let proof ← mkAppM ``Eq.trans #[combined, ← decideEq app expr]
    return ⟨data, expr, ← checked (← mkEq input expr) proof⟩
  else
    let reduced ← withTransparency .all <| reduce input
    let data ← decode reduced
    let expr ← literal data
    return ⟨data, expr, ← decideEq input expr⟩

private partial def normalize (boundProducts : Bool) (e : Expr) : ProofM Normal := do
  let isMerge := e.isAppOfArity ``QuantitativeArithmeticSparsePolynomialCertificate.merge 2
  let isProduct := e.isAppOfArity ``QuantitativeArithmeticSparsePolynomialCertificate.product 2
  if isMerge || isProduct then
    let left ← normalize boundProducts e.getAppArgs[0]!
    let right ← normalize boundProducts e.getAppArgs[1]!
    let data := if isMerge then merge (left.data.length + right.data.length) left.data right.data
                else multiply left.data right.data
    let expr ← literal data
    let op := e.getAppFn
    let operation ← if boundProducts && isProduct && left.data.length * right.data.length > 1024 then
      pure (← normalizeProduct left.data left.expr right.data).proof
      else if boundProducts && isMerge then
        pure (← normalizeMerge (left.data.length + right.data.length) left.data right.data).proof
      else decideEq (mkApp2 op left.expr right.expr) expr
    let congruence ← mkAppM ``congrArg₂ #[op, left.proof, right.proof]
    let proof ← mkAppM ``Eq.trans #[congruence, operation]
    return ⟨data, expr, ← checked (← mkEq e expr) proof⟩
  else
    let reduced ← withTransparency .all <| reduce e
    let data ← decode reduced
    let expr ← literal data
    return ⟨data, expr, ← decideEq e expr⟩

private def solve (boundProducts : Bool) : TacticM Unit := do
  closeMainGoalUsing `staged_sparse_certificate fun type _ => withLiterals do
    let type ← instantiateMVars type
    if type.hasFVar || type.hasMVar then throwError "Expected a closed identity"
    unless type.isAppOfArity ``Eq 3 do throwError "Expected an equality"
    let lhs := type.getAppArgs[1]!
    let rhs := type.getAppArgs[2]!
    let result ← normalize boundProducts lhs
    let last ← decideEq result.expr rhs
    checked type (← mkAppM ``Eq.trans #[result.proof, last])

elab "staged_sparse_certificate" : tactic => solve false
elab "bounded_sparse_certificate" : tactic => solve true

/-- Separate coefficient extraction from sorting. In particular the sorting
recursion never repeatedly expands the original, much larger input table. -/
elab "sliced_sparse_certificate" : tactic => do
  closeMainGoalUsing `sliced_sparse_certificate fun type _ => withLiterals do
    let type ← instantiateMVars type
    if type.hasFVar || type.hasMVar then throwError "Expected a closed identity"
    unless type.isAppOfArity ``Eq 3 do throwError "Expected an equality"
    let lhs := type.getAppArgs[1]!
    let rhs := type.getAppArgs[2]!
    unless lhs.isAppOfArity ``SmallLevelSparsePolynomialNormalize.normalize 2 do
      throwError "Expected bounded sparse normalization"
    let input := lhs.getAppArgs[1]!
    unless input.isAppOfArity ``SmallLevelSparseCoefficientPartition.slice 2 do
      throwError "Expected coefficient extraction"
    let result ← extract input.getAppArgs[0]! input.getAppArgs[1]!
    let literal := result.expr
    let extracted := result.proof
    let operation := mkApp lhs.getAppFn lhs.getAppArgs[0]!
    let congruence ← mkAppM ``congrArg #[operation, extracted]
    let sorted ← decideEq (mkApp operation literal) rhs
    checked type (← mkAppM ``Eq.trans #[congruence, sorted])

/-- Check concatenated data a block at a time, composing exact Boolean equalities. -/
private partial def boundedProof (n e : Expr) : MetaM Expr := do
  let mut expanded := e
  if e.isConst then
    if let .defnInfo info ← getConstInfo e.constName! then expanded := info.value
  let input := mkApp2 (mkConst ``SmallLevelSparseCoefficientPartition.bounded) n e
  let result := toExpr true
  if expanded.isAppOfArity ``HAppend.hAppend 6 || expanded.isAppOfArity ``List.append 3 then
    let args := expanded.getAppArgs
    let p := args[args.size-2]!
    let q := args[args.size-1]!
    let left ← boundedProof n p
    let right ← boundedProof n q
    let decomposition ← mkAppM ``sparse_bounded_append #[n,p,q]
    let congruence ← mkAppM ``congrArg₂ #[mkConst ``Bool.and, left, right]
    checked (← mkEq input result) (← mkAppM ``Eq.trans #[decomposition, congruence])
  else decideEq input result

elab "bounded_sparse_data" : tactic => do
  closeMainGoalUsing `bounded_sparse_data fun type _ => do
    let type ← instantiateMVars type
    if type.hasFVar || type.hasMVar then throwError "Expected a closed bound"
    unless type.isAppOfArity ``Eq 3 do throwError "Expected an equality"
    let lhs := type.getAppArgs[1]!
    unless lhs.isAppOfArity ``SmallLevelSparseCoefficientPartition.bounded 2 do
      throwError "Expected a sparse polynomial bound"
    let proof ← boundedProof lhs.getAppArgs[0]! lhs.getAppArgs[1]!
    checked type proof

end QuantitativeArithmeticSparseCertificateCompute
end
