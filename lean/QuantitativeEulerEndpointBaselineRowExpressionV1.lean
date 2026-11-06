module

public import QuantitativeEulerEndpointWideRowExpressionsV1
public import AsymptoticFiniteBranchRowsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic AsymptoticSectorSigns
open AsymptoticRegularObservationRows QuantitativeArithmetic QuantitativeEulerDensityGenerators
open scoped Classical

def baselineMatrixSize (N : ℕ) [NeZero N] : NewBaselineIndex N → ℕ
  | .inl none => N
  | .inl (some a) => N*(primeLift N a).q^3
  | .inr p => p.val

def baselineMatrixHeight (N : ℕ) [NeZero N] (R Y H : ℝ) (i : NewBaselineIndex N) : ℝ :=
  4*(1+(wideCompactCutoff (baselineMatrixSize N i) R Y H:ℝ))*(baselineMatrixSize N i:ℝ)

def originalBaselineExpression (N : ℕ) [NeZero N] (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) : NewBaselineIndex N → Expression
  | .inl none => compactFamilyExpression (twistBranches N 1 (NeZero.pos N) Nat.zero_lt_one)
      (Sum.elim (fun _ => (1:ℂ)) (fun _ => -sign sector.1)) hs hε t
  | .inl (some a) => compactFamilyExpression (twistBranches N (primeLift N a).q
      (NeZero.pos N) (primeLift N a).prime.pos)
      (Sum.elim (fun _ => (1:ℂ)) (fun _ => -sign sector.1)) hs hε t
  | .inr p => compactFamilyExpression (ramifiedBranches p.val (Nat.mem_primeFactors.mp p.property).1.pos)
      (Sum.elim (fun _ => (1:ℂ)) (fun _ => -AsymptoticCylinderRamified.eigenvalue sector p.val)) hs hε t

variable {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H)

include hY hre hlo hhi in
theorem exists_baseline_row_expression (N : ℕ) [NeZero N] (sector : Sector N) (t : ℕ)
    (i : NewBaselineIndex N) :
    ∃ E : Expression, (∀ x, regularSum E x=newBaselineRows N sector hs hε t x i) ∧
      (∀ m,holomorphicSum E m=holomorphicSum (originalBaselineExpression N sector hs hε t i) m) ∧
      expressionBound E≤wideBaselineRowBound N sector R Y H t i ∧
      ExpressionMatrixBound E (baselineMatrixHeight N R Y H i) := by
  cases i with
  | inl i =>
    cases i with
    | none =>
      simpa only [newBaselineRows,baselineRows,originalBaselineExpression,wideBaselineRowBound,
        baselineMatrixHeight,baselineMatrixSize,Nat.one_pow,Nat.mul_one] using
        exists_twist_expression hs hε hY hre hlo hhi N 1 (NeZero.pos N) Nat.zero_lt_one (sign sector.1) t
    | some a =>
      exact exists_twist_expression hs hε hY hre hlo hhi N (primeLift N a).q
        (NeZero.pos N) (primeLift N a).prime.pos (sign sector.1) t
  | inr p =>
    exact exists_ramified_expression hs hε hY hre hlo hhi p.val
      (Nat.mem_primeFactors.mp p.property).1.pos (AsymptoticCylinderRamified.eigenvalue sector p.val) t

include hY hre hlo hhi in
theorem exists_baseline_expressions (N : ℕ) [NeZero N] (sector : Sector N) (t : ℕ) :
    ∃ E : NewBaselineIndex N → Expression, ∀ i,
      (∀ x, regularSum (E i) x=newBaselineRows N sector hs hε t x i) ∧
      (∀ m,holomorphicSum (E i) m=holomorphicSum (originalBaselineExpression N sector hs hε t i) m) ∧
      expressionBound (E i)≤wideBaselineRowBound N sector R Y H t i ∧
      ExpressionMatrixBound (E i) (baselineMatrixHeight N R Y H i) := by
  choose E hE using exists_baseline_row_expression hs hε hY hre hlo hhi N sector t
  exact ⟨E,hE⟩

#print axioms exists_baseline_row_expression
#print axioms exists_baseline_expressions
end QuantitativeEulerEndpointPrepared
