module

public import QuantitativeEulerEndpointActualFiniteSectorComparisonV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointCommonReconstruction
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The actual finite regular expression is itself a positive terminal
contraction, independently of its comparison with the intrinsic iterate. -/
theorem actualFiniteExpression_regular_order (n : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j)) (x : UpperHalfPlane) :
    let U := regularSum (QuantitativeEulerEndpointTerminalExpression.unit A P) x
    let F := regularSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) x
    0≤F ∧ F≤1 ∧ F≤U ∧ U*F=F ∧ F*U=F := by
  apply QuantitativeEulerEndpointTerminalExpression.regular_order A P _ _ q n x _ hq
  intro j hj
  rw [actualGramExpressions_regular]
  let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
  let E := expression A P (NeZero.pos N) s e
  have ho := replacementGram_order A P e b.compact b.primes b.bound x
    (fun i => actualBlock_uncomposed_norm A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j i x)
    (regularSum E x) (regular_norm A P (NeZero.pos N) s e x)
  have hp : regularSum E x*regularSum (QuantitativeEulerEndpointTerminalExpression.unit A P) x=regularSum E x := by
    rw [QuantitativeEulerEndpointTerminalExpression.unit_regular]
    exact regular_right_terminal A P (NeZero.pos N) s e x
  have hs := replacementGram_support A P e b.compact b.primes b.bound x (regularSum E x) _
    (QuantitativeEulerEndpointTerminalExpression.unit_regular_projection A P x) hp
  exact ⟨ho.1,ho.2,hs⟩

#print axioms actualFiniteExpression_regular_order
end QuantitativeEulerEndpointBoundedIteration
