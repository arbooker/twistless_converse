module

public import QuantitativeEulerEndpointActualPhysicalGramV1
public import QuantitativeEulerEndpointActualFiniteFilterV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointBernstein
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- Partial iteration at a fixed horizon n: the block family and the
common reconstruction are held fixed while the iteration index varies. -/
def actualFinitePrefix (n : ℕ) (s : ℝ) (q : ℕ → ℝ[X]) (j : ℕ) : Expression :=
  let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n
  let E := QuantitativeEulerEndpointCommonReconstruction.expression A P (NeZero.pos N) s e
  QuantitativeEulerEndpointTerminalExpression.iterate A P
    (actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E)
    (fun i => power (effortAt A P e n b i)) q j

theorem actualFinitePrefix_physical_order (n j h : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ i<j,ScalarSharpening (q i)) :
    let U := holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) (h+1)
    let F := holomorphicSum (actualFinitePrefix A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q j) (h+1)
    0≤F ∧ F≤1 ∧ F≤U ∧ U*F=F ∧ F*U=F := by
  apply QuantitativeEulerEndpointTerminalExpression.physical_order A P _ _ q j (h+1) _ hq
  intro i _
  have ho := actualGramExpressions_physical_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n i (h+1)
    _ (QuantitativeEulerEndpointCommonReconstruction.physical_norm A P (NeZero.pos N) s e h)
  have hs := actualGramExpressions_physical_support A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n i (h+1)
    _ (QuantitativeEulerEndpointCommonReconstruction.physical_right_terminal A P (NeZero.pos N) s e h)
  exact ⟨ho.1,ho.2,hs⟩

/-- The literal finite filter from the regular approximation theorem is
also a positive contraction supported on the entire physical terminal
source. All actual Gram hypotheses have been discharged. -/
theorem actualFiniteExpression_physical_order (n h : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j)) :
    let U := holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) (h+1)
    let F := holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) (h+1)
    0≤F ∧ F≤1 ∧ F≤U ∧ U*F=F ∧ F*U=F :=
  actualFinitePrefix_physical_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n n h s q hq

#print axioms actualFinitePrefix_physical_order
#print axioms actualFiniteExpression_physical_order
end QuantitativeEulerEndpointBoundedIteration
