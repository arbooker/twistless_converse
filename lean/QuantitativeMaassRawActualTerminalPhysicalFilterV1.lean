module

public import QuantitativeMaassRawActualPhysicalGramV1
public import QuantitativeMaassRawActualFiniteFilterV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeMaass.RawBoundedIteration
open QuantitativeMaass.RawPrepared
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
  let E := QuantitativeMaass.RawCommonReconstruction.expression A P (NeZero.pos N) s e
  QuantitativeEulerEndpointTerminalExpression.iterate A P
    (actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E)
    (fun i => power (effortAt A P e n b i)) q j

theorem actualFinitePrefix_physical_order (n j : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ i<j,ScalarSharpening (q i)) :
    let U := holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) 0
    let F := holomorphicSum (actualFinitePrefix A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q j) 0
    0≤F ∧ F≤1 ∧ F≤U ∧ U*F=F ∧ F*U=F := by
  apply QuantitativeEulerEndpointTerminalExpression.physical_order A P _ _ q j 0 _ hq
  intro i _
  have ho := actualGramExpressions_physical_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n i 0
    _ (QuantitativeMaass.RawCommonReconstruction.physical_norm A P (NeZero.pos N) s e)
  have hs := actualGramExpressions_physical_support A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n i 0
    _ (QuantitativeMaass.RawCommonReconstruction.physical_right_terminal A P (NeZero.pos N) s e)
  exact ⟨ho.1,ho.2,hs⟩

/-- The literal finite filter from the regular approximation theorem is
also a positive contraction supported on the entire physical terminal
source. All actual Gram hypotheses have been discharged. -/
theorem actualFiniteExpression_physical_order (n : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j)) :
    let U := holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) 0
    let F := holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) 0
    0≤F ∧ F≤1 ∧ F≤U ∧ U*F=F ∧ F*U=F :=
  actualFinitePrefix_physical_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n n s q hq

#print axioms actualFinitePrefix_physical_order
#print axioms actualFiniteExpression_physical_order
end QuantitativeMaass.RawBoundedIteration
