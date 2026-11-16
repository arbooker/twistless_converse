module

public import QuantitativeMaassRawActualTerminalPhysicalFilterV1
public import QuantitativeEulerEndpointTerminalPhysicalResidualV1
public import QuantitativeEulerEndpointPhysicalResidualV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeMaass.RawBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeHolomorphic AsymptoticFiniteBranch QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointResidual
open scoped MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem actualFiniteExpression_physical_residual (n : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hPE : holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) 0*E=E)
    {δ : ℝ} (hδ : 0≤δ)
    (hgE : ∀ j<n,‖holomorphicSum (actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (QuantitativeMaass.RawCommonReconstruction.expression A P (NeZero.pos N) s e) j) 0*E‖≤δ) :
    ‖holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) 0*E-E‖≤
      errorBudget (fun j => power (effortAt A P e n
        (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*δ := by
  apply QuantitativeEulerEndpointTerminalExpression.physical_residual A P _ _ q n 0 E hPE _ hq hδ hgE
  intro j _
  have ho := actualGramExpressions_physical_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j 0
    _ (QuantitativeMaass.RawCommonReconstruction.physical_norm A P (NeZero.pos N) s e)
  have hs := actualGramExpressions_physical_support A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j 0
    _ (QuantitativeMaass.RawCommonReconstruction.physical_right_terminal A P (NeZero.pos N) s e)
  exact ⟨ho.1,ho.2,hs⟩

#print axioms actualFiniteExpression_physical_residual
end QuantitativeMaass.RawBoundedIteration
