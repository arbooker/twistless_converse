module

public import QuantitativeEulerEndpointActualTerminalPhysicalFilterV1
public import QuantitativeEulerEndpointPhysicalResidualV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTerminalExpression
open FinitenessCertificate FinitenessGlobalHeight AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointResidual
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- Approximate preservation of a terminal-supported operator under the
full-terminal finite recurrence. The initial identity incurs zero error. -/
theorem physical_residual (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n m : ℕ)
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hPE : holomorphicSum (unit A P) m*E=E)
    (hg : ∀ j<n,let U := holomorphicSum (unit A P) m
      let G := holomorphicSum (g j) m
      0≤G ∧ G≤1 ∧ U*G=G ∧ G*U=G)
    (hq : ∀ j<n,ScalarSharpening (q j))
    {δ : ℝ} (hδ : 0≤δ) (hgE : ∀ j<n,‖holomorphicSum (g j) m*E‖≤δ) :
    ‖holomorphicSum (iterate A P g L q n) m*E-E‖≤errorBudget L q n*δ := by
  induction n with
  | zero =>
    change ‖holomorphicSum (unit A P) m*E-E‖≤1*δ
    rw [hPE,sub_self,norm_zero,one_mul]
    exact hδ
  | succ n ih =>
    have hgn := hg n (by omega)
    have ho := physical_order A P g L q n m (fun j hj => hg j (by omega))
      (fun j hj => hq j (by omega))
    have hu := unit_physical_order A P m
    have he := ih (fun j hj => hg j (by omega)) (fun j hj => hq j (by omega))
      (fun j hj => hgE j (by omega))
    rw [physical_step]
    exact (QuantitativeEulerEndpointPhysicalCorner.sharpened_residual _ _ _ E
      (unit_physical_projection A P m) hu.1 hu.2 ho.2.2.2.1 ho.2.2.2.2
      hgn.2.2.1 hgn.2.2.2 ho.1 ho.2.1 hgn.1 hgn.2.1 hPE (L n) (q n) (hq n (by omega)).2.1).trans
      (errorBudget_step L q n hδ he (hgE n (by omega)))

#print axioms physical_residual
end QuantitativeEulerEndpointTerminalExpression

namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeHolomorphic AsymptoticFiniteBranch QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointResidual
open scoped MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem actualFiniteExpression_physical_residual (n h : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hPE : holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) (h+1)*E=E)
    {δ : ℝ} (hδ : 0≤δ)
    (hgE : ∀ j<n,‖holomorphicSum (actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (QuantitativeEulerEndpointCommonReconstruction.expression A P (NeZero.pos N) s e) j) (h+1)*E‖≤δ) :
    ‖holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) (h+1)*E-E‖≤
      errorBudget (fun j => power (effortAt A P e n
        (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*δ := by
  apply QuantitativeEulerEndpointTerminalExpression.physical_residual A P _ _ q n (h+1) E hPE _ hq hδ hgE
  intro j _
  have ho := actualGramExpressions_physical_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j (h+1)
    _ (QuantitativeEulerEndpointCommonReconstruction.physical_norm A P (NeZero.pos N) s e h)
  have hs := actualGramExpressions_physical_support A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j (h+1)
    _ (QuantitativeEulerEndpointCommonReconstruction.physical_right_terminal A P (NeZero.pos N) s e h)
  exact ⟨ho.1,ho.2,hs⟩

#print axioms actualFiniteExpression_physical_residual
end QuantitativeEulerEndpointBoundedIteration
