module

public import QuantitativeEulerEndpointTerminalExpressionIterationV1
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
theorem regular_residual (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) (x : UpperHalfPlane)
    (E : AsymptoticRegularCompactBranch.Space →L[ℂ] AsymptoticRegularCompactBranch.Space)
    (hPE : regularSum (unit A P) x*E=E)
    (hg : ∀ j<n,let U := regularSum (unit A P) x
      let G := regularSum (g j) x
      0≤G ∧ G≤1 ∧ U*G=G ∧ G*U=G)
    (hq : ∀ j<n,ScalarSharpening (q j))
    {δ : ℝ} (hδ : 0≤δ) (hgE : ∀ j<n,‖regularSum (g j) x*E‖≤δ) :
    ‖regularSum (iterate A P g L q n) x*E-E‖≤errorBudget L q n*δ := by
  induction n with
  | zero =>
    change ‖regularSum (unit A P) x*E-E‖≤1*δ
    rw [hPE,sub_self,norm_zero,one_mul]
    exact hδ
  | succ n ih =>
    have hgn := hg n (by omega)
    have ho := regular_order A P g L q n x (fun j hj => hg j (by omega))
      (fun j hj => hq j (by omega))
    have hu := unit_regular_order A P x
    have he := ih (fun j hj => hg j (by omega)) (fun j hj => hq j (by omega))
      (fun j hj => hgE j (by omega))
    rw [regular_step]
    exact (QuantitativeEulerEndpointPhysicalCorner.sharpened_residual _ _ _ E
      (unit_regular_projection A P x) hu.1 hu.2 ho.2.2.2.1 ho.2.2.2.2
      hgn.2.2.1 hgn.2.2.2 ho.1 ho.2.1 hgn.1 hgn.2.1 hPE (L n) (q n) (hq n (by omega)).2.1).trans
      (errorBudget_step L q n hδ he (hgE n (by omega)))

#print axioms regular_residual
end QuantitativeEulerEndpointTerminalExpression
