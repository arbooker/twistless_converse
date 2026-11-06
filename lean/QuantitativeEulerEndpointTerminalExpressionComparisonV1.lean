module

public import QuantitativeEulerEndpointTerminalExpressionIterationV1
public import QuantitativeEulerEndpointComparisonIterationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTerminalExpression
open FinitenessCertificate FinitenessGlobalHeight AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointTerminalAlgebra QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointNestedPerturbation
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- Compare a finite expression on the entire terminal source with an
intrinsic terminal-algebra iteration. Only the Gram approximations incur
error; the terminal identity is represented exactly. -/
theorem regular_comparison (F G : ℕ → Algebra A P) (g : ℕ → Expression)
    (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) (x : UpperHalfPlane)
    (hinit : F 0=1) (hF : ∀ j<n,0≤F j ∧ F j≤1) (hG : ∀ j<n,0≤G j ∧ G j≤1)
    (hrec : ∀ j<n,F (j+1)=aeval
      (QuantitativeEulerEndpointSoftUpdate.update (F j) (F j*G j*F j) (L j)) (q j))
    (hg : ∀ j<n,let U := regularSum (unit A P) x
      let T := regularSum (g j) x
      0≤T ∧ T≤1 ∧ U*T=T ∧ T*U=T)
    (hq : ∀ j<n,ScalarSharpening (q j))
    {δ : ℝ} (hδ : 0≤δ) (herror : ∀ j<n,‖rep A P (G j) x-regularSum (g j) x‖≤δ) :
    ‖rep A P (F n) x-regularSum (iterate A P g L q n) x‖≤comparisonBudget L q n*δ := by
  apply iteration_difference (fun j => rep A P (F j) x)
    (fun j => regularSum (iterate A P g L q j) x)
    (fun j => rep A P (G j) x) (fun j => regularSum (g j) x) L q n hδ
  · change ‖rep A P (F 0) x-regularSum (unit A P) x‖≤δ
    rw [hinit,unit_regular,sub_self,norm_zero]
    exact hδ
  · intro j hj
    exact rep_order A P (F j) (hF j hj) x
  · intro j hj
    have h := regular_order A P g L q j x (fun i hi => hg i (by omega))
      (fun i hi => hq i (by omega))
    exact ⟨h.1,h.2.1⟩
  · intro j hj
    exact rep_order A P (G j) (hG j hj) x
  · intro j hj
    exact ⟨(hg j hj).1,(hg j hj).2.1⟩
  · intro j hj
    rw [hrec j hj]
    exact rep_sharpened_ambient A P (F j) (G j) (L j) (q j) (hq j hj).1 x
  · intro j hj
    exact regular_ambient_step A P g L q j x (fun i hi => hg i (by omega))
      (fun i hi => hq i (by omega))
  · exact herror

/-- Exact complexity bound for the same full-terminal expression, retaining
all actual Gram and polynomial coefficient costs as finite-horizon inputs. -/
theorem bounds (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X])
    {B a b : ℝ} (hB : 16≤B) (n : ℕ)
    (hg : ∀ j<n,expressionBound (g j)≤B) (hgM : ∀ j<n,ExpressionMatrixBound (g j) B)
    (hq : ∀ j<n,(∑ i∈(q j).support,|(q j).coeff i|)≤B)
    (ha : (∑ j∈Finset.range n,QuantitativeEulerEndpointNestedExpression.logarithmicCost L q j)≤a)
    (hb : Real.log B≤Real.exp b) :
    expressionBound (iterate A P g L q n)≤Real.exp (Real.exp (a+b)) ∧
    ExpressionMatrixBound (iterate A P g L q n) (Real.exp (Real.exp (a+b))) := by
  have h1 : (1:ℝ)≤B := by linarith
  exact QuantitativeEulerEndpointNestedExpression.bounds_double_exp_upto
    (unit A P) (unit A P) g L q hB (unit_mass A P).le (unit_matrix A P)
    ((unit_mass A P).le.trans h1) ((unit_matrix A P).mono h1) n hg hgM hq ha hb

#print axioms regular_comparison
#print axioms bounds
end QuantitativeEulerEndpointTerminalExpression
