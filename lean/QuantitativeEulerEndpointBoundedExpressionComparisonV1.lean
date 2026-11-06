module

public import QuantitativeEulerEndpointTerminalExpressionComparisonV1
public import QuantitativeEulerEndpointReplacementGramSupportV1
public import QuantitativeEulerEndpointCommonReconstructionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra QuantitativeHolomorphic
open AsymptoticFiniteBranch QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointNestedPerturbation
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (n : ℕ) (b : ℕ → Block A P e)

/-- A single common reconstruction realizes the finite iteration on the
whole terminal source. Raw row bounds, already proved for actualBlock,
discharge every Gram order condition; the error is explicit. -/
theorem common_expression_comparison (s : ℝ) (F : ℕ → Algebra A P)
    (q : ℕ → ℝ[X]) (g : ℕ → Expression)
    (hinit : F 0=1) (hF : ∀ j<n,0≤F j ∧ F j≤1)
    (hrec : ∀ j<n,F (j+1)=nextAt A P e n b j (F j) (q j))
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hraw : ∀ j<n,∀ i x,‖uncomposedCombinedRows A P e (b j).compact (b j).primes i x‖≤(b j).bound i)
    (hg : ∀ j<n,∀ x,regularSum (g j) x=
      replacementGram A P e (b j).compact (b j).primes (b j).bound x
        (regularSum (QuantitativeEulerEndpointCommonReconstruction.expression A P (NeZero.pos N) s e) x))
    (x : UpperHalfPlane) :
    ‖rep A P (F n) x-regularSum (QuantitativeEulerEndpointTerminalExpression.iterate A P g
      (fun j => power (effortAt A P e n b j)) q n) x‖≤
      comparisonBudget (fun j => power (effortAt A P e n b j)) q n*Real.exp (-8*s) := by
  let E := QuantitativeEulerEndpointCommonReconstruction.expression A P (NeZero.pos N) s e
  let G (j : ℕ) := QuantitativeEulerEndpointBoundedTerminal.gram A P e
    (b j).compact (b j).primes (b j).bound (b j).norm_bound
  have hEn := QuantitativeEulerEndpointCommonReconstruction.regular_norm A P (NeZero.pos N) s e x
  have hEp : regularSum E x*regularSum (QuantitativeEulerEndpointTerminalExpression.unit A P) x=
      regularSum E x := by
    rw [QuantitativeEulerEndpointTerminalExpression.unit_regular]
    exact QuantitativeEulerEndpointCommonReconstruction.regular_right_terminal A P (NeZero.pos N) s e x
  have hT (j : ℕ) (hj : j<n) :
      let U := regularSum (QuantitativeEulerEndpointTerminalExpression.unit A P) x
      let T := regularSum (g j) x
      0≤T ∧ T≤1 ∧ U*T=T ∧ T*U=T := by
    rw [hg j hj]
    have ho := replacementGram_order A P e (b j).compact (b j).primes (b j).bound x
      (fun i => hraw j hj i x) (regularSum E x) hEn
    have hs := replacementGram_support A P e (b j).compact (b j).primes (b j).bound x
      (regularSum E x) _ (QuantitativeEulerEndpointTerminalExpression.unit_regular_projection A P x) hEp
    exact ⟨ho.1,ho.2,hs⟩
  apply QuantitativeEulerEndpointTerminalExpression.regular_comparison A P F G g
    (fun j => power (effortAt A P e n b j)) q n x hinit hF
    (fun j _ => QuantitativeEulerEndpointBoundedTerminal.gram_order A P e
      (b j).compact (b j).primes (b j).bound (b j).norm_bound) hrec hT hq (Real.exp_pos _).le
  intro j hj
  rw [hg j hj]
  have hd := replacementGram_difference A P e (b j).compact (b j).primes (b j).bound x
    (fun i => hraw j hj i x) _ (regularSum E x)
    (normalizedRegularAmbientCountReconstruction_norm_le A (NeZero.pos N) P e x) hEn
  have he := QuantitativeEulerEndpointCommonReconstruction.regular_error A P (NeZero.pos N) s e x
  change ‖rep A P (G j) x-_‖≤_
  dsimp only [G]
  rw [replacementGram_exact,norm_sub_rev]
  exact hd.trans (by linarith)

#print axioms common_expression_comparison
end QuantitativeEulerEndpointBoundedIteration
