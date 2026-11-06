module

public import QuantitativeArithmeticRetainedFinitePacketV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra QuantitativeHolomorphic
open AsymptoticFiniteBranch QuantitativeEulerEndpointBernstein
open QuantitativeArithmeticRetainedPacket
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointNestedPerturbation
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)
    (hR₀ : ∀p∈R₀,p.Prime) (e : Sector N) (n : ℕ) (b : ℕ → Block A P hR₀ e)

/-- A single common reconstruction realizes the finite iteration on the
whole terminal source. Raw row bounds, already proved for actualBlock,
discharge every Gram order condition; the error is explicit. -/
theorem common_expression_comparison (s : ℝ) (F : ℕ → Algebra A P)
    (q : ℕ → ℝ[X]) (g : ℕ → Expression)
    (hinit : F 0=1) (hF : ∀ j<n,0≤F j ∧ F j≤1)
    (hrec : ∀ j<n,F (j+1)=nextAt A P hR₀ e n b j (F j) (q j))
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hraw : ∀ j<n,∀ i x,‖uncomposedCombinedRows A P e (b j).compact (b j).primes i x‖≤(b j).bound i)
    (hg : ∀ j<n,∀ x,regularSum (g j) x=
      replacementGram A P e (b j).compact (b j).primes (b j).bound x
        (regularSum (QuantitativeArithmeticRetainedCommonExpression.expression A P hR₀ (NeZero.pos N) s e) x))
    (x : UpperHalfPlane) :
    ‖rep A P (F n) x-regularSum (QuantitativeArithmeticRetainedExpressionIteration.iterate A P g
      (fun j => power (effortAt A P hR₀ e n b j)) q n) x‖≤
      comparisonBudget (fun j => power (effortAt A P hR₀ e n b j)) q n*Real.exp (-8*s) := by
  let E := QuantitativeArithmeticRetainedCommonExpression.expression A P hR₀ (NeZero.pos N) s e
  let G (j : ℕ) := QuantitativeArithmeticRetainedPacket.gram A P hR₀ e
    (b j).compact (b j).primes (b j).bound (b j).norm_bound
  have hEn := QuantitativeArithmeticRetainedCommonExpression.regular_norm A P hR₀ (NeZero.pos N) s e x
  have hEp : regularSum E x*regularSum (QuantitativeArithmeticRetainedExpressionIteration.unit A P) x=
      regularSum E x := by
    exact QuantitativeArithmeticRetainedCommonExpression.regular_right_terminal A P hR₀ (NeZero.pos N) s e x
  have hT (j : ℕ) (hj : j<n) :
      let U := regularSum (QuantitativeArithmeticRetainedExpressionIteration.unit A P) x
      let T := regularSum (g j) x
      0≤T ∧ T≤1 ∧ U*T=T ∧ T*U=T := by
    rw [hg j hj]
    have ho := replacementGram_order A P e (b j).compact (b j).primes (b j).bound x
      (fun i => hraw j hj i x) (regularSum E x) hEn
    have hs := replacementGram_support A P e (b j).compact (b j).primes (b j).bound x
      (regularSum E x) _ (QuantitativeArithmeticRetainedExpressionIteration.unit_regular_projection A P x) hEp
    exact ⟨ho.1,ho.2,hs⟩
  apply QuantitativeArithmeticRetainedExpressionIteration.regular_comparison A P F G g
    (fun j => power (effortAt A P hR₀ e n b j)) q n x hinit hF
    (fun j _ => QuantitativeArithmeticRetainedPacket.gram_order A P hR₀ e
      (b j).compact (b j).primes (b j).bound (b j).norm_bound) hrec hT hq (Real.exp_pos _).le
  intro j hj
  rw [hg j hj]
  have hd := replacementGram_difference A P e (b j).compact (b j).primes (b j).bound x
    (fun i => hraw j hj i x) _ (regularSum E x)
    (QuantitativeArithmeticRetainedFilterExpression.regularAmbient_norm A P hR₀ (NeZero.pos N) e x) hEn
  have he := QuantitativeArithmeticRetainedCommonExpression.regular_error A P hR₀ (NeZero.pos N) s e x
  change ‖rep A P (G j) x-_‖≤_
  dsimp only [G]
  rw [QuantitativeArithmeticRetainedPacket.replacementGram_exact,norm_sub_rev]
  exact hd.trans (by linarith)

#print axioms common_expression_comparison
end QuantitativeArithmeticRetainedIteration
