module

public import QuantitativeMaassRawActualPhysicalResidualV1
public import QuantitativeEulerEndpointActualPhysicalPreservationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeMaass.RawBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointResidual
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointNestedPerturbation
open QuantitativeMaass.RawCommonReconstruction
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- Explicit original equations after the EXACT normalized reconstruction.
No filter or counting conclusion is part of these premises. -/
structure OriginalPhysicalSolution (n : ℕ)
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) : Prop where
  terminal : holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) 0*E=E
  baseline : ∀ j<n,
    let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
    ∀ i,holomorphicSum (originalBaselineExpression N e b.compact
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) i) 0*physicalExact A P (NeZero.pos N) e*E=0
  prime : ∀ j<n,
    let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
    ∀ i : Fin b.primes.length,holomorphicSum (originalPacketSequenceExpression b.compact
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos N (NeZero.pos N) (sign e.1)
      ((AsymptoticReconstructedCount.parameters A P).s+3) b.primes i) 0*physicalExact A P (NeZero.pos N) e*E=0

theorem actualFiniteExpression_original_residual (n : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hsol : OriginalPhysicalSolution A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E) :
    ‖holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) 0*E-E‖≤
      errorBudget (fun j => power (effortAt A P e n
        (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*
          (Real.exp (-8*s)*‖E‖) := by
  apply actualFiniteExpression_physical_residual A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n s q hq E hsol.terminal (mul_nonneg (Real.exp_pos _).le (norm_nonneg E))
  intro j hj
  have hh := actualGramExpressions_original_residual A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n j 0 (expression A P (NeZero.pos N) s e) (physicalExact A P (NeZero.pos N) e) E
    (physical_norm A P (NeZero.pos N) s e) (physicalExact_norm A P (NeZero.pos N) e)
    (hsol.baseline j hj) (hsol.prime j hj)
  have he := physical_error A P (NeZero.pos N) s e
  change ‖holomorphicSum (expression A P (NeZero.pos N) s e) 0-physicalExact A P (NeZero.pos N) e‖≤Real.exp (-8*s)/2 at he
  apply hh.trans
  have hb : 2*‖holomorphicSum (expression A P (NeZero.pos N) s e) 0-physicalExact A P (NeZero.pos N) e‖≤
      Real.exp (-8*s) := by linarith
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg E)

/-- The same accuracy that pays the regular comparison budget pays the
physical original-equation residual; no new row-count factor appears. -/
theorem actualFiniteExpression_original_paid (n : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n)))
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hsol : OriginalPhysicalSolution A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E) :
    ‖holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (Real.exp ((K+1)*(4:ℝ)^n)) q) 0*E-E‖≤(2/(4:ℝ)^n)*‖E‖ := by
  have he := actualFiniteExpression_original_residual A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n (Real.exp ((K+1)*(4:ℝ)^n)) q hq E hsol
  have hb := (errorBudget_le_comparisonBudget _ q n).trans hbudget
  have hp := QuantitativeEulerEndpointCommonReconstruction.amplified_error_le hK (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) hb
  have hp' : errorBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*
      Real.exp (-8*Real.exp ((K+1)*(4:ℝ)^n))≤2/(4:ℝ)^n := by
    rw [show (2:ℝ)/(4:ℝ)^n=2*(1/(4:ℝ)^n) by ring]
    nlinarith only [hp]
  rw [←mul_assoc] at he
  exact he.trans (mul_le_mul_of_nonneg_right hp' (norm_nonneg E))

#print axioms actualFiniteExpression_original_residual
#print axioms actualFiniteExpression_original_paid
end QuantitativeMaass.RawBoundedIteration
