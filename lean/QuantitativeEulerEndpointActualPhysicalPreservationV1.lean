module

public import QuantitativeEulerEndpointActualPhysicalResidualV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNestedPerturbation
open Polynomial QuantitativeEulerEndpointResidual

theorem errorBudget_le_comparisonBudget (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) :
    errorBudget L q n≤comparisonBudget L q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hq := slopeMass_nonneg (q n)
    have hL : (0:ℝ)≤L n := Nat.cast_nonneg _
    have he : 0≤errorBudget L q n := by linarith [errorBudget_ge_one L q n]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (by linarith : 4+2*(L n:ℝ)≤4+3*(L n:ℝ)) (by positivity)) ih he (by positivity)

#print axioms errorBudget_le_comparisonBudget
end QuantitativeEulerEndpointNestedPerturbation

namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointResidual
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointNestedPerturbation
open QuantitativeEulerEndpointCommonReconstruction
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- Explicit original equations after the EXACT normalized reconstruction.
No filter or counting conclusion is part of these premises. -/
structure OriginalPhysicalSolution (n h : ℕ)
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) : Prop where
  terminal : holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) (h+1)*E=E
  baseline : ∀ j<n,
    let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
    ∀ i,holomorphicSum (originalBaselineExpression N e b.compact
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) i) (h+1)*physicalExact A P (NeZero.pos N) h e*E=0
  prime : ∀ j<n,
    let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
    ∀ i : Fin b.primes.length,holomorphicSum (originalPacketSequenceExpression b.compact
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos N (NeZero.pos N) (sign e.1)
      ((AsymptoticReconstructedCount.parameters A P).s+4) b.primes i) (h+1)*physicalExact A P (NeZero.pos N) h e*E=0

theorem actualFiniteExpression_original_residual (n h : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hsol : OriginalPhysicalSolution A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n h E) :
    ‖holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) (h+1)*E-E‖≤
      errorBudget (fun j => power (effortAt A P e n
        (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*
          (Real.exp (-8*s)*‖E‖) := by
  apply actualFiniteExpression_physical_residual A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n h s q hq E hsol.terminal (mul_nonneg (Real.exp_pos _).le (norm_nonneg E))
  intro j hj
  have hh := actualGramExpressions_original_residual A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n j (h+1) (expression A P (NeZero.pos N) s e) (physicalExact A P (NeZero.pos N) h e) E
    (physical_norm A P (NeZero.pos N) s e h) (physicalExact_norm A P (NeZero.pos N) h e)
    (hsol.baseline j hj) (hsol.prime j hj)
  have he := physical_error A P (NeZero.pos N) s e h
  change ‖holomorphicSum (expression A P (NeZero.pos N) s e) (h+1)-physicalExact A P (NeZero.pos N) h e‖≤Real.exp (-8*s)/2 at he
  apply hh.trans
  have hb : 2*‖holomorphicSum (expression A P (NeZero.pos N) s e) (h+1)-physicalExact A P (NeZero.pos N) h e‖≤
      Real.exp (-8*s) := by linarith
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg E)

/-- The same accuracy that pays the regular comparison budget pays the
physical original-equation residual; no new row-count factor appears. -/
theorem actualFiniteExpression_original_paid (n h : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n)))
    (E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hsol : OriginalPhysicalSolution A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n h E) :
    ‖holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (Real.exp ((K+1)*(4:ℝ)^n)) q) (h+1)*E-E‖≤(2/(4:ℝ)^n)*‖E‖ := by
  have he := actualFiniteExpression_original_residual A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n h (Real.exp ((K+1)*(4:ℝ)^n)) q hq E hsol
  have hb := (errorBudget_le_comparisonBudget _ q n).trans hbudget
  have hp := amplified_error_le hK (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) hb
  have hp' : errorBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*
      Real.exp (-8*Real.exp ((K+1)*(4:ℝ)^n))≤2/(4:ℝ)^n := by
    rw [show (2:ℝ)/(4:ℝ)^n=2*(1/(4:ℝ)^n) by ring]
    nlinarith only [hp]
  rw [←mul_assoc] at he
  exact he.trans (mul_le_mul_of_nonneg_right hp' (norm_nonneg E))

#print axioms actualFiniteExpression_original_residual
#print axioms actualFiniteExpression_original_paid
end QuantitativeEulerEndpointBoundedIteration
