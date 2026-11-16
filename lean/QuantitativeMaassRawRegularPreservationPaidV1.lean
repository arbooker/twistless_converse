module

public import QuantitativeMaassRawRegularPreservationV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointResidual
open QuantitativeEulerEndpointNestedPerturbation
open QuantitativeEulerEndpointExponentialParameters
open QuantitativeMaass.EulerHilbert.FullTerminal
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem actualFiniteExpression_regular_original_paid (n : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ→ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n)))
    (x : UpperHalfPlane) (E : Space→L[ℂ]Space)
    (hPE : regularSum (QuantitativeEulerEndpointTerminalExpression.unit A P) x*E=E)
    (hrows : ∀ (r : AsymptoticCompactObservationCount.Row N) (u : Set UpperHalfPlane) (hu : IsCompact u),
      AsymptoticRegularObservationRows.row (NeZero.pos N) r e hu
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+3) x*
          normalizedRegularAmbient A (NeZero.pos N) P e x*E=0) :
    ‖regularSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (Real.exp ((K+1)*(4:ℝ)^n)) q) x*E-E‖≤(2/(4:ℝ)^n)*‖E‖ := by
  have he := actualFiniteExpression_regular_original_residual A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n (Real.exp ((K+1)*(4:ℝ)^n)) q hq x E hPE hrows
  have hb := (errorBudget_le_comparisonBudget _ q n).trans hbudget
  have hp := QuantitativeEulerEndpointCommonReconstruction.amplified_error_le hK
    (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) hb
  have hp' : errorBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*
      Real.exp (-8*Real.exp ((K+1)*(4:ℝ)^n))≤2/(4:ℝ)^n := by
    rw [show (2:ℝ)/(4:ℝ)^n=2*(1/(4:ℝ)^n) by ring]
    nlinarith only [hp]
  rw [←mul_assoc] at he
  exact he.trans (mul_le_mul_of_nonneg_right hp' (norm_nonneg E))

#print axioms actualFiniteExpression_regular_original_paid
end QuantitativeMaass.RawBoundedIteration
