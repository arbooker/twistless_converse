module

public import QuantitativeEulerEndpointActualCommonFilterV1
public import AsymptoticSignedCornerContinuityV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTerminalExpression
open FinitenessCertificate FinitenessGlobalHeight AsymptoticFiniteBranch Polynomial
open QuantitativeEulerEndpointTerminalAlgebra
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

theorem iterate_regular_right_support (g : ℕ → Expression) (L : ℕ → ℕ)
    (q : ℕ → ℝ[X]) (n : ℕ) (x : UpperHalfPlane) :
    regularSum (iterate A P g L q n) x*regularSum (unit A P) x=
      regularSum (iterate A P g L q n) x := by
  have hp := (unit_regular_projection A P x).isIdempotentElem.eq
  cases n with
  | zero => exact hp
  | succ n => rw [regular_step,mul_assoc,hp]

/-- Uniform finite-expression error costs exactly the terminal area in
rooted trace. Integrability and measurability are proved internally. -/
theorem trace_error (a : Algebra A P) (E : Expression) (δ : ℝ)
    (hs : ∀ x,regularSum E x*regularSum (unit A P) x=regularSum E x)
    (he : ∀ x,‖rep A P a x-regularSum E x‖≤δ) :
    ‖tr A P a-AsymptoticRegularTrace.signedTrace MeasureTheory.volume (regularSum E)‖≤
      δ*(AsymptoticReconstructedCount.parameters A P).ε⁻¹ := by
  have hh := AsymptoticRegularTrace.norm_signedTrace_sub_le_corner
    QuantitativeEulerEndpointRegularBase.measure (terminal_measurable A P) (terminal_finite A P)
    (rep A P a) (regularSum E)
    (QuantitativeSpectralRegularAlgebra.representation_matrix_measurable _ _ _ _ _ a 1 1)
    (QuantitativeHolomorphic.regularSum_matrix_measurable E 1 1)
    (QuantitativeSpectralRegularAlgebra.representation_norm_le _ _ _ _ _ a)
    (regularSum_norm_le E)
    (QuantitativeSpectralRegularAlgebra.representation_supported _ _ _ _ _ a)
    (fun x => by
      have hx := hs x
      rw [unit_regular] at hx
      exact hx) he
  rw [terminal_area,ENNReal.toReal_ofReal (inv_nonneg.mpr
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le)] at hh
  exact hh

#print axioms iterate_regular_right_support
#print axioms trace_error
end QuantitativeEulerEndpointTerminalExpression

namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointTerminalAlgebra QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointNestedPerturbation
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem actualFiniteExpression_trace_error (n : ℕ) (s : ℝ) (F : ℕ → Algebra A P) (q : ℕ → ℝ[X])
    (hinit : F 0=1) (hF : ∀ j<n,0≤F j ∧ F j≤1)
    (hrec : ∀ j<n,F (j+1)=nextAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j (F j) (q j))
    (hq : ∀ j<n,ScalarSharpening (q j)) :
    ‖tr A P (F n)-AsymptoticRegularTrace.signedTrace MeasureTheory.volume
      (regularSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q))‖≤
      (comparisonBudget (fun j => power (effortAt A P e n
        (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*Real.exp (-8*s))*
          (AsymptoticReconstructedCount.parameters A P).ε⁻¹ := by
  apply QuantitativeEulerEndpointTerminalExpression.trace_error A P (F n) _ _
  · exact QuantitativeEulerEndpointTerminalExpression.iterate_regular_right_support A P _ _ q n
  · exact actualFiniteExpression_error A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n s F q hinit hF hrec hq

#print axioms actualFiniteExpression_trace_error
end QuantitativeEulerEndpointBoundedIteration
