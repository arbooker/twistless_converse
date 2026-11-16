module

public import QuantitativeMaassRegularOriginalGramV1
public import QuantitativeMaassRegularTerminalResidualV1
public import QuantitativeMaassRawActualTerminalRegularFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointResidual
open QuantitativeEulerEndpointExponentialParameters
open QuantitativeMaass.RawCommonReconstruction QuantitativeMaass.RawPrepared
open QuantitativeMaass.EulerHilbert.FullTerminal
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem actualGramExpressions_regular_order_support (n j : ℕ) (s : ℝ) (x : UpperHalfPlane) :
    let U := regularSum (QuantitativeEulerEndpointTerminalExpression.unit A P) x
    let G := regularSum (actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (QuantitativeMaass.RawCommonReconstruction.expression A P (NeZero.pos N) s e) j) x
    0≤G ∧ G≤1 ∧ U*G=G ∧ G*U=G := by
  rw [actualGramExpressions_regular]
  let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
  let T : Expression := QuantitativeMaass.RawCommonReconstruction.expression A P (NeZero.pos N) s e
  have ho := QuantitativeMaass.RawPrepared.replacementGram_order A P e b.compact b.primes b.bound x
    (fun i => actualBlock_uncomposed_norm A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j i x)
    (regularSum T x) (regular_norm A P (NeZero.pos N) s e x)
  have hp : regularSum T x*regularSum (QuantitativeEulerEndpointTerminalExpression.unit A P) x=regularSum T x := by
    rw [QuantitativeEulerEndpointTerminalExpression.unit_regular]
    exact regular_right_terminal A P (NeZero.pos N) s e x
  exact ⟨ho.1,ho.2,QuantitativeMaass.RawPrepared.replacementGram_support A P e b.compact b.primes b.bound x (regularSum T x) _
    (QuantitativeEulerEndpointTerminalExpression.unit_regular_projection A P x) hp⟩

/-- The literal finite regular iterate preserves any terminal operator
whose exact reconstruction satisfies the original compact equations. -/
theorem actualFiniteExpression_regular_original_residual (n : ℕ) (s : ℝ) (q : ℕ→ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j)) (x : UpperHalfPlane) (E : Space→L[ℂ]Space)
    (hPE : regularSum (QuantitativeEulerEndpointTerminalExpression.unit A P) x*E=E)
    (hrows : ∀ (r : AsymptoticCompactObservationCount.Row N) (u : Set UpperHalfPlane) (hu : IsCompact u),
      AsymptoticRegularObservationRows.row (NeZero.pos N) r e hu
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+3) x*
          normalizedRegularAmbient A (NeZero.pos N) P e x*E=0) :
    ‖regularSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) x*E-E‖≤
      errorBudget (fun j => power (effortAt A P e n
        (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*
          (Real.exp (-8*s)*‖E‖) := by
  refine QuantitativeEulerEndpointTerminalExpression.regular_residual A P _ _ q n x E hPE ?_ hq
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg E)) ?_
  · intro j _
    exact actualGramExpressions_regular_order_support A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j s x
  · intro j _
    rw [actualGramExpressions_regular]
    let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
    have hh := replacementGram_original_residual A P e x
      (normalizedRegularAmbient A (NeZero.pos N) P e x) E hrows b.compact b.primes b.bound
      (fun i => actualBlock_uncomposed_norm A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j i x)
      (regularSum (QuantitativeMaass.RawCommonReconstruction.expression A P (NeZero.pos N) s e) x)
      (normalizedRegularAmbient_norm A (NeZero.pos N) P e x) (regular_norm A P (NeZero.pos N) s e x)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg E)
    have he := regular_error A P (NeZero.pos N) s e x
    linarith

#print axioms actualFiniteExpression_regular_original_residual
end QuantitativeMaass.RawBoundedIteration
