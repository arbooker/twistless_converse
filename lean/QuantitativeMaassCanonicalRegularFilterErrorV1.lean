module

public import QuantitativeMaassCanonicalCapSourceV1
public import QuantitativeMaassRawRegularPreservationPaidV1
public import QuantitativeMaassRawReconstructedSourceErrorV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointResidual
open QuantitativeEulerEndpointNestedPerturbation
open QuantitativeEulerEndpointExponentialParameters ContinuousLinearMap
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups
namespace QuantitativeMaass.RawBoundedIteration
open QuantitativeMaass.RawCommonReconstruction QuantitativeMaass.EulerHilbert.FullTerminal
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN2 : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The actual reconstructed finite filter approximately fixes the canonical
cap-space projection, with coefficient one and all original rows discharged. -/
theorem actualFiniteExpression_canonical_reconstructed_error
    {hN : GridAdmissibleGap.Admissible N} (cover : AdmissibleScalarCover N hN)
    (n : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ→ℝ[X]) (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN2 excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n)))
    (x : UpperHalfPlane) (hx : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • x)) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let s := Real.exp ((K+1)*(4:ℝ)^n)
    let T := actualFiniteExpression A P e hN2 excluded threshold S hS W B Bg D H₀ G C Kobs n s q
    let Qcap : Space→L[ℂ]Space := (cover.regularCapSpace P'.epsilon_pos (by omega : 1≤P'.s+3) e x).starProjection
    ‖regularSum (reconstructedFilterExpression A P e s T) x*Qcap-Qcap‖≤2/(4:ℝ)^n+Real.exp (-8*s) := by
  intro P' s T Qcap
  let R : Space→L[ℂ]Space := normalizedRegularAmbient A (NeZero.pos N) P e x
  let V : Space→L[ℂ]Space := regularSum (expression A P (NeZero.pos N) s e) x
  let E : Space→L[ℂ]Space := R.adjoint*Qcap*R
  have hQ : IsStarProjection Qcap := isStarProjection_starProjection
  have hQnorm : ‖Qcap‖≤1 := (cover.regularCapSpace P'.epsilon_pos (by omega : 1≤P'.s+3) e x).starProjection_norm_le
  have hRQ : R*R.adjoint*Qcap=Qcap := cover.regularCapSpace_cogram_fixed A P e x hx
  have hpull := projection_source_pullback R Qcap hQ hRQ
  have hR : ‖R‖≤1 := normalizedRegularAmbient_norm A (NeZero.pos N) P e x
  have hE : ‖E‖≤1 := projection_source_pullback_norm R Qcap hR hQnorm
  have hPE : regularSum (QuantitativeEulerEndpointTerminalExpression.unit A P) x*E=E := by
    rw [QuantitativeEulerEndpointTerminalExpression.unit_regular]
    change AsymptoticOrbitDiagonal.corner (AsymptoticCertificateOperators.highStrip P'.ε) x*E=E
    rw [←normalizedRegularAmbient_gram A (NeZero.pos N) P e x]
    exact hpull.1
  have hrows : ∀ (r : AsymptoticCompactObservationCount.Row N) (u : Set UpperHalfPlane) (hu : IsCompact u),
      AsymptoticRegularObservationRows.row (NeZero.pos N) r e hu P'.epsilon_pos (P'.s+3) x*R*E=0 := by
    intro r u hu
    exact projection_source_pullback_rows R Qcap _ hRQ (cover.regularCapSpace_original_rows A P e x hx r u hu)
  have he := actualFiniteExpression_regular_original_paid A P e hN2 excluded threshold S hS W B Bg D H₀ G C Kobs
    n hK q hq hbudget x E hPE hrows
  have herr : ‖regularSum T x*E-E‖≤2/(4:ℝ)^n :=
    he.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hE (by positivity : (0:ℝ)≤2/(4:ℝ)^n))
  have horder := actualFiniteExpression_regular_order A P e hN2 excluded threshold S hS W B Bg D H₀ G C Kobs n s q hq x
  have hT : ‖regularSum T x‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ horder.1).mpr horder.2.1
  have hv : ‖V‖≤1 := regular_norm A P (NeZero.pos N) s e x
  have hdiff : ‖R-V‖≤Real.exp (-8*s)/2 := by
    rw [norm_sub_rev]
    exact regular_error A P (NeZero.pos N) s e x
  have hRE : R.adjoint.comp (R.comp E)=E := by
    simpa only [E,mul_def,ContinuousLinearMap.comp_assoc] using hpull.1
  have hh := reconstructed_source_error R V E (regularSum T x) hR hv hE hT hRE herr hdiff
  have hconj : R.comp (E.comp R.adjoint)=Qcap := by
    simpa only [E,mul_def,ContinuousLinearMap.comp_assoc] using hpull.2
  rw [hconj] at hh
  rw [reconstructedFilterExpression_regular]
  convert hh using 1
  ring

#print axioms actualFiniteExpression_canonical_reconstructed_error
end QuantitativeMaass.RawBoundedIteration
