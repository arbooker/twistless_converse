module

public import QuantitativeMaassCanonicalRegularFilterErrorV1
public import QuantitativeMaassCanonicalMetricImageV1

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

/-- The literal original-row metric filter approximately fixes the actual
canonical regular projection, with constants uniform in the free orbit root. -/
theorem actualFiniteExpression_canonical_metric_error
    {hN : GridAdmissibleGap.Admissible N} (cover : AdmissibleScalarCover N hN)
    (n : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ→ℝ[X]) (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN2 excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n)))
    (x : UpperHalfPlane) (hx : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • x)) (m : ℕ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let s := Real.exp ((K+1)*(4:ℝ)^n)
    let T := actualFiniteExpression A P e hN2 excluded threshold S hS W B Bg D H₀ G C Kobs n s q
    let M := cover.metric P'.epsilon_pos (by omega : 1≤P'.s+3)
    let Qcan : Space→L[ℂ]Space := cover.regularProjection P'.epsilon_pos (by omega : 1≤P'.s+3) e x
    ‖regularSum (physicalMetricFilterExpression A P e M s T m) x*Qcan-Qcan‖^2≤
      (M.lower⁻¹)^2/(expressionMetricScale [M.branch]*(((2*m:ℕ):ℝ)+1))+
      3*(M.lower⁻¹)^2*(2/(4:ℝ)^n+Real.exp (-8*s))*M.upper^2 := by
  intro P' s T M Qcan
  have hraw := actualFiniteExpression_canonical_reconstructed_error A P e hN2 excluded threshold S hS W B Bg D H₀ G C Kobs
    cover n hK q hq hbudget x hx
  have hT := actualFiniteExpression_regular_order A P e hN2 excluded threshold S hS W B Bg D H₀ G C Kobs n s q hq x
  have hrec : 0≤regularSum (reconstructedFilterExpression A P e s T) x ∧
      regularSum (reconstructedFilterExpression A P e s T) x≤1 := by
    rw [reconstructedFilterExpression_regular]
    exact contractive_target_minorant 1
      (by change star (1 : Space→L[ℂ]Space)=1; exact star_one _) (by simp)
      (regularSum (expression A P (NeZero.pos N) s e) x) (regular_norm A P (NeZero.pos N) s e x)
      (by rfl) _ hT.1 hT.2.1
  have hh := cover.regular_metric_power_error P'.epsilon_pos (by omega : 1≤P'.s+3) e x
    (reconstructedFilterExpression A P e s T) hrec.1 hrec.2 hraw m
  apply hh.trans
  have hi := M.regularChange_inv_norm x
  have hd := M.regularChange_norm x
  have hs := expressionMetricScale_pos [M.branch]
  have hu : 0≤M.upper := M.branch.bound_nonneg
  have hl : 0≤M.lower⁻¹ := (inv_pos.mpr M.lower_pos).le
  gcongr

#print axioms actualFiniteExpression_canonical_metric_error
end QuantitativeMaass.RawBoundedIteration
