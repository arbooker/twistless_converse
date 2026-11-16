module

public import QuantitativeMaassRawOriginalSourceKernelV1
public import QuantitativeMaassRawActualPhysicalPreservationV1

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

/-- The projection onto all compact original equations satisfies every row
of each finite block, by its range membership. -/
theorem originalSourceProjection_original_solution (n : ℕ) :
    OriginalPhysicalSolution A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (originalSourceProjection A P e) := by
  constructor
  · ext1 v
    exact ((originalSourceKernel A P e).starProjection_apply_mem v).1
  · intro j _hj b i
    ext1 v
    have hv := ((originalSourceKernel A P e).starProjection_apply_mem v).2
    change holomorphicSum _ _ (physicalExact A P (NeZero.pos N) e
      (originalSourceProjection A P e v))=0
    exact RawPrepared.baseline_zero_of_original_rows e
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) _ hv b.compact i
  · intro j _hj b i
    ext1 v
    have hv := ((originalSourceKernel A P e).starProjection_apply_mem v).2
    change holomorphicSum _ _ (physicalExact A P (NeZero.pos N) e
      (originalSourceProjection A P e v))=0
    exact RawPrepared.packet_zero_of_original_rows e
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) _ hv b.compact b.primes i

/-- The common finite filter approximately fixes the actual entire sector.
All original baseline and prime equations are discharged internally. -/
theorem actualFiniteExpression_source_paid (n : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n))) :
    ‖holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (Real.exp ((K+1)*(4:ℝ)^n)) q) 0*originalSourceProjection A P e-
        originalSourceProjection A P e‖≤2/(4:ℝ)^n := by
  have hh := actualFiniteExpression_original_paid A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n hK q hq hbudget (originalSourceProjection A P e)
    (originalSourceProjection_original_solution A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n)
  have hb := mul_le_mul_of_nonneg_left (originalSourceProjection_norm A P e)
    (by positivity : (0:ℝ)≤2/(4:ℝ)^n)
  simpa only [mul_one] using hh.trans hb

#print axioms originalSourceProjection_original_solution
#print axioms actualFiniteExpression_source_paid
end QuantitativeMaass.RawBoundedIteration
