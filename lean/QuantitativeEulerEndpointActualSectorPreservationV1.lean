module

public import QuantitativeEulerEndpointNormalizedPhysicalSectorV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointResidual
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointNestedPerturbation
open QuantitativeEulerEndpointCommonReconstruction QuantitativeEulerEndpointSector
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The actual normalized full coefficient sector satisfies all original
physical equations, with the exact original block coefficients. -/
theorem normalizedPhysicalSector_original_solution (n h : ℕ) :
    OriginalPhysicalSolution A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n h
      (normalizedPhysicalSectorProjection A P (NeZero.pos N) h e) := by
  constructor
  · exact normalizedPhysicalSectorProjection_terminal A P (NeZero.pos N) h e
  · intro j hj b i
    ext1 v
    obtain ⟨a,ha⟩ := normalizedPhysicalSectorProjection_mem A P (NeZero.pos N) h e v
    change holomorphicSum _ _ (physicalExact A P (NeZero.pos N) h e
      (normalizedPhysicalSectorProjection A P (NeZero.pos N) h e v))=0
    rw [←ha,normalizedPhysicalSectorMap_reconstruct]
    exact baseline_sector_zero (AsymptoticReconstructedCount.parameters A P) h e _ i a
  · intro j hj b i
    ext1 v
    obtain ⟨a,ha⟩ := normalizedPhysicalSectorProjection_mem A P (NeZero.pos N) h e v
    change holomorphicSum _ _ (physicalExact A P (NeZero.pos N) h e
      (normalizedPhysicalSectorProjection A P (NeZero.pos N) h e v))=0
    rw [←ha,normalizedPhysicalSectorMap_reconstruct]
    exact packet_sector_zero (NeZero.pos N) (AsymptoticReconstructedCount.parameters A P) h e
      b.primes[i.val].val b.primes[i.val].property.1 b.primes[i.val].property.2 b.compact a

/-- The common finite filter approximately fixes the actual entire sector.
All original baseline and prime equations are discharged internally. -/
theorem actualFiniteExpression_sector_paid (n h : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n))) :
    ‖holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (Real.exp ((K+1)*(4:ℝ)^n)) q) (h+1)*normalizedPhysicalSectorProjection A P (NeZero.pos N) h e-
        normalizedPhysicalSectorProjection A P (NeZero.pos N) h e‖≤2/(4:ℝ)^n := by
  have hh := actualFiniteExpression_original_paid A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n h hK q hq hbudget (normalizedPhysicalSectorProjection A P (NeZero.pos N) h e)
    (normalizedPhysicalSector_original_solution A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n h)
  have hb := mul_le_mul_of_nonneg_left (normalizedPhysicalSectorProjection_norm A P (NeZero.pos N) h e)
    (by positivity : (0:ℝ)≤2/(4:ℝ)^n)
  simpa only [mul_one] using hh.trans hb

#print axioms normalizedPhysicalSector_original_solution
#print axioms actualFiniteExpression_sector_paid
end QuantitativeEulerEndpointBoundedIteration
