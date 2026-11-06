module

public import QuantitativeArithmeticRetainedPhysicalFilterV1
public import QuantitativeEulerEndpointSectorRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedPhysicalSector
open UpperHalfPlane QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticCylinderLift AsymptoticFiniteBranch
open AsymptoticCompactObservationCount QuantitativeEulerEndpointPrepared
open QuantitativeEulerDensityGenerators

variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ)
    (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)

/-- The literal coefficient sector, realized in the physical strip space. -/
def physicalSectorMap :
    AsymptoticRamifiedSectors.sector N h (h+1+P.s) e →ₗ[ℂ]
      AsymptoticHyperbolicSlash.Space :=
  lift.toLinearMap.comp ((holomorphicSpace (2*h) (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)
    (by positivity : 0<4*Real.pi) P.epsilon_pos).subtype.comp
      (AsymptoticRamifiedSectors.cylinderMap N h (h+1+P.s) (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) e
        P.epsilon_pos (by have := QuantitativeArithmeticRetainedPreparedReconstruction.exponent_ge A P; omega)))

theorem physicalSectorMap_injective : Function.Injective (physicalSectorMap A P h e) :=
  lift.injective.comp (Subtype.val_injective.comp
    (AsymptoticRamifiedSectors.cylinderMap_injective N h (h+1+P.s) (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) e
      P.epsilon_pos (by have := QuantitativeArithmeticRetainedPreparedReconstruction.exponent_ge A P; omega)))

theorem physicalSectorMap_finrank :
    Module.finrank ℂ (LinearMap.range (physicalSectorMap A P h e)) =
      Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :=
  LinearMap.finrank_range_of_inj (physicalSectorMap_injective A P h e)

/-- No truncation is made in this exact original-row identity. -/
theorem row_sector_zero (r : Row N) {s : Set ℍ} (hs : IsCompact s)
    (a : AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :
    holomorphicSum (rowExpression hN r e hs P.epsilon_pos (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)) (h+1)
      (physicalSectorMap A P h e a)=0 := by
  have he := congrArg (fun T => T
    ((AsymptoticRamifiedSectors.cylinderMap N h (h+1+P.s) (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) e
      P.epsilon_pos (by have := QuantitativeArithmeticRetainedPreparedReconstruction.exponent_ge A P; omega) a : holomorphicSpace (2*h) (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)
        (by positivity : 0<4*Real.pi) P.epsilon_pos) : Space))
    (cylinder_rowExpression hN r e hs P.epsilon_pos (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) (h+1))
  exact he.trans (QuantitativeArithmeticRetainedFilterTrace.row_annihilates hN h (h+1+P.s)
    (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) P.epsilon_pos
    (by have := QuantitativeArithmeticRetainedPreparedReconstruction.exponent_ge A P; omega) e r hs a)

theorem packet_sector_zero (q : ℕ) (hq : q.Prime) (hqN : ¬q∣N)
    {s : Set ℍ} (hs : IsCompact s)
    (a : AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :
    holomorphicSum (originalPacketExpression hs P.epsilon_pos N q hN hq.pos
      (sign e.1) (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)) (h+1) (physicalSectorMap A P h e a)=0 := by
  have hz := row_sector_zero A hN P h e (.twist q hq.pos) hs a
  rw [rowExpression,multiplier_fresh e hq hqN] at hz
  rw [originalPacketExpression,holomorphicSum_scale,smul_apply,hz,smul_zero]

variable [NeZero N]

theorem baseline_sector_zero {s : Set ℍ} (hs : IsCompact s)
    (i : NewBaselineIndex N)
    (a : AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :
    holomorphicSum (originalBaselineExpression N e hs P.epsilon_pos (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) i) (h+1)
      (physicalSectorMap A P h e a)=0 := by
  cases i with
  | inl i =>
    cases i with
    | none =>
      simpa only [originalBaselineExpression,rowExpression,multiplier_one] using
        row_sector_zero A (NeZero.pos N) P h e (.twist 1 Nat.zero_lt_one) hs a
    | some b =>
      have hf : ¬(primeLift N b).q∣N := fun hd =>
        (not_le_of_gt (primeLift N b).large) (Nat.le_of_dvd (NeZero.pos N) hd)
      simpa only [originalBaselineExpression,rowExpression,
        multiplier_fresh e (primeLift N b).prime hf] using
        row_sector_zero A (NeZero.pos N) P h e (.twist (primeLift N b).q
          (primeLift N b).prime.pos) hs a
  | inr p =>
    simpa only [originalBaselineExpression,rowExpression] using
      row_sector_zero A (NeZero.pos N) P h e (.ramified p.val
        (Nat.mem_primeFactors.mp p.property).1
        (Nat.mem_primeFactors.mp p.property).2.1) hs a

#print axioms physicalSectorMap_injective
#print axioms physicalSectorMap_finrank
#print axioms row_sector_zero
#print axioms packet_sector_zero
#print axioms baseline_sector_zero
end QuantitativeArithmeticRetainedPhysicalSector


namespace QuantitativeArithmeticRetainedPhysicalSector
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedCommonExpression AsymptoticSectorSigns
open AsymptoticFiniteBranch ContinuousLinearMap
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (hN : 0<N)
  (h : ℕ) (e : Sector N)

def normalizedPhysicalSectorMap :=
  QuantitativeArithmeticRetainedSectorProjection.physicalMap A hR₀ hN P h (h+1+P.s)
    (exponent A P+3) (by omega) (degree_bound A P h) e

def normalizedPhysicalSectorProjection (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) :=
  QuantitativeArithmeticRetainedSectorProjection.projection A hR₀ hN P h (h+1+P.s)
    (exponent A P+3) (by omega) (degree_bound A P h) e hdiv hbad

theorem normalizedPhysicalSectorProjection_mem (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N)
    (v : AsymptoticHyperbolicSlash.Space) :
    normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad v∈
      LinearMap.range (normalizedPhysicalSectorMap A P hR₀ hN h e) :=
  QuantitativeArithmeticRetainedSectorProjection.projection_mem A hR₀ hN P h (h+1+P.s)
    (exponent A P+3) (by omega) (degree_bound A P h) e hdiv hbad v

theorem normalizedPhysicalSectorProjection_norm (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) :
    ‖normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad‖≤1 :=
  QuantitativeArithmeticRetainedSectorProjection.projection_norm A hR₀ hN P h (h+1+P.s)
    (exponent A P+3) (by omega) (degree_bound A P h) e hdiv hbad

theorem normalizedPhysicalSectorProjection_terminal (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) :
    holomorphicSum (QuantitativeArithmeticRetainedExpressionIteration.unit A P) (h+1)*
      normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad=
      normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad := by
  rw [QuantitativeArithmeticRetainedExpressionIteration.unit_physical]
  exact QuantitativeArithmeticRetainedSectorProjection.projection_terminal A hR₀ hN P h (h+1+P.s)
    (exponent A P+3) (by omega) (degree_bound A P h) e hdiv hbad

theorem normalizedPhysicalSectorMap_finrank (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) :
    Module.finrank ℂ (LinearMap.range (normalizedPhysicalSectorMap A P hR₀ hN h e))=
      Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :=
  QuantitativeArithmeticRetainedSectorProjection.physicalMap_finrank A hR₀ hN P h (h+1+P.s)
    (exponent A P+3) (by omega) (degree_bound A P h) e hdiv hbad
    (physical_contraction A P hR₀ hN e (h+1))

theorem normalizedPhysicalSectorMap_reconstruct (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N)
    (a : AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :
    physicalExact A P hR₀ hN h e (normalizedPhysicalSectorMap A P hR₀ hN h e a)=
      physicalSectorMap A P h e a := by
  let v := QuantitativeArithmeticRetainedSectorProjection.coordinates A hR₀ hN P h (h+1+P.s)
    (exponent A P+3) (by omega) (degree_bound A P h) e a
  have hs := congrArg (fun T => T v) (AsymptoticCylinderTerminal.ambientLift_adjoint_self P.ε)
  change (AsymptoticCylinderTerminal.ambientLift P.ε).adjoint
    (AsymptoticCylinderTerminal.ambientLift P.ε v)=v at hs
  change AsymptoticCylinderLift.lift (QuantitativeArithmeticRetainedFilterTrace.reconstruction A hR₀ hN P h e
    ((AsymptoticCylinderTerminal.ambientLift P.ε).adjoint
      (AsymptoticCylinderTerminal.ambientLift P.ε v)))=_
  rw [hs]
  exact congrArg AsymptoticCylinderLift.lift
    (QuantitativeArithmeticRetainedSectorProjection.coordinates_reconstruct A hR₀ hN P h (h+1+P.s)
      (exponent A P+3) (by omega) (degree_bound A P h) e hdiv hbad
      (physical_contraction A P hR₀ hN e (h+1)) a)

#print axioms normalizedPhysicalSectorMap_reconstruct
#print axioms normalizedPhysicalSectorMap_finrank
#print axioms normalizedPhysicalSectorProjection_norm
#print axioms normalizedPhysicalSectorProjection_terminal
end QuantitativeArithmeticRetainedPhysicalSector

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointResidual
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointNestedPerturbation
open QuantitativeArithmeticRetainedCommonExpression QuantitativeArithmeticRetainedPhysicalSector
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The actual normalized full coefficient sector satisfies all original
physical equations, with the exact original block coefficients. -/
theorem normalizedPhysicalSector_original_solution (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) (n h : ℕ) :
    OriginalPhysicalSolution A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n h
      (normalizedPhysicalSectorProjection A P hR₀ (NeZero.pos N) h e hdiv hbad) := by
  constructor
  · exact normalizedPhysicalSectorProjection_terminal A P hR₀ (NeZero.pos N) h e hdiv hbad
  · intro j hj b i
    ext1 v
    obtain ⟨a,ha⟩ := normalizedPhysicalSectorProjection_mem A P hR₀ (NeZero.pos N) h e hdiv hbad v
    change holomorphicSum _ _ (physicalExact A P hR₀ (NeZero.pos N) h e
      (normalizedPhysicalSectorProjection A P hR₀ (NeZero.pos N) h e hdiv hbad v))=0
    rw [←ha,normalizedPhysicalSectorMap_reconstruct A P hR₀ (NeZero.pos N) h e hdiv hbad]
    exact baseline_sector_zero A P h e _ i a
  · intro j hj b i
    ext1 v
    obtain ⟨a,ha⟩ := normalizedPhysicalSectorProjection_mem A P hR₀ (NeZero.pos N) h e hdiv hbad v
    change holomorphicSum _ _ (physicalExact A P hR₀ (NeZero.pos N) h e
      (normalizedPhysicalSectorProjection A P hR₀ (NeZero.pos N) h e hdiv hbad v))=0
    rw [←ha,normalizedPhysicalSectorMap_reconstruct A P hR₀ (NeZero.pos N) h e hdiv hbad]
    exact packet_sector_zero A (NeZero.pos N) P h e
      b.primes[i.val].val b.primes[i.val].property.1 b.primes[i.val].property.2 b.compact a

/-- The common finite filter approximately fixes the actual entire sector.
All original baseline and prime equations are discharged internally. -/
theorem actualFiniteExpression_sector_paid (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) (n h : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P hR₀ e n
      (actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n))) :
    ‖holomorphicSum (actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n
      (Real.exp ((K+1)*(4:ℝ)^n)) q) (h+1)*normalizedPhysicalSectorProjection A P hR₀ (NeZero.pos N) h e hdiv hbad-
        normalizedPhysicalSectorProjection A P hR₀ (NeZero.pos N) h e hdiv hbad‖≤2/(4:ℝ)^n := by
  have hh := actualFiniteExpression_original_paid A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n h hK q hq hbudget (normalizedPhysicalSectorProjection A P hR₀ (NeZero.pos N) h e hdiv hbad)
    (normalizedPhysicalSector_original_solution A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs hdiv hbad n h)
  have hb := mul_le_mul_of_nonneg_left (normalizedPhysicalSectorProjection_norm A P hR₀ (NeZero.pos N) h e hdiv hbad)
    (by positivity : (0:ℝ)≤2/(4:ℝ)^n)
  simpa only [mul_one] using hh.trans hb

#print axioms normalizedPhysicalSector_original_solution
#print axioms actualFiniteExpression_sector_paid
end QuantitativeArithmeticRetainedIteration
