module

public import QuantitativeEulerEndpointBaselineRowExpressionV1
public import QuantitativeEulerEndpointPhysicalPacketRowsV1
public import AsymptoticFreshKernelRankV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSector
open UpperHalfPlane FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticCylinderLift AsymptoticFiniteBranch
open AsymptoticCompactObservationCount QuantitativeEulerEndpointPrepared
open QuantitativeEulerDensityGenerators

variable {N Q : ℕ} {hQ : 0<Q} {A : Certificate N Q hQ}
    (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)

/-- The literal coefficient sector, realized in the physical strip space. -/
def physicalSectorMap :
    AsymptoticRamifiedSectors.sector N h (h+1+P.s) e →ₗ[ℂ]
      AsymptoticHyperbolicSlash.Space :=
  lift.toLinearMap.comp ((holomorphicSpace (2*h) (P.s+4)
    (by positivity : 0<4*Real.pi) P.epsilon_pos).subtype.comp
      (AsymptoticRamifiedSectors.cylinderMap N h (h+1+P.s) (P.s+4) e
        P.epsilon_pos (by omega)))

theorem physicalSectorMap_injective : Function.Injective (physicalSectorMap P h e) :=
  lift.injective.comp (Subtype.val_injective.comp
    (AsymptoticRamifiedSectors.cylinderMap_injective N h (h+1+P.s) (P.s+4) e
      P.epsilon_pos (by omega)))

theorem physicalSectorMap_finrank :
    Module.finrank ℂ (LinearMap.range (physicalSectorMap P h e)) =
      Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :=
  LinearMap.finrank_range_of_inj (physicalSectorMap_injective P h e)

/-- No truncation is made in this exact original-row identity. -/
theorem row_sector_zero (r : Row N) {s : Set ℍ} (hs : IsCompact s)
    (a : AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :
    holomorphicSum (rowExpression hN r e hs P.epsilon_pos (P.s+4)) (h+1)
      (physicalSectorMap P h e a)=0 := by
  have he := congrArg (fun T => T
    ((AsymptoticRamifiedSectors.cylinderMap N h (h+1+P.s) (P.s+4) e
      P.epsilon_pos (by omega) a : holomorphicSpace (2*h) (P.s+4)
        (by positivity : 0<4*Real.pi) P.epsilon_pos) : Space))
    (cylinder_rowExpression hN r e hs P.epsilon_pos (P.s+4) (h+1))
  exact he.trans (row_sector_annihilated hN P h e r hs _ ⟨a,rfl⟩)

theorem packet_sector_zero (q : ℕ) (hq : q.Prime) (hqN : ¬q∣N)
    {s : Set ℍ} (hs : IsCompact s)
    (a : AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :
    holomorphicSum (originalPacketExpression hs P.epsilon_pos N q hN hq.pos
      (sign e.1) (P.s+4)) (h+1) (physicalSectorMap P h e a)=0 := by
  have hz := row_sector_zero hN P h e (.twist q hq.pos) hs a
  rw [rowExpression,multiplier_fresh e hq hqN] at hz
  rw [originalPacketExpression,holomorphicSum_scale,smul_apply,hz,smul_zero]

variable [NeZero N]

theorem baseline_sector_zero {s : Set ℍ} (hs : IsCompact s)
    (i : NewBaselineIndex N)
    (a : AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :
    holomorphicSum (originalBaselineExpression N e hs P.epsilon_pos (P.s+4) i) (h+1)
      (physicalSectorMap P h e a)=0 := by
  cases i with
  | inl i =>
    cases i with
    | none =>
      simpa only [originalBaselineExpression,rowExpression,multiplier_one] using
        row_sector_zero (NeZero.pos N) P h e (.twist 1 Nat.zero_lt_one) hs a
    | some b =>
      have hf : ¬(primeLift N b).q∣N := fun hd =>
        (not_le_of_gt (primeLift N b).large) (Nat.le_of_dvd (NeZero.pos N) hd)
      simpa only [originalBaselineExpression,rowExpression,
        multiplier_fresh e (primeLift N b).prime hf] using
        row_sector_zero (NeZero.pos N) P h e (.twist (primeLift N b).q
          (primeLift N b).prime.pos) hs a
  | inr p =>
    simpa only [originalBaselineExpression,rowExpression] using
      row_sector_zero (NeZero.pos N) P h e (.ramified p.val
        (Nat.mem_primeFactors.mp p.property).1
        (Nat.mem_primeFactors.mp p.property).2.1) hs a

#print axioms physicalSectorMap_injective
#print axioms physicalSectorMap_finrank
#print axioms row_sector_zero
#print axioms packet_sector_zero
#print axioms baseline_sector_zero
end QuantitativeEulerEndpointSector
