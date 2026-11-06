module

public import QuantitativeArithmeticRetainedSectorProjectionV1
public import QuantitativeArithmeticRetainedRegularNormalizationV1
public import QuantitativeArithmeticRetainedFiniteExtensionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedPreparedReconstruction
open Filter AsymptoticSectorSigns
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedSectorReconstruction

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ) (P : Parameters A)

theorem exists_exponent : ∃s : ℕ,P.s≤s ∧
    P.ρ^(s+2)*QuantitativeArithmeticRetainedCertificateOperators.lowConstant A P<1/2 := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one P.rho_pos.le P.rho_lt_one).mul_const
    (P.ρ^2*QuantitativeArithmeticRetainedCertificateOperators.lowConstant A P)
  simp only [zero_mul] at h
  obtain ⟨n,hn⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  refine ⟨max n P.s,le_max_right _ _,?_⟩
  have hb := hn (max n P.s) (le_max_left _ _)
  simpa only [pow_add,mul_assoc] using hb

/-- One exponent, chosen before the weight, sign sector, or orbit root.
Its scalar estimate also controls all finite truncations. -/
def exponent : ℕ := (exists_exponent A P).choose

theorem exponent_ge : P.s≤exponent A P := (exists_exponent A P).choose_spec.1

theorem scalar_contraction :
    P.ρ^(exponent A P+3-1)*QuantitativeArithmeticRetainedCertificateOperators.lowConstant A P<1/2 := by
  rw [show exponent A P+3-1=exponent A P+2 by omega]
  exact (exists_exponent A P).choose_spec.2

theorem degree_bound (h : ℕ) :
    2*(h+1+P.s)+4≤2*h+2*(exponent A P+3)+1 := by
  have := exponent_ge A P
  omega

variable (hS : ∀p∈S,p.Prime) (hN : 0<N)

theorem physical_contraction (e : Sector N) (m : ℕ) :
    ‖QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P
      (multiplier e) (ramifiedParameter e) (exponent A P+3) m‖<1/2 :=
  (QuantitativeArithmeticRetainedCertificateOperators.low_norm_le A hS hN P
    (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
    (fun p _ => ramifiedParameter_norm e p) (by omega) m).trans_lt (scalar_contraction A P)

theorem regular_contraction (e : Sector N) (z : UpperHalfPlane) :
    ‖QuantitativeArithmeticRetainedRegularOperators.low A hS hN P
      (multiplier e) (ramifiedParameter e) (exponent A P+3) z‖<1/2 :=
  (QuantitativeArithmeticRetainedRegularOperators.low_norm_le A hS hN P
    (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
    (fun p _ => ramifiedParameter_norm e p) (by omega) z).trans_lt (scalar_contraction A P)

include hS hN in
/-- Original Euler count against the same coefficient sectors that the
normalized terminal projection represents. -/
theorem original_count (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) (h : ℕ) :
    (FinitenessOriginalInput.S N (2*(h+1))).Finite ∧
      (FinitenessOriginalInput.S N (2*(h+1))).ncard≤
        ∑e : Sector N,Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) := by
  have hd := degree_bound A P h
  obtain ⟨hf,hb⟩ := QuantitativeArithmeticRetainedEulerCylinder.euler_count_le_cylinder_sectors
    A hS hN P hdiv hbad h (exponent A P+3) (by omega)
  refine ⟨hf,?_⟩
  simpa only [cylinderSector_finrank] using hb

/-- Fixed-weight projection rank equals the original sector dimension;
there is no contraction assumption remaining in this endpoint. -/
theorem physical_sector_rank (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    (h : ℕ) (e : Sector N) :
    Module.finrank ℂ (LinearMap.range
      (QuantitativeArithmeticRetainedSectorProjection.physicalMap A hS hN P h (h+1+P.s)
        (exponent A P+3) (by omega) (degree_bound A P h) e))=
      Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :=
  QuantitativeArithmeticRetainedSectorProjection.physicalMap_finrank A hS hN P h (h+1+P.s)
    (exponent A P+3) (by omega) (degree_bound A P h) e hdiv hbad (physical_contraction A P hS hN e (h+1))

/-- The actual finite reconstruction has the same coefficient mass bound
at every cutoff, with all scalar smallness obligations discharged. -/
theorem finite_mass (e : Sector N) (n : ℕ) (I : Finset ℤ) :
    AsymptoticFiniteBranch.expressionBound
      (QuantitativeArithmeticRetainedFiniteExpressions.fullExpression A hS hN P
        (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) n I)≤
      QuantitativeArithmeticRetainedCylinderNormalization.bound A P :=
  QuantitativeArithmeticRetainedFiniteExpressions.fullExpression_mass A hS hN P
    (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
    (fun p _ => ramifiedParameter_norm e p) (by omega) (scalar_contraction A P).le n I

#print axioms scalar_contraction
#print axioms physical_contraction
#print axioms regular_contraction
#print axioms original_count
#print axioms physical_sector_rank
#print axioms finite_mass
end QuantitativeArithmeticRetainedPreparedReconstruction
