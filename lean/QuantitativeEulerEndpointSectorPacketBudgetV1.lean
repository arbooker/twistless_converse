module

public import QuantitativeEulerEndpointSectorThresholdPolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticSectorSigns QuantitativeSpectralObservability Polynomial
open QuantitativeEulerDensityGenerators Filter Asymptotics
open scoped Classical MatrixGroups

variable {N : ℕ} [NeZero N] {hN : 2≤N} {sector : Sector N}
  {excluded : Finset ℕ} {threshold : ℕ} {S : Finset SL(2,ℤ)}
  {hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N}
  {ε : ℝ} {hε : 0<ε}

/-- Reciprocal of the squared cutoff actually used by the sector packet,
with common height equal to the prime range. -/
def SectorPacketWitness.inverseCut
    (d : SectorPacketWitness N hN sector excluded threshold S hS hε) (t : ℕ) (x : ℝ) : ℝ :=
  let P := prepared N hN excluded threshold
  let R := d.Bg*(d.D*x+2+1)/min 1 (min ε (1/4))
  let L := (2*generatorTransportConstant P*d.B)*x^4
  let A := sectorObservationCost N (NeZero.pos N) sector S hS d.W d.Bobs x ε t*
    (d.K*((wideDistortion L R R)^t)^2)
  ((2*(1+2*A))⁻¹)⁻¹

def SectorPacketWitness.cutPolynomial
    (d : SectorPacketWitness N hN sector excluded threshold S hS hε) (t : ℕ) : Polynomial ℝ :=
  sectorThresholdPolynomial N (NeZero.pos N) sector S hS d.W d.Bobs ε d.K
    (2*generatorTransportConstant (prepared N hN excluded threshold)*d.B)
    (3*d.Bg/min 1 (min ε (1/4))) (d.Bg*d.D/min 1 (min ε (1/4))) t

theorem SectorPacketWitness.cutPolynomial_degree
    (d : SectorPacketWitness N hN sector excluded threshold S hS hε) (t : ℕ) :
    (d.cutPolynomial t).natDegree≤32*t :=
  sectorThresholdPolynomial_degree N (NeZero.pos N) sector S hS _ _ _ _ _ _ _ t

theorem SectorPacketWitness.inverseCut_nonneg
    (d : SectorPacketWitness N hN sector excluded threshold S hS hε) (t : ℕ) (x : ℝ) :
    0≤d.inverseCut t x := by
  dsimp only [inverseCut]
  rw [inv_inv]
  have ho := sectorObservationCost_nonneg N (NeZero.pos N) sector S hS d.W d.Bobs x ε t
  have hk := d.hK
  positivity

theorem SectorPacketWitness.inverseCut_le_polynomial
    (d : SectorPacketWitness N hN sector excluded threshold S hS hε) (t : ℕ) (x : ℝ) :
    d.inverseCut t x≤(d.cutPolynomial t).eval x := by
  have hr : d.Bg*(d.D*x+2+1)/min 1 (min ε (1/4))=
      (d.Bg*d.D/min 1 (min ε (1/4)))*x+3*d.Bg/min 1 (min ε (1/4)) := by ring
  dsimp only [inverseCut,cutPolynomial]
  rw [hr]
  exact sectorThresholdPolynomial_bound N (NeZero.pos N) sector S hS
    d.W d.Bobs ε d.K _ _ _ d.hK t x

/-- Actual reciprocal packet cut grows at most as x^(32t), with epsilon,
sector and reconstruction weight held fixed. No varying-epsilon uniformity
or small-spectrum estimate is claimed. -/
theorem SectorPacketWitness.inverseCut_isBigO
    (d : SectorPacketWitness N hN sector excluded threshold S hS hε) (t : ℕ) :
    d.inverseCut t=O[atTop] (fun x : ℝ => x^(32*t)) := by
  have hp : (d.cutPolynomial t).eval=O[atTop] (fun x : ℝ => x^(32*t)) := by
    have he := Polynomial.isBigO_atTop_of_degree_le (d.cutPolynomial t) (X^(32*t))
      (by rw [degree_X_pow]; exact degree_le_of_natDegree_le (d.cutPolynomial_degree t))
    simpa only [eval_pow,eval_X] using he
  apply IsBigO.trans (g := (d.cutPolynomial t).eval) _ hp
  apply isBigO_of_le
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (d.inverseCut_nonneg t x)]
  exact (d.inverseCut_le_polynomial t x).trans (le_abs_self _)

#print axioms SectorPacketWitness.inverseCut_le_polynomial
#print axioms SectorPacketWitness.inverseCut_isBigO
end QuantitativeEulerEndpointPrepared
