module

public import QuantitativeEulerEndpointSectorEnergyTraceV1
public import AsymptoticIncidenceCountReductionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory AsymptoticSectorSigns AsymptoticRegularTrace QuantitativeSpectralObservability QuantitativeNewGap
open scoped Classical MatrixGroups ENNReal

/-- The combined old-and-sign tail coefficient is fixed before the height and the fresh prime. -/
def sectorTailConstant (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) : ℝ :=
  3*(CongruenceSubgroup.Gamma0 N).index*∑ i,sectorFamilyC N hN sector S hS i

theorem sectorTailConstant_nonneg (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    0≤sectorTailConstant N hN sector S hS := by
  unfold sectorTailConstant
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => (sectorFamilyC_pos N hN sector S hS i).le))

theorem sectorTailCost_eq (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {H : ℝ} (hH : 0<H) :
    (∑ i, (CongruenceSubgroup.Gamma0 N).index*
      (3*ENNReal.ofReal (H/sectorFamilyC N hN sector S hS i)⁻¹))=
      ENNReal.ofReal (sectorTailConstant N hN sector S hS/H) := by
  have he (i) : (CongruenceSubgroup.Gamma0 N).index*
      (3*ENNReal.ofReal (H/sectorFamilyC N hN sector S hS i)⁻¹)=
      ENNReal.ofReal (3*(CongruenceSubgroup.Gamma0 N).index*sectorFamilyC N hN sector S hS i/H) := by
    rw [inv_div]
    rw [show (3:ℝ≥0∞)=ENNReal.ofReal (3:ℝ) by norm_num,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3),
      ←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  simp_rw [he]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (mul_nonneg (by positivity) (sectorFamilyC_pos N hN sector S hS i).le) hH.le)]
  congr 1
  simp only [sectorTailConstant,Finset.sum_div,Finset.mul_sum]

def sectorTraceTarget (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (H : ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) : ℝ :=
  (trace volume (fun x => (AsymptoticQuotientIncidence.space N hN hε ht sector x).starProjection)).toReal+
    sectorTailConstant N hN sector S hS/H

theorem sectorTraceTarget_nonneg (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {H : ℝ} (hH : 0≤H) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    0≤sectorTraceTarget N hN sector S hS H hε ht :=
  add_nonneg ENNReal.toReal_nonneg (div_nonneg (sectorTailConstant_nonneg N hN sector S hS) hH)

theorem sectorTraceTarget_ofReal (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {H : ℝ} (hH : 0<H) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    ENNReal.ofReal (sectorTraceTarget N hN sector S hS H hε ht)=
      trace volume (fun x => (AsymptoticQuotientIncidence.space N hN hε ht sector x).starProjection)+
        ∑ i, (CongruenceSubgroup.Gamma0 N).index*
          (3*ENNReal.ofReal (H/sectorFamilyC N hN sector S hS i)⁻¹) := by
  rw [sectorTraceTarget,ENNReal.ofReal_add ENNReal.toReal_nonneg
    (div_nonneg (sectorTailConstant_nonneg N hN sector S hS) hH.le),
    ENNReal.ofReal_toReal (AsymptoticQuotientIncidence.space_trace_finite N hN hε ht sector).ne,
    sectorTailCost_eq N hN sector S hS hH]

#print axioms sectorTailCost_eq
#print axioms sectorTraceTarget_ofReal
end QuantitativeEulerEndpointPrepared
