module

public import QuantitativeEulerEndpointNewEnergyTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace QuantitativeSpectralObservability QuantitativeNewGap
open scoped Classical MatrixGroups ENNReal

/-- The old-tail coefficient is fixed before the height and the fresh prime. -/
def newTailConstant (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) : ℝ :=
  3*(CongruenceSubgroup.Gamma0 N).index*∑ i,(primeOldData N hN S hS i).C

theorem newTailConstant_nonneg (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    0≤newTailConstant N hN S hS := by
  unfold newTailConstant
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => (primeOldData N hN S hS i).C_pos.le))

theorem newTailCost_eq (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {H : ℝ} (hH : 0<H) :
    (∑ i, (CongruenceSubgroup.Gamma0 N).index*
      (3*ENNReal.ofReal (H/(primeOldData N hN S hS i).C)⁻¹))=
      ENNReal.ofReal (newTailConstant N hN S hS/H) := by
  have he (i) : (CongruenceSubgroup.Gamma0 N).index*
      (3*ENNReal.ofReal (H/(primeOldData N hN S hS i).C)⁻¹)=
      ENNReal.ofReal (3*(CongruenceSubgroup.Gamma0 N).index*(primeOldData N hN S hS i).C/H) := by
    rw [inv_div]
    rw [show (3:ℝ≥0∞)=ENNReal.ofReal (3:ℝ) by norm_num,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3),
      ←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  simp_rw [he]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (mul_nonneg (by positivity) (primeOldData N hN S hS i).C_pos.le) hH.le)]
  congr 1
  simp only [newTailConstant,Finset.sum_div,Finset.mul_sum]

def newTraceTarget (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (H : ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) : ℝ :=
  (trace volume (fun x => (AsymptoticTotalNewCorner.stripSpace N hN hε ht x).starProjection)).toReal+
    newTailConstant N hN S hS/H

theorem newTraceTarget_nonneg (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {H : ℝ} (hH : 0≤H) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    0≤newTraceTarget N hN S hS H hε ht :=
  add_nonneg ENNReal.toReal_nonneg (div_nonneg (newTailConstant_nonneg N hN S hS) hH)

theorem newTraceTarget_ofReal (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {H : ℝ} (hH : 0<H) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    ENNReal.ofReal (newTraceTarget N hN S hS H hε ht)=
      trace volume (fun x => (AsymptoticTotalNewCorner.stripSpace N hN hε ht x).starProjection)+
        ∑ i, (CongruenceSubgroup.Gamma0 N).index*
          (3*ENNReal.ofReal (H/(primeOldData N hN S hS i).C)⁻¹) := by
  rw [newTraceTarget,ENNReal.ofReal_add ENNReal.toReal_nonneg
    (div_nonneg (newTailConstant_nonneg N hN S hS) hH.le),
    ENNReal.ofReal_toReal (AsymptoticTotalNewCorner.stripSpace_trace_finite N hN hε ht).ne,
    newTailCost_eq N hN S hS hH]

#print axioms newTailCost_eq
#print axioms newTraceTarget_ofReal
end QuantitativeEulerEndpointPrepared
