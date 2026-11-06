module

public import QuantitativeEulerEndpointActualCombinedLogV1
public import QuantitativeEulerEndpointEndpointEffortV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open AsymptoticSectorSigns QuantitativeEulerEndpointNormalizedThreshold
open scoped Classical MatrixGroups

variable (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ)
    (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs ε : ℝ) (t : ℕ)

/-- Exactly the logarithm of the explicit normalization in the actual
block schedule, with one common geometric terminal height H0*4^n. -/
def actualCombinedLog (n j : ℕ) : ℝ :=
  let H := H₀*(4:ℝ)^n
  let X := QuantitativeEulerEndpointPrimeBlocks.bound N hN excluded threshold₀ j
  let Y := min ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  let Z := Y/wideDistortion Bg 2 (D*H)
  let L := (2*G*C)*X^4
  let height := L*(R+R+1)/min 1 Z
  let low := Z/wideDistortion L R R
  let O := sectorObservationCost N (NeZero.pos N) sector S hS W B H ε t
  let A := O*(Kobs*((wideDistortion L R R)^t)^2)
  let l := QuantitativeEulerEndpointPrimeBlocks.primes N hN excluded threshold₀ j
  Real.log (2/(QuantitativeEulerEndpointBlockNormalization.factor
    (prepend (wideDetectorBound N sector (height+1) low height t)
      (wideSequenceBound N (sign sector.1) (height+1) low height t l)) (l.length+1)*threshold A)^2)

/-- The effort of every actual update, INCLUDING the final sharpening,
has total O(4^n). No quantitative cost-growth hypothesis remains. -/
theorem exists_actual_combined_total_effort (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) (hε : 0<ε) :
    ∃ Q : ℝ, 0≤Q ∧ ∀ n : ℕ,
      (∑ j∈Finset.range n, QuantitativeEulerEndpointLocalEffort.effort n j
        (actualCombinedLog N hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs ε t n j))+
      QuantitativeEulerEndpointLocalEffort.effort n n
        (actualCombinedLog N hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs ε t n n)
      ≤Q*(4:ℝ)^n := by
  obtain ⟨Q,hQ,hbound⟩ := exists_actual_combined_log_bound N hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs ε hBg0 hD0 hH₀ hG0 hC0 hK0 hε t
  refine ⟨2+5*Q,by positivity,?_⟩
  intro n
  exact QuantitativeEulerEndpointLocalEffort.effort_sum_with_endpoint n
    (actualCombinedLog N hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs ε t n)
    hQ (fun j _ => hbound n j)

#print axioms exists_actual_combined_total_effort
end QuantitativeEulerEndpointPrepared
