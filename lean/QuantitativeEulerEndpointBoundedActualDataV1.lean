module

public import QuantitativeEulerEndpointActualCombinedEffortV1
public import QuantitativeEulerEndpointBoundedPrimeIterationV1

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra
open QuantitativeEulerEndpointNormalizedThreshold QuantitativeHolomorphic
open scoped Classical MatrixGroups

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
  (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
  (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
  (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)
local notation "P'" => AsymptoticReconstructedCount.parameters A P

/-- The exact explicitly normalized block in the constructed iteration,
with one fixed transport constant and common terminal height H0*4^n. -/
def actualBlock (n j : ℕ) : Block A P sector :=
  let H := H₀*(4:ℝ)^n
  let X := QuantitativeEulerEndpointPrimeBlocks.bound N hN excluded threshold₀ j
  let Y := min (P').ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  let Z := Y/wideDistortion Bg 2 (D*H)
  let hZ := div_pos (lt_min (P').epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  let L := (2*G*C)*X^4
  let hs := wideFreshRegion_compact L R R hZ
  let cost := (countReconstructionBound A P)^2*
    sectorObservationCost N (NeZero.pos N) sector S hS W B H (P').ε ((P').s+4)*
      (Kobs*((wideDistortion L R R)^((P').s+4))^2)
  let l := QuantitativeEulerEndpointPrimeBlocks.primes N hN excluded threshold₀ j
  let height := L*(R+R+1)/min 1 Z
  let low := Z/wideDistortion L R R
  ⟨_,hs,l,threshold cost,wideCombinedBound A P sector (height+1) low height l,
    combined_rows_wide_norm A P sector hs (div_pos hZ (wideDistortion_pos L R R))
      (fun _ hz => hz.1) (fun _ hz => hz.2.1) (fun _ hz => hz.2.2) l⟩

theorem actualBlock_range (hK0 : 0≤Kobs) (n j : ℕ) :
    let b := actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
    0<b.cutoff ∧ QuantitativeEulerEndpointBlockNormalization.factor
      b.bound (b.primes.length+1)*b.cutoff≤1 := by
  have hcost (H L R : ℝ) : 0≤(countReconstructionBound A P)^2*
      sectorObservationCost N (NeZero.pos N) sector S hS W B H (P').ε ((P').s+4)*
        (Kobs*((wideDistortion L R R)^((P').s+4))^2) :=
    mul_nonneg (mul_nonneg (sq_nonneg _)
      (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W B H (P').ε ((P').s+4)))
      (mul_nonneg hK0 (sq_nonneg _))
  dsimp only [actualBlock]
  exact ⟨threshold_pos (hcost _ _ _),(normalized_range _ _ (hcost _ _ _)).2⟩

theorem actualBlock_effort_pos (hK0 : 0≤Kobs) (n j : ℕ) :
    0<effortAt A P sector n
      (actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n) j := by
  have hr := actualBlock_range A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs hK0 n j
  exact QuantitativeEulerEndpointLocalEffort.effort_pos n j
    (QuantitativeEulerEndpointBoundedTerminal.logCost_nonneg _ _ hr.1 hr.2)

theorem actualBlock_logCost (n j : ℕ) :
    let b := actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
    QuantitativeEulerEndpointBoundedTerminal.logCost b.primes b.bound b.cutoff=
      actualCombinedLog N hN excluded threshold₀ sector S hS W B Bg D H₀ G C
        ((countReconstructionBound A P)^2*Kobs) (P').ε ((P').s+4) n j := by
  dsimp only [actualBlock,QuantitativeEulerEndpointBoundedTerminal.logCost,actualCombinedLog]
  have he : ∀ R Y H : ℝ,∀ l : List (EligiblePrime N),wideCombinedBound A P sector R Y H l=
      prepend (wideDetectorBound N sector R Y H ((P').s+4))
        (wideSequenceBound N (sign sector.1) R Y H ((P').s+4) l) := by
    intro R Y H l
    funext i
    cases i <;> rfl
  rw [he]
  congr 4
  ring

theorem actualBlock_effort (n j : ℕ) :
    effortAt A P sector n (actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n) j=
      QuantitativeEulerEndpointLocalEffort.effort n j
        (actualCombinedLog N hN excluded threshold₀ sector S hS W B Bg D H₀ G C
          ((countReconstructionBound A P)^2*Kobs) (P').ε ((P').s+4) n j) := by
  unfold effortAt QuantitativeEulerEndpointBoundedTerminal.effort
  rw [actualBlock_logCost]

/-- All logarithmic effort of the actual bounded iteration, including
its final next-block sharpening, is O(4^n). -/
theorem exists_actual_total_effort (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      (∑ j∈Finset.range n,effortAt A P sector n
        (actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n) j)+
      effortAt A P sector n
        (actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n) n≤K*(4:ℝ)^n := by
  obtain ⟨K,hK,hbound⟩ := exists_actual_combined_total_effort N hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C ((countReconstructionBound A P)^2*Kobs) (P').ε ((P').s+4)
    hBg0 hD0 hH₀ hG0 hC0 (mul_nonneg (sq_nonneg _) hK0) (P').epsilon_pos
  refine ⟨K,hK,?_⟩
  intro n
  simpa only [actualBlock_effort] using hbound n

#print axioms actualBlock_logCost
#print axioms actualBlock_range
#print axioms actualBlock_effort_pos
#print axioms actualBlock_effort
#print axioms exists_actual_total_effort
end QuantitativeEulerEndpointBoundedIteration
