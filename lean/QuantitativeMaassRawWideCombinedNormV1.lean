module

public import QuantitativeMaassRawNormalizedCombinedRegularV1
public import QuantitativeEulerEndpointWideBaselineBoundsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeMaass.RawPrepared
open QuantitativeEulerEndpointPrepared
open QuantitativeMaass.EulerHilbert.FullTerminal
open QuantitativeMaass.RawPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open AsymptoticRegularCompactBranch

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)

def wideCombinedBound (R Y H : ℝ) (l : List (EligiblePrime N)) : ℕ → ℝ
  | 0 => wideDetectorBound N e R Y H ((AsymptoticReconstructedCount.parameters A P).s+3)
  | j+1 => wideSequenceBound N (sign e.1) R Y H ((AsymptoticReconstructedCount.parameters A P).s+3) l j

theorem combined_rows_wide_norm {s : Set UpperHalfPlane} (hs : IsCompact s)
    {R Y H : ℝ} (hY : 0<Y)
    (hre : ∀ z∈s,|z.re|≤R) (hlo : ∀ z∈s,Y≤z.im) (hhi : ∀ z∈s,z.im≤H)
    (l : List (EligiblePrime N)) (i : ℕ) (x : UpperHalfPlane) :
    ‖normalizedCombinedRows A P e hs l i x‖≤wideCombinedBound A P e R Y H l i := by
  have hu := normalizedRegularAmbient_norm A (NeZero.pos N) P e x
  cases i with
  | zero =>
    apply (norm_mul_le_of_le
      (newBaselineDetector_wide_norm hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        hY hre hlo hhi N e ((AsymptoticReconstructedCount.parameters A P).s+3) x) hu).trans_eq
    exact mul_one _
  | succ i =>
    apply (norm_mul_le_of_le
      (packet_sequence_wide_norm N (NeZero.pos N) (sign e.1) hs
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos hY hre hlo hhi
        ((AsymptoticReconstructedCount.parameters A P).s+3) l i x) hu).trans_eq
    exact mul_one _

#print axioms combined_rows_wide_norm
end QuantitativeMaass.RawPrepared
