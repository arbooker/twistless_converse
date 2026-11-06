module

public import QuantitativeEulerEndpointNormalizedCombinedPacketV1
public import QuantitativeEulerEndpointTerminalGramV1
public import QuantitativeEulerEndpointPacketRegularV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticRegularCompactBranch AsymptoticRegularTrace
open QuantitativeEulerEndpointRegularBase QuantitativeEulerEndpointTerminalAlgebra
open ContinuousLinearMap MeasureTheory AsymptoticObservationStack AsymptoticPolarIsometry

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))

def normalizedCombinedBound : ℕ → ℝ
  | 0 => ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : NewBaselineIndex N => Space)).symm.toContinuousLinearMap‖ *
      ∑ i,newBaselineRowBound N e hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4) i
  | j+1 => packetSequenceBound N (NeZero.pos N) (sign e.1) hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) l j

theorem normalized_combined_rows_regular (i : ℕ) :
    (∀ g k,Measurable (fun x => matrix (normalizedCombinedRows A P e hs l i x) g k)) ∧
      Covariant (normalizedCombinedRows A P e hs l i) := by
  have hu := normalizedRegularCountReconstruction_regular A (NeZero.pos N) P e
  cases i with
  | zero =>
    obtain ⟨M,_hM,_hn,hm,hc⟩ := newBaselineDetector_regular N e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4)
    exact ⟨matrix_comp_measurable _ _ hm hu.1,covariant_comp _ _ hc hu.2⟩
  | succ i =>
    have hb := packet_sequence_regular N (NeZero.pos N) (sign e.1) hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) l i
    exact ⟨matrix_comp_measurable _ _ hb.1 hu.1,covariant_comp _ _ hb.2 hu.2⟩

theorem normalized_combined_rows_norm (i : ℕ) (x : UpperHalfPlane) :
    ‖normalizedCombinedRows A P e hs l i x‖≤normalizedCombinedBound A P e hs l i := by
  have hu := normalizedRegularAmbientCountReconstruction_norm_le A (NeZero.pos N) P e x
  cases i with
  | zero =>
    apply (norm_mul_le_of_le (le_refl _) hu).trans
    rw [mul_one,newBaselineDetector,absolute_opNorm]
    exact stack_norm_le _ _ (newBaselineRowBound_nonneg N e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4))
      (newBaselineRows_norm N e hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4) x)
  | succ i =>
    apply (norm_mul_le_of_le (packet_sequence_norm N (NeZero.pos N) (sign e.1) hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) l i x) hu).trans_eq
    exact mul_one _

theorem normalized_combined_rows_source (i : ℕ) (x : Base) :
    normalizedCombinedRows A P e hs l i x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=
      normalizedCombinedRows A P e hs l i x := by
  have hu : normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x *
      AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=
      normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x :=
    normalized_right_terminal A (NeZero.pos N) P e x
  cases i <;> simp only [normalizedCombinedRows,mul_assoc,hu]

#print axioms normalized_combined_rows_regular
#print axioms normalized_combined_rows_norm
#print axioms normalized_combined_rows_source
end QuantitativeEulerEndpointPrepared
