module

public import QuantitativeEulerEndpointNormalizedSourceReturnV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticRegularCompactBranch QuantitativeSpectralDeflationChain

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem chain_prepend (F : ClosedSubmodule ℂ H) (B₀ : H →L[ℂ] H)
    (B : ℕ → H →L[ℂ] H) (c : ℝ) (n : ℕ) :
    chain F (fun i => match i with | 0 => B₀ | j+1 => B j) c (n+1)=chain (step F B₀ c) B c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (chain F _ c (n+1)) (B n) c=step (chain (step F B₀ c) B c n) (B n) c
    exact congrArg (fun V => step V (B n) c) ih
end Hilbert

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))

/-- A single packet includes the baseline observation followed by the original-prime rows.
It depends only on the fixed observations and normalized reconstruction, not on its source. -/
def normalizedCombinedRows : ℕ → UpperHalfPlane → Space →L[ℂ] Space
  | 0, x => newBaselineDetector N e hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) x *
      normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x
  | j+1, x => packetSequence N (NeZero.pos N) (sign e.1) hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) l j x *
      normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x

theorem normalized_combined_chain (F : UpperHalfPlane → ClosedSubmodule ℂ Space)
    (a : ℝ) (x : UpperHalfPlane) :
    chain (F x) (fun i => normalizedCombinedRows A P e hs l i x) (Real.sqrt a) (l.length+1)=
      normalizedSourcePacket A P e F hs a (Real.sqrt a) l x :=
  by
    let B₀ := newBaselineDetector N e hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) x *
      normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x
    let B := fun i => packetSequence N (NeZero.pos N) (sign e.1) hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) l i x *
      normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x
    have he : (fun i => normalizedCombinedRows A P e hs l i x)=
        (fun i => match i with | 0 => B₀ | j+1 => B j) := by
      funext i
      cases i <;> rfl
    rw [he]
    exact chain_prepend (F x) B₀ B (Real.sqrt a) l.length

#print axioms chain_prepend
#print axioms normalized_combined_chain
end QuantitativeEulerEndpointPrepared
