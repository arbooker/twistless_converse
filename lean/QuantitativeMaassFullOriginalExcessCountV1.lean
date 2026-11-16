module

public import QuantitativeMaassFullOriginalOrthogonalCountV1
public import QuantitativeMaassFullParityDecompositionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticSectorSigns QuantitativeNewGap
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass

/-- Original fixed-parity solutions are counted by the corresponding canonical
packet plus the full new/sign excess of the common twist filter. The opposite
parity is removed exactly, so no parity filter or parity approximation enters
the remaining physical-to-regular trace comparison. -/
theorem originalWindow_fullTerminal_sector_count_common_full_excess {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (η : ℝ) (hηsq : η^2=1) (e : Sector N)
    {ι κ : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε))
    (c : HilbertBasis κ ℂ (completedNewSignParitySpace N hN.1 (sectorCharacter N hN.1 e) η)) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Set UpperHalfPlane) (hsObs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) (σ : ℕ) (_hη : η=(-1:ℝ)^σ) (t ε : ℝ)
      (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
      (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
      (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R),
      (∀ r∈Icc t (t+ε),1≤(cosinePacket f r).re) →
      let V := {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
        EulerHilbert.FullTerminal.windowSector A hN.1 P σ t ε p=e}
      let B := (EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e).comp
        (EulerHilbert.FullTerminal.commonResidualFilter A hN.1 P e hsObs qs d)
      Finite V ∧ (Nat.card V:ℝ)≤
        hilbertSchmidtEnergy c (completedNewSignParityTimePacket N hN.1 (sectorCharacter N hN.1 e) η f hc he hr R hR hs)+
        C*hilbertSchmidtEnergy basis (B.comp
          (1-embeddingGramProjection
            (V := completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e))
            (H := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
            (completedNewSignFullTerminalEmbedding A hN.1 P (sectorCharacter N hN.1 e) e))) := by
  have hh := originalWindow_fullTerminal_sector_count_orthogonal_excess A hN P η hηsq
    (sectorCharacter N hN.1 e) e (sectorCharacter_norm N hN.1 e)
    (sectorCharacter_coherent N hN.1 e).1 (sectorCharacter_coherent N hN.1 e).2 basis c
  have hp := completedSectorFullTerminal_parity_projection_sum A hN P e η hηsq
  simpa only [sub_sub,←hp] using hh

#print axioms originalWindow_fullTerminal_sector_count_common_full_excess
end QuantitativeMaass
