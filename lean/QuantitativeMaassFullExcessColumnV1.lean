module

public import QuantitativeMaassFullOriginalExcessCountV1
public import QuantitativeMaassRectangularColumnTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

open Set MeasureTheory ContinuousLinearMap AsymptoticSectorSigns AsymptoticClassicalPetersson
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass

local instance (ε : ℝ) : NormedAddCommGroup (AsymptoticCylinderTerminal.Space ε) := inferInstance
local instance (ε : ℝ) : InnerProductSpace ℂ (AsymptoticCylinderTerminal.Space ε) := inferInstance
local instance (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) :
    NormedAddCommGroup (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) :
    InnerProductSpace ℂ (completedNewSignSpace N hN χ) := inferInstance

def fullTerminalColumnOutput {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) (e : Sector N) :=
  let P' := AsymptoticReconstructedCount.parameters A P
  (EulerHilbert.FullTerminal.terminalLeftInverse A hN P e).comp
    (AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint.comp
      (AsymptoticZeroExtension.isometry volume (AsymptoticCertificateOperators.highStrip P'.ε)
        (AsymptoticCertificateOperators.highStrip_measurable P'.ε)).toContinuousLinearMap)

/-- The exact error in the original full-terminal count is bounded by the
linear trace of its actual centered, weighted cylinder columns. -/
theorem fullTerminal_excess_column_bound {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε))
    (e : Sector N) {s : Set UpperHalfPlane} (hsObs : IsCompact s) (qs : Finset ℕ+) (d : ℕ)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ u,star (f u)=f u)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := (fullTerminalTranslationIsometry A hN.1 P e).toContinuousLinearMap
    let F := EulerHilbert.FullTerminal.commonResidualFilter A hN.1 P e hsObs qs d
    let K := completedNewSignFullTerminalEmbedding A hN.1 P (sectorCharacter N hN.1 e) e
    let Q := embeddingGramProjection
      (V := completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e))
      (H := AsymptoticCylinderTerminal.Space P'.ε) K
    hilbertSchmidtEnergy basis
      (((EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e).comp F).comp (1-Q))≤
      ‖fullTerminalColumnOutput A hN.1 P e‖^2*
        columnLinearTrace (volume.restrict (AsymptoticCertificateOperators.highStrip P'.ε))
          (cylinderCenteredCappedColumn f hc he R hR hs P'.ε (P'.s+3))
          (U.comp ((F*F-Q).comp U.adjoint)) := by
  intro P' U F K Q
  obtain ⟨a,ha,hl⟩ := completedNewSignFullTerminalEmbedding_lower A hN P
  have hK : ∀ x,a*‖x‖^2≤‖K x‖^2 :=
    hl _ e (sectorCharacter_norm N hN.1 e)
      (sectorCharacter_coherent N hN.1 e).1 (sectorCharacter_coherent N hN.1 e).2
  have hF : IsSelfAdjoint F :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (EulerHilbert.FullTerminal.commonResidualFilter_order A hN.1 P e hsObs qs d).1).isSelfAdjoint
  have hFK : ∀ x,F (K x)=K x :=
    completedNewSignFullTerminalEmbedding_filter A hN.1 P _ e
      (sectorCharacter_coherent N hN.1 e).1 (sectorCharacter_coherent N hN.1 e).2 hsObs qs d
  exact isometric_column_excess_bound
    (volume.restrict (AsymptoticCertificateOperators.highStrip P'.ε))
    (cylinderCenteredCappedColumn f hc he R hR hs P'.ε (P'.s+3))
    (cylinderCenteredCappedColumn_memLp f hc he hr R hR hs P'.ε (P'.s+3) P'.ε P'.epsilon_pos)
    basis (fullTerminalTranslationIsometry A hN.1 P e) K ha hK F hFK hF
    (fullTerminalColumnOutput A hN.1 P e)

/-- Under the actual cylinder isometry the full canonical projection is the
original weighted new/sign projection, with no change of target space. -/
theorem fullTerminal_full_projection_cylinder {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N] (e : Sector N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := (fullTerminalTranslationIsometry A hN P e).toContinuousLinearMap
    U.comp ((embeddingGramProjection
      (V := completedNewSignSpace N hN (sectorCharacter N hN e))
      (H := AsymptoticCylinderTerminal.Space P'.ε)
      (completedNewSignFullTerminalEmbedding A hN P (sectorCharacter N hN e) e)).comp U.adjoint)=
      embeddingGramProjection (V := completedNewSignSpace N hN (sectorCharacter N hN e))
        (H := Lp ℂ 2 (quotientMeasure 0))
        (completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega)
          (sectorCharacter N hN e)) := by
  intro P' U
  have heq : U.comp (completedNewSignFullTerminalEmbedding A hN P (sectorCharacter N hN e) e)=
      completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega)
        (sectorCharacter N hN e) := by
    apply ContinuousLinearMap.ext
    intro x
    exact fullTerminalTranslationIsometry_newSign A hN P _ e
      (sectorCharacter_coherent N hN e).1 (sectorCharacter_coherent N hN e).2 x
  rw [←output_isometry_gramProjection (fullTerminalTranslationIsometry A hN P e),heq]

#print axioms fullTerminal_excess_column_bound
#print axioms fullTerminal_full_projection_cylinder
end QuantitativeMaass
