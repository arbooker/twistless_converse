module

public import QuantitativeMaassFullTerminalEmbeddingV1
public import QuantitativeMaassCanonicalResidualV1
public import QuantitativeMaassFullResidualFilterV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticClassicalPetersson
open AsymptoticCongruenceStrip AsymptoticSectorSigns QuantitativeNewGap
open scoped Topology

namespace QuantitativeMaass

theorem completedNewSignFullTerminalEmbedding_residual {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (q : ℕ) (hq : 0<q) {s : Set ℍ} (hs : IsCompact s)
    (x : completedNewSignSpace N hN χ) :
    EulerHilbert.FullTerminal.residualRow A hN P e q hq hs
      (completedNewSignFullTerminalEmbedding A hN P χ e x)=0 := by
  let P' := AsymptoticReconstructedCount.parameters A P
  change AsymptoticTwistObservation.residual N q hN hq hs P'.epsilon_pos (P'.s+3) 0 (multiplier e q)
    (AsymptoticCylinderLift.lift (EulerHilbert.normalized A hN P e
      (completedNewSignFullTerminalEmbedding A hN P χ e x)))=0
  rw [completedNewSignFullTerminalEmbedding_normalized A hN P χ e hχW hχS]
  exact completedNewSign_weighted_residual N hN χ e hχW hχS P'.epsilon_pos
    (show 1≤P'.s+3 by omega) q hq hs x.val x.property

/-- Every finite positive residual filter fixes the canonical target exactly. -/
theorem completedNewSignFullTerminalEmbedding_filter {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    {s : Set ℍ} (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ)
    (x : completedNewSignSpace N hN χ) :
    EulerHilbert.FullTerminal.commonResidualFilter A hN P e hs qs d
      (completedNewSignFullTerminalEmbedding A hN P χ e x)=
        completedNewSignFullTerminalEmbedding A hN P χ e x := by
  apply gram_filter_fixes qs
    (fun q : ℕ+ => EulerHilbert.FullTerminal.residualRow A hN P e q.val q.property hs)
  intro q _
  exact completedNewSignFullTerminalEmbedding_residual A hN P χ e hχW hχS q.val q.property hs x

#print axioms completedNewSignFullTerminalEmbedding_residual
#print axioms completedNewSignFullTerminalEmbedding_filter

end QuantitativeMaass
