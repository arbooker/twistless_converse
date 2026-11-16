module

public import QuantitativeMaassRawCanonicalSourceV1
public import QuantitativeMaassRawOriginalWindowV1
public import QuantitativeMaassFullParityOrthogonalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNewGap
namespace QuantitativeMaass

theorem raw_terminalSourceProjection_canonical {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N (NeZero.pos N)→ℂ) (e : Sector N)
    (hW : χ (frickeGeneratorIndex N (NeZero.pos N))=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N (NeZero.pos N) p)= -delta e p.val)
    (x : completedNewSignSpace N (NeZero.pos N) χ) :
    RawCommonReconstruction.terminalSourceProjection A P e
      (completedNewSignFullTerminalEmbedding A (NeZero.pos N) P χ e x)=
      completedNewSignFullTerminalEmbedding A (NeZero.pos N) P χ e x :=
  RawCommonReconstruction.terminalSourceProjection_fixes A P e _
    (RawCommonReconstruction.canonical_source_mem A P χ e hW hS x)

theorem raw_terminalSourceProjection_parity {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N (NeZero.pos N)→ℂ) (e : Sector N) (η : ℝ)
    (hW : χ (frickeGeneratorIndex N (NeZero.pos N))=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N (NeZero.pos N) p)= -delta e p.val)
    (x : completedNewSignParitySpace N (NeZero.pos N) χ η) :
    RawCommonReconstruction.terminalSourceProjection A P e
      (completedNewSignParityFullTerminalEmbedding A (NeZero.pos N) P χ e η x)=
      completedNewSignParityFullTerminalEmbedding A (NeZero.pos N) P χ e η x :=
  raw_terminalSourceProjection_canonical A P χ e hW hS (completedNewSignParityInclusion N (NeZero.pos N) χ η x)

theorem rawWindowDatum_opposite_target_inner_zero {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (σ : ℕ) (t ε : ℝ) (p : QuantitativeConcreteGoals.maassWindow N σ t ε)
    (e : Sector N) (hp : RawOriginalWindow.windowSector A P σ t ε p=e)
    (χ : admissibleGeneratorIndex N (NeZero.pos N)→ℂ)
    (hW : χ (frickeGeneratorIndex N (NeZero.pos N))=sign e.1)
    (hS : ∀ q : SimplePrime N,χ (simpleAtkinGeneratorIndex N (NeZero.pos N) q)= -delta e q.val)
    (x : completedNewSignParitySpace N (NeZero.pos N) χ (-((-1:ℝ)^σ))) :
    inner ℂ (RawOriginalWindow.windowDatum A P σ t ε p)
      (completedNewSignParityFullTerminalEmbedding A (NeZero.pos N) P χ e (-((-1:ℝ)^σ)) x)=0 := by
  have hg := RawOriginalWindow.windowDatum_realizes A P σ t ε p
  rw [hp] at hg
  rw [←(fullTerminalTranslationIsometry A (NeZero.pos N) P e).inner_map_map,
    fullTerminalTranslationIsometry_original A (NeZero.pos N) P e p.val.1 σ p.property.2.2 _ hg,
    fullTerminalTranslationIsometry_newSignParity A (NeZero.pos N) P χ e _ hW hS]
  exact principalEulerCylinder_orthogonal_opposite (NeZero.pos N) A
    (AsymptoticReconstructedCount.parameters A P) p.val.1 σ p.property.2.2 x.val x.property.2

#print axioms raw_terminalSourceProjection_canonical
#print axioms raw_terminalSourceProjection_parity
#print axioms rawWindowDatum_opposite_target_inner_zero
end QuantitativeMaass
