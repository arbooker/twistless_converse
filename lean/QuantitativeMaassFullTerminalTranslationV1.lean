module

public import QuantitativeMaassFullParityEmbeddingV1
public import QuantitativeMaassNormalizedNewSignEmbeddingV1
public import QuantitativeHolomorphicNewtonTransportV1
public import QuantitativeMaassWeightedTargetProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNewGap
open QuantitativeHolomorphic
namespace QuantitativeMaass

/-- The actual normalized terminal reconstruction, in the quotient-cylinder
coordinates used by the weighted band estimates. -/
def fullTerminalTranslationIsometry {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) (e : Sector N) :
    AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →ₗᵢ[ℂ]
      Lp ℂ 2 (quotientMeasure 0) where
  toLinearMap := translationToProductCylinder.symm.toLinearMap.comp
    (EulerHilbert.normalized A hN P e).toLinearMap
  norm_map' x := by
    change ‖translationToProductCylinder.symm (EulerHilbert.normalized A hN P e x)‖=‖x‖
    rw [translationToProductCylinder.symm.norm_map,EulerHilbert.normalized_norm]

/-- This is the original weighted embedding, not a newly chosen realization. -/
theorem fullTerminalTranslationIsometry_newSign {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N)
    (hW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (x : completedNewSignSpace N hN χ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    fullTerminalTranslationIsometry A hN P e (completedNewSignFullTerminalEmbedding A hN P χ e x)=
      completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ x := by
  change translationToProductCylinder.symm
    (EulerHilbert.normalized A hN P e (completedNewSignFullTerminalEmbedding A hN P χ e x))=_
  rw [completedNewSignFullTerminalEmbedding_normalized A hN P χ e hW hS]
  exact translationToProductCylinder.symm_apply_apply _

theorem fullTerminalTranslationIsometry_newSignParity {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N) (η : ℝ)
    (hW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (x : completedNewSignParitySpace N hN χ η) :
    let P' := AsymptoticReconstructedCount.parameters A P
    fullTerminalTranslationIsometry A hN P e (completedNewSignParityFullTerminalEmbedding A hN P χ e η x)=
      completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ
        (completedNewSignParityInclusion N hN χ η x) :=
  fullTerminalTranslationIsometry_newSign A hN P χ e hW hS _

#print axioms fullTerminalTranslationIsometry_newSign
#print axioms fullTerminalTranslationIsometry_newSignParity
end QuantitativeMaass
