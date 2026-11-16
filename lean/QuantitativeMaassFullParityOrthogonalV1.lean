module

public import QuantitativeMaassTerminalParityOrthogonalV1
public import QuantitativeMaassFullTerminalTranslationV1
public import QuantitativeMaassFullWindowDataV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNewGap

namespace QuantitativeMaass

theorem fullTerminalTranslationIsometry_original {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) (e : Sector N)
    (r : ℝ) (σ : ℕ) {b : ℕ→ℂ} (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (hg : EulerHilbert.FullTerminal.physicalIsometry A hN P e g=
      principalEulerWeightedLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb) :
    fullTerminalTranslationIsometry A hN P e g=
      principalEulerCylinderLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb := by
  apply cylinderZeroExtension.injective
  change cylinderZeroExtension (productCylinderToTranslation (EulerHilbert.normalized A hN P e g))=_
  rw [productCylinderToTranslation_lift,principalEulerCylinderLp_physical]
  exact hg

theorem completedParityFullTerminal_opposite_inner_zero {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (e : Sector N) (η : ℝ) (hη : η^2=1)
    (hW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hS : ∀ q : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN q)= -delta e q.val)
    (x : completedNewSignParitySpace N hN χ η)
    (y : completedNewSignParitySpace N hN χ (-η)) :
    inner ℂ (completedNewSignParityFullTerminalEmbedding A hN P χ e η x)
      (completedNewSignParityFullTerminalEmbedding A hN P χ e (-η) y)=0 := by
  rw [←(fullTerminalTranslationIsometry A hN P e).inner_map_map,
    fullTerminalTranslationIsometry_newSignParity A hN P χ e η hW hS,
    fullTerminalTranslationIsometry_newSignParity A hN P χ e (-η) hW hS]
  exact weightedQuotientEmbedding_opposite_inner_zero N
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega)
    η hη x.val y.val x.property.2 y.property.2

/-- Every actual window datum is orthogonal to the opposite canonical
new/sign/parity target in its original terminal norm. -/
theorem fullWindowDatum_opposite_target_inner_zero {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (σ : ℕ) (t ε : ℝ) (p : QuantitativeConcreteGoals.maassWindow N σ t ε)
    (e : Sector N) (hp : EulerHilbert.FullTerminal.windowSector A hN P σ t ε p=e)
    (χ : admissibleGeneratorIndex N hN→ℂ)
    (hW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hS : ∀ q : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN q)= -delta e q.val)
    (x : completedNewSignParitySpace N hN χ (-((-1:ℝ)^σ))) :
    inner ℂ (EulerHilbert.FullTerminal.windowDatum A hN P σ t ε p)
      (completedNewSignParityFullTerminalEmbedding A hN P χ e (-((-1:ℝ)^σ)) x)=0 := by
  have hg := EulerHilbert.FullTerminal.windowDatum_realizes A hN P σ t ε p
  rw [hp] at hg
  rw [←(fullTerminalTranslationIsometry A hN P e).inner_map_map,
    fullTerminalTranslationIsometry_original A hN P e p.val.1 σ p.property.2.2 _ hg,
    fullTerminalTranslationIsometry_newSignParity A hN P χ e _ hW hS]
  exact principalEulerCylinder_orthogonal_opposite hN A
    (AsymptoticReconstructedCount.parameters A P) p.val.1 σ p.property.2.2 x.val x.property.2

#print axioms fullTerminalTranslationIsometry_original
#print axioms completedParityFullTerminal_opposite_inner_zero
#print axioms fullWindowDatum_opposite_target_inner_zero

end QuantitativeMaass
