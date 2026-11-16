module

public import QuantitativeMaassCompletedNewReconstructionV1
public import QuantitativeMaassFullTerminalLeftInverseV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNewGap

namespace QuantitativeMaass

theorem full_normalized_terminalLeftInverse_raw {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) (e : Sector N)
    (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) :
    EulerHilbert.normalized A hN P e
      (EulerHilbert.FullTerminal.terminalLeftInverse A hN P e
        (EulerHilbert.reconstruction A hN P e g))=
      EulerHilbert.reconstruction A hN P e g := by
  let R := EulerHilbert.reconstruction A hN P e
  change QuantitativeHolomorphic.normalizedReconstruction R
    ((R.adjoint.comp R).comp (QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R))
      (EulerHilbert.FullTerminal.terminalRestriction _ (R g)))=R g
  rw [EulerHilbert.FullTerminal.terminalRestriction_reconstruction]
  apply QuantitativeHolomorphic.normalizedReconstruction_reconstruct R (by norm_num : (0:ℝ)<1)
  intro v
  simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg v)
    (EulerHilbert.reconstruction_norm_ge A hN P e v) 2

/-- The actual canonical new/sign space embedded into the normalized
terminal Hilbert space used by the original-solution count. -/
def completedNewSignFullTerminalEmbedding {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N) :
    completedNewSignSpace N hN χ →L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε :=
  let P' := AsymptoticReconstructedCount.parameters A P
  (EulerHilbert.FullTerminal.terminalLeftInverse A hN P e).comp
    (translationToProductCylinder.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ))

theorem completedNewSignFullTerminalEmbedding_normalized {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (x : completedNewSignSpace N hN χ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    EulerHilbert.normalized A hN P e (completedNewSignFullTerminalEmbedding A hN P χ e x)=
      translationToProductCylinder
        (completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ x) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let g := terminalNonzeroInclusion P'.ε (cuspidalTerminalData N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) ⟨x.val,x.property.1⟩)
  have he := completedNewSign_nonzero_reconstruction A hN P χ e hχW hχS x
  change EulerHilbert.reconstruction A hN P e g=_ at he
  change EulerHilbert.normalized A hN P e
    (EulerHilbert.FullTerminal.terminalLeftInverse A hN P e
      (translationToProductCylinder
        (completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ x))) = _
  rw [←he,full_normalized_terminalLeftInverse_raw]

theorem completedNewSignFullTerminalEmbedding_norm {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (x : completedNewSignSpace N hN χ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ‖completedNewSignFullTerminalEmbedding A hN P χ e x‖=
      ‖completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ x‖ := by
  rw [←EulerHilbert.normalized_norm A hN P e,
    completedNewSignFullTerminalEmbedding_normalized A hN P χ e hχW hχS]
  exact translationToProductCylinder.norm_map _

#print axioms full_normalized_terminalLeftInverse_raw
#print axioms completedNewSignFullTerminalEmbedding_normalized
#print axioms completedNewSignFullTerminalEmbedding_norm

end QuantitativeMaass
