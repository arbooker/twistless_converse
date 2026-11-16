module

public import QuantitativeMaassParityTerminalEmbeddingV1
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
def terminalTranslationIsometry {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) (e : Sector N) :
    terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε →ₗᵢ[ℂ]
      Lp ℂ 2 (quotientMeasure 0) where
  toLinearMap := translationToProductCylinder.symm.toLinearMap.comp
    (EulerHilbert.Nonzero.normalized A hN P e).toLinearMap
  norm_map' x := by
    change ‖translationToProductCylinder.symm (EulerHilbert.Nonzero.normalized A hN P e x)‖=‖x‖
    rw [translationToProductCylinder.symm.norm_map,EulerHilbert.Nonzero.normalized_norm]

/-- This is the original weighted embedding, not a newly chosen realization. -/
theorem terminalTranslationIsometry_newSign {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N)
    (hW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (x : completedNewSignSpace N hN χ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    terminalTranslationIsometry A hN P e (completedNewSignTerminalEmbedding A hN P χ e x)=
      completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ x := by
  change translationToProductCylinder.symm
    (EulerHilbert.Nonzero.normalized A hN P e (completedNewSignTerminalEmbedding A hN P χ e x))=_
  rw [completedNewSignTerminalEmbedding_normalized A hN P χ e hW hS]
  exact translationToProductCylinder.symm_apply_apply _

theorem terminalTranslationIsometry_newSignParity {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N) (η : ℝ)
    (hW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (x : completedNewSignParitySpace N hN χ η) :
    let P' := AsymptoticReconstructedCount.parameters A P
    terminalTranslationIsometry A hN P e (completedNewSignParityTerminalEmbedding A hN P χ e η x)=
      completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ
        (completedNewSignParityInclusion N hN χ η x) :=
  terminalTranslationIsometry_newSign A hN P χ e hW hS _

/-- An actual isometric change of output coordinates preserves the Gram. -/
theorem output_isometry_gram {V E F : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : E →ₗᵢ[ℂ] F) (R : V →L[ℂ] E) :
    (U.toContinuousLinearMap.comp R).adjoint.comp (U.toContinuousLinearMap.comp R)=
      R.adjoint.comp R := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap,U.inner_map_map]

/-- The same coordinate change intertwines every finite Newton reconstruction. -/
theorem output_isometry_newton {V E F : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : E →ₗᵢ[ℂ] F) (R : V →L[ℂ] E) (n : ℕ) :
    polynomialNormalizedReconstruction (U.toContinuousLinearMap.comp R) n=
      U.toContinuousLinearMap.comp (polynomialNormalizedReconstruction R n) := by
  unfold polynomialNormalizedReconstruction
  rw [output_isometry_gram U R]
  rfl

/-- Gram target projections transform by the same actual output isometry. -/
theorem output_isometry_gramProjection {V E F : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : E →ₗᵢ[ℂ] F) (R : V →L[ℂ] E) :
    embeddingGramProjection (U.toContinuousLinearMap.comp R)=
      U.toContinuousLinearMap.comp ((embeddingGramProjection R).comp U.toContinuousLinearMap.adjoint) := by
  unfold embeddingGramProjection
  rw [output_isometry_gram U R,ContinuousLinearMap.adjoint_comp]
  rfl

def completedNewSignParityWeightedEmbedding (N : ℕ) [NeZero N] (hN : 0<N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ) (η : ℝ) :
    completedNewSignParitySpace N hN χ η →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (completedNewSignWeightedEmbedding N hN hδ hν χ).comp
    (completedNewSignParityInclusion N hN χ η).toContinuousLinearMap

/-- Exact identification of the original parity target in cylinder coordinates. -/
theorem terminalTranslationIsometry_parity_projection {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N) (η : ℝ)
    (hW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := (terminalTranslationIsometry A hN P e).toContinuousLinearMap
    U.comp ((embeddingGramProjection (V := completedNewSignParitySpace N hN χ η)
      (H := terminalNonzeroModes P'.ε) (completedNewSignParityTerminalEmbedding A hN P χ e η)).comp U.adjoint)=
      embeddingGramProjection (V := completedNewSignParitySpace N hN χ η)
        (H := Lp ℂ 2 (quotientMeasure 0)) (completedNewSignParityWeightedEmbedding N hN P'.epsilon_pos
        (show 1≤P'.s+3 by omega) χ η) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have heq : (terminalTranslationIsometry A hN P e).toContinuousLinearMap.comp
      (completedNewSignParityTerminalEmbedding A hN P χ e η)=
      completedNewSignParityWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ η := by
    apply ContinuousLinearMap.ext
    intro x
    exact terminalTranslationIsometry_newSignParity A hN P χ e η hW hS x
  have hp := output_isometry_gramProjection
    (V := completedNewSignParitySpace N hN χ η)
    (E := terminalNonzeroModes P'.ε) (F := Lp ℂ 2 (quotientMeasure 0))
    (terminalTranslationIsometry A hN P e)
    (completedNewSignParityTerminalEmbedding A hN P χ e η)
  exact hp.symm.trans (congrArg
    (embeddingGramProjection (V := completedNewSignParitySpace N hN χ η)
      (H := Lp ℂ 2 (quotientMeasure 0))) heq)

#print axioms terminalTranslationIsometry_newSign
#print axioms terminalTranslationIsometry_newSignParity
#print axioms output_isometry_gram
#print axioms output_isometry_newton
#print axioms output_isometry_gramProjection
#print axioms terminalTranslationIsometry_parity_projection
end QuantitativeMaass
