module

public import QuantitativeMaassWeightedParityOrthogonalV1
public import QuantitativeMaassTerminalTranslationIsometryV1
public import QuantitativeMaassNonzeroWindowCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNewGap

namespace QuantitativeMaass

theorem weightedQuotientEmbedding_parity (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (η : ℝ) (hη : η^2=1)
    (x : AutomorphicSpace N) (hx : x∈completedParitySpace N η) :
    reflectionIsometry 0 (cylinderAutomorphic (weightedQuotientEmbedding N hε hv x))=
      (η:ℂ) • cylinderAutomorphic (weightedQuotientEmbedding N hε hv x) := by
  have hr := parityProjection_eigen N η hη x
  rw [(mem_completedParitySpace N η x).mp hx] at hr
  rw [weightedQuotientEmbedding_reflection,hr,map_smul,map_smul]

/-- The two actual canonical parity ranges are orthogonal also in the
weighted cylinder metric, although that metric is not the quotient metric. -/
theorem weightedQuotientEmbedding_opposite_inner_zero (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (η : ℝ) (hη : η^2=1)
    (x y : AutomorphicSpace N) (hx : x∈completedParitySpace N η)
    (hy : y∈completedParitySpace N (-η)) :
    inner ℂ (weightedQuotientEmbedding N hε hv x) (weightedQuotientEmbedding N hε hv y)=0 := by
  have hy' := weightedQuotientEmbedding_parity N hε hv (-η) (by simpa only [neg_sq] using hη) y hy
  simp only [Complex.ofReal_neg] at hy'
  simpa only [cylinderAutomorphic.inner_map_map] using
    reflection_opposite_inner_zero 0 η hη _ _
      (weightedQuotientEmbedding_parity N hε hv η hη x hx) hy'

theorem terminalTranslationIsometry_original {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) (e : Sector N)
    (r : ℝ) (σ : ℕ) {b : ℕ→ℂ} (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (g : terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)
    (hg : EulerHilbert.Nonzero.physicalIsometry A hN P e g=
      principalEulerWeightedLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb) :
    terminalTranslationIsometry A hN P e g=
      principalEulerCylinderLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb := by
  apply cylinderZeroExtension.injective
  change cylinderZeroExtension (productCylinderToTranslation (EulerHilbert.Nonzero.normalized A hN P e g))=_
  rw [productCylinderToTranslation_lift,principalEulerCylinderLp_physical]
  exact hg

theorem completedParityTerminal_opposite_inner_zero {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (e : Sector N) (η : ℝ) (hη : η^2=1)
    (hW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hS : ∀ q : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN q)= -delta e q.val)
    (x : completedNewSignParitySpace N hN χ η)
    (y : completedNewSignParitySpace N hN χ (-η)) :
    inner ℂ (completedNewSignParityTerminalEmbedding A hN P χ e η x)
      (completedNewSignParityTerminalEmbedding A hN P χ e (-η) y)=0 := by
  rw [←(terminalTranslationIsometry A hN P e).inner_map_map,
    terminalTranslationIsometry_newSignParity A hN P χ e η hW hS,
    terminalTranslationIsometry_newSignParity A hN P χ e (-η) hW hS]
  exact weightedQuotientEmbedding_opposite_inner_zero N
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega)
    η hη x.val y.val x.property.2 y.property.2

/-- Every actual window datum is orthogonal to the opposite canonical
new/sign/parity target in its original terminal norm. -/
theorem windowDatum_opposite_target_inner_zero {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (σ : ℕ) (t ε : ℝ) (p : QuantitativeConcreteGoals.maassWindow N σ t ε)
    (e : Sector N) (hp : EulerHilbert.Nonzero.windowSector A hN P σ t ε p=e)
    (χ : admissibleGeneratorIndex N hN→ℂ)
    (hW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hS : ∀ q : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN q)= -delta e q.val)
    (x : completedNewSignParitySpace N hN χ (-((-1:ℝ)^σ))) :
    inner ℂ (EulerHilbert.Nonzero.windowDatum A hN P σ t ε p)
      (completedNewSignParityTerminalEmbedding A hN P χ e (-((-1:ℝ)^σ)) x)=0 := by
  have hg := EulerHilbert.Nonzero.windowDatum_realizes A hN P σ t ε p
  rw [hp] at hg
  rw [←(terminalTranslationIsometry A hN P e).inner_map_map,
    terminalTranslationIsometry_original A hN P e p.val.1 σ p.property.2.2 _ hg,
    terminalTranslationIsometry_newSignParity A hN P χ e _ hW hS]
  exact principalEulerCylinder_orthogonal_opposite hN A
    (AsymptoticReconstructedCount.parameters A P) p.val.1 σ p.property.2.2 x.val x.property.2

#print axioms weightedQuotientEmbedding_parity
#print axioms weightedQuotientEmbedding_opposite_inner_zero
#print axioms terminalTranslationIsometry_original
#print axioms completedParityTerminal_opposite_inner_zero
#print axioms windowDatum_opposite_target_inner_zero

end QuantitativeMaass
